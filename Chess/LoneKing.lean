import Chess.KingPawnTheorems
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# Lone king versus arbitrary material: an engineered mating line

One player has only a king; the other has a king and any material. This
module decides whether checkmate is reachable by cooperative play, without
searching the game tree: it *engineers* a legal sequence of moves that
steers the position into an ending whose mating line is already known.

The reduction proceeds in phases, replanned after every ply:

* **Sacrifices.** Every piece of the strong side that is not needed for
  the final mate is brought next to the lone king on an unprotected
  square, and the lone king captures it.
* **Promotions.** Pawns are pushed (the lone king steps out of the file)
  and promoted, usually to a queen, which is then sacrificed in turn.
* **Known endings.** Once only a queen, a rook, or a pawn is left, the
  proven lines of `Chess.KingQueen`, `Chess.KingRook`, and `Chess.KingPawn`
  finish the job.
* **Two minor pieces.** Material that cannot reduce to a queen or a rook
  (two bishops of opposite colors, bishop and knight, two knights) is
  mated in a corner by a fixed picture: the strong king two files from
  the corner, one piece covering the square beside the corner, and the
  other piece giving the final check.

The material that cannot mate (a lone minor piece, or bishops all on one
square color) is detected up front. `Position.loneKingCheckmateReachable`
answers `true` only when the engineered line is checked to be legal and
to end in checkmate, or when the position is one of the proven
three-piece endings and its state is not dead; it is therefore sound for
every valid position (`Chess.LoneKingTheorems`). A failed line is not by
itself a proof of deadness, so the negative answer is engineered too:
`Position.loneKingDead` recognizes a position as dead when it is a
rejected three-piece ending, a stalemate, or when every legal move leads
to such a position within two plies. `Position.loneKingDecided` records
that one of the two procedures succeeded. For at most three pieces the
procedures always succeed.

A position with more material that neither procedure settles is not left
undecided: `Position.loneKingVerdict` falls back to an exhaustive
exploration of the positions reachable from it (`LoneKing.explore`),
which stops as soon as it meets a checkmate or a position whose
engineered line succeeds, and does not expand a position recognized as
dead — a rejected three-piece ending, or the strong side left with a
king and bishops of one square color (`Chess.LoneKingMaterial`). The
exploration terminates because there are finitely many positions, and
the verdict is proved correct for every valid position in which one
player has only a king (`Position.HasLoneKing`), which gives
`Position.loneKingDecidable : Decidable (CheckmateReachable p)` from
exactly those two hypotheses. The engineered procedures answer first, so
the exhaustive fallback runs only on the positions they leave open.
-/

namespace Chess

namespace Board

/-- The board read off a 64-entry array indexed by `KQState.idx`. Kept
out of line so that a call `ofArray arr` is a closure over the finished
array rather than a recomputation of it on every lookup. -/
@[noinline] def ofArray (arr : Array (Option Piece)) : Board :=
  fun s => arr.getD (KQState.idx s) none

/-- The 64 entries of a board, in `KQState.idx` order. -/
def tabulate (b : Board) : Array (Option Piece) :=
  (KQState.allSquares.map b).toArray

/-- The same board tabulated into an array, so that a lookup costs one
array access even after a long chain of `relocate`s. Propositionally
equal to the original (`normalize_eq`). Runtime code should call
`ofArray (tabulate b)` from a context that is not itself of function type
(as `Position.normalize` does): the compiler eta-expands a definition of
type `Board`, which would rebuild the array at every lookup. -/
def normalize (b : Board) : Board := ofArray (tabulate b)

theorem allSquares_getElem?_idx (s : Square) :
    KQState.allSquares[KQState.idx s]? = some s := by
  revert s
  native_decide

theorem allSquares_map_getD (f : Square → Option Piece) (s : Square) :
    (KQState.allSquares.map f).toArray.getD (KQState.idx s) none = f s := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    allSquares_getElem?_idx]
  rfl

theorem normalize_eq (b : Board) : b.normalize = b := by
  funext s
  exact allSquares_map_getD b s

end Board

namespace Position

/-- The position with its board tabulated (`Board.normalize`, spelled out
so that the array is built once). -/
def normalize (p : Position) : Position :=
  { p with board := Board.ofArray (Board.tabulate p.board) }

theorem normalize_eq (p : Position) : p.normalize = p := by
  rcases p with ⟨b, tm, c, e⟩
  have h : Board.ofArray (Board.tabulate b) = b := Board.normalize_eq b
  simp [normalize, h]

/-- `pathLegal`, tabulating the board after every move. -/
def pathLegalN (p : Position) : List Move → Bool
  | [] => true
  | m :: ms => p.isLegalMove m && pathLegalN (p.play m).normalize ms

theorem pathLegalN_eq (p : Position) (ms : List Move) :
    pathLegalN p ms = pathLegal p ms := by
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => simp [pathLegalN, pathLegal, normalize_eq, ih]

/-- `playSeq`, tabulating the board after every move. -/
def playSeqN (p : Position) : List Move → Position
  | [] => p
  | m :: ms => playSeqN (p.play m).normalize ms

theorem playSeqN_eq (p : Position) (ms : List Move) :
    playSeqN p ms = playSeq p ms := by
  induction ms generalizing p with
  | nil => rfl
  | cons m ms ih => simp [playSeqN, playSeq, normalize_eq, ih]

/-- The color that owns no piece besides its king, if there is one. When
both players have bare kings, Black is reported. -/
def loneKingSide? (p : Position) : Option Color :=
  let bare (c : Color) : Bool :=
    KQState.allSquares.all fun s =>
      match p.board s with
      | some q => q.color != c || q.kind == .king
      | none => true
  if bare .black then some .black
  else if bare .white then some .white
  else none

/-- Every piece of color `c` on the board is a king: the player `c` has
only a king (possibly none, on an invalid board). -/
def LoneFor (c : Color) (p : Position) : Prop :=
  ∀ s q, p.board s = some q → q.color = c → q.kind = .king

instance {c : Color} {p : Position} : Decidable (LoneFor c p) := by
  unfold LoneFor
  infer_instance

/-- One of the players has only a king on the board. -/
def HasLoneKing (p : Position) : Prop :=
  ∃ c, LoneFor c p

instance {p : Position} : Decidable (HasLoneKing p) := by
  unfold HasLoneKing
  infer_instance

/-- The player with only a king: Black when Black has only a king,
otherwise White. Meaningful under `HasLoneKing` (`loneFor_loneColor`). -/
def loneColor (p : Position) : Color :=
  if LoneFor .black p then .black else .white

/-- Every piece of color `s` other than a king is a bishop standing on a
square of color `χ`. Together with a bare opponent this material cannot
checkmate (`Chess.LoneKingMaterial`). -/
def OnlyBishopsOn (s χ : Color) (p : Position) : Prop :=
  ∀ sq q, p.board sq = some q → q.color = s → q.kind ≠ .king →
    q.kind = .bishop ∧ sq.color = χ

instance {s χ : Color} {p : Position} : Decidable (OnlyBishopsOn s χ p) := by
  unfold OnlyBishopsOn
  infer_instance

end Position

namespace LoneKing

open KQState (allSquares idx kingNeighbors shift)

/-- The square with the given file and rank indices. -/
def sq (f r : Fin 8) : Square := ⟨f, r⟩

/-- Square of the king of color `c`, if present. -/
def findKing (b : Board) (c : Color) : Option Square :=
  allSquares.find? fun s => b s == some { color := c, kind := .king }

/-- Squares and kinds of the non-king pieces of color `c`. -/
def piecesOf (b : Board) (c : Color) : List (Square × PieceKind) :=
  allSquares.filterMap fun s =>
    match b s with
    | some q => if q.color == c && q.kind != .king then some (s, q.kind) else none
    | none => none

/-- Working context: the position (with a tabulated board), the strong
and lone colors, the two king squares, and the strong side's pieces. -/
structure Ctx where
  /-- The position under consideration. -/
  p : Position
  /-- The side with material. -/
  strong : Color
  /-- The side with a bare king. -/
  lone : Color
  /-- Square of the strong king. -/
  wk : Square
  /-- Square of the lone king. -/
  bk : Square
  /-- Non-king pieces of the strong side. -/
  pieces : List (Square × PieceKind)

/-- The context of a position in which one side has a bare king. -/
def Ctx.of? (p : Position) : Option Ctx := do
  let lone ← p.loneKingSide?
  let strong := lone.other
  let wk ← findKing p.board strong
  let bk ← findKing p.board lone
  pure ⟨p, strong, lone, wk, bk, piecesOf p.board strong⟩

/-- Ranks advanced by a pawn of color `c` standing on `s`. -/
def pawnAdvance (c : Color) (s : Square) : Nat :=
  match c with
  | .white => s.rank.val
  | .black => 7 - s.rank.val

/-- The pawn of color `c` closest to promotion. -/
def mostAdvancedPawn (c : Color) (pieces : List (Square × PieceKind)) : Option Square :=
  pieces.foldl
    (fun acc (s, k) =>
      if k != .pawn then acc
      else
        match acc with
        | none => some s
        | some t => if pawnAdvance c s > pawnAdvance c t then some s else acc)
    none

/-- The squares in front of a pawn of color `c` on `s`, up to and
including its promotion square. -/
def pawnPath (c : Color) (s : Square) : List Square :=
  let rec go (t : Square) : Nat → List Square
    | 0 => []
    | n + 1 =>
      match shift t 0 (pawnPushDelta c) with
      | some u => u :: go u n
      | none => []
  go s 7

/-- The squares of the strong pieces that the reduction must preserve: a
queen; else a rook; else the most advanced pawn; else a pair of minor
pieces that can mate (bishops of opposite colors, a bishop and a knight,
or two knights). `none` when the material cannot mate. -/
def keeper (c : Color) (pieces : List (Square × PieceKind)) : Option (List Square) :=
  match pieces.find? (·.2 == .queen) with
  | some (s, _) => some [s]
  | none =>
  match pieces.find? (·.2 == .rook) with
  | some (s, _) => some [s]
  | none =>
  match mostAdvancedPawn c pieces with
  | some s => some [s]
  | none =>
    let bishops := pieces.filterMap fun (s, k) => if k == .bishop then some s else none
    let knights := pieces.filterMap fun (s, k) => if k == .knight then some s else none
    match bishops.find? (·.color == .white), bishops.find? (·.color == .black) with
    | some l, some d => some [l, d]
    | _, _ =>
      match bishops, knights with
      | b :: _, n :: _ => some [b, n]
      | _, n₁ :: n₂ :: _ => some [n₁, n₂]
      | _, _ => none

/-! ### Movement and search for a single piece -/

/-- Empty squares of `b` that the piece `q`, imagined on `u`, attacks. -/
def destsFrom (b : Board) (q : Piece) (u : Square) : List Square :=
  let b' := b.place u q
  allSquares.filter fun t => (b t).isNone && b'.attacks u t

/-- Unreachable distance marker. -/
def far : Nat := 1000

/-- Multi-source breadth-first distances to `sources` over the empty
squares of `b` that satisfy `allowed`, moving as the piece `q`. The
movement of kings, knights, and sliders is symmetric, so this is also the
distance from each square to the nearest source. -/
def bfsDist (b : Board) (q : Piece) (sources : List Square) (allowed : Square → Bool)
    (maxDepth : Nat) : Array Nat :=
  let init := sources.foldl (fun (a : Array Nat) s => a.setIfInBounds (idx s) 0)
    (Array.replicate 64 far)
  let rec go (frontier : List Square) (dist : Array Nat) (d : Nat) : Nat → Array Nat
    | 0 => dist
    | fuel + 1 =>
      let (next, dist) := frontier.foldl
        (fun (acc : List Square × Array Nat) u =>
          (destsFrom b q u).foldl
            (fun (acc : List Square × Array Nat) t =>
              if acc.2.getD (idx t) far == far && allowed t then
                (t :: acc.1, acc.2.setIfInBounds (idx t) d)
              else acc)
            acc)
        ([], dist)
      if next.isEmpty then dist else go next dist (d + 1) fuel
  go sources init 1 maxDepth

/-- The first step of a shortest route for the piece `q` from `start` to
one of the `goals`, through empty squares satisfying `allowed`. -/
def firstStepToward (b : Board) (q : Piece) (start : Square) (goals : List Square)
    (allowed : Square → Bool) : Option Square :=
  let b₀ := b.clear start
  let dist := bfsDist b₀ q goals allowed 12
  let cands := (destsFrom b₀ q start).filter fun t =>
    allowed t && dist.getD (idx t) far < far
  cands.foldl
    (fun best t =>
      match best with
      | none => some t
      | some u => if dist.getD (idx t) far < dist.getD (idx u) far then some t else best)
    none

/-! ### Safety checks -/

/-- Whether the lone king on `bk` has a legal move in `p`. -/
def loneHasMove (p : Position) (bk : Square) : Bool :=
  (kingNeighbors bk).any fun d => p.isLegalMove (Move.std bk d)

/-- Whether the lone king on `bk`, to move in `p`, is checkmated. -/
def loneMated (p : Position) (bk : Square) : Bool :=
  p.inCheck && !loneHasMove p bk

/-- Whether `p` is a proven three-piece ending that is dead. -/
def knownDead (p : Position) : Bool :=
  match KQState.ofPosition? p with
  | some s => s.deadB
  | none =>
  match KRState.ofPosition? p with
  | some s => s.deadB
  | none =>
  match KPState.ofPosition? p with
  | some s => s.deadB
  | none => false

/-- Whether `p` is a proven three-piece ending. -/
def knownState (p : Position) : Bool :=
  (KQState.ofPosition? p).isSome || (KRState.ofPosition? p).isSome ||
    (KPState.ofPosition? p).isSome

/-- Whether the strong side has some legal move in `p` (its king on `wk`). -/
def strongHasMove (p : Position) (c : Color) (wk : Square) : Bool :=
  ((kingNeighbors wk).any fun d => p.isLegalMove (Move.std wk d)) ||
    (piecesOf p.board c).any fun (s, k) =>
      match k with
      | .pawn =>
        (shift s 0 (pawnPushDelta c)).any fun a =>
          p.isLegalMove (Move.std s a) || p.isLegalMove (Move.promote s a .queen)
      | _ => (destsFrom p.board ⟨c, k⟩ s).any fun t => p.isLegalMove (Move.std s t)

/-- A strong-side move is acceptable when it is legal and afterwards the
lone king (on `bk`) either has a legal move or is checkmated, and the
result is not a dead three-piece ending. -/
def afterOk (p : Position) (bk : Square) (m : Move) : Bool :=
  p.isLegalMove m &&
    let p' := (p.play m).normalize
    (loneHasMove p' bk || p'.inCheck) && !knownDead p'

/-- Whether the strong move `m` gives check. -/
def givesCheck (p : Position) (m : Move) : Bool :=
  ((p.play m).normalize).inCheck

/-! ### Reduction: sacrifices, promotions, waiting moves -/

/-- Offer the piece `q` on `x` to the lone king: move it to an unprotected
square next to the king when possible, otherwise take the first step of
a route to such a square. -/
def sacrificeMove (c : Ctx) (x : Square) (q : Piece) : Option Move :=
  let b := c.p.board
  let others := b.clear x
  let landing := (kingNeighbors c.bk).filter fun t =>
    (b t).isNone && !(others.isAttackedBy c.strong t)
  let offer := landing.find? fun t =>
    let m := Move.std x t
    afterOk c.p c.bk m &&
      let p' := (c.p.play m).normalize
      p'.isLegalMove (Move.std c.bk t) &&
        let p'' := (p'.play (Move.std c.bk t)).normalize
        !knownDead p'' && strongHasMove p'' c.strong c.wk
  match offer with
  | some t => some (Move.std x t)
  | none =>
    match firstStepToward b q x landing (fun _ => true) with
    | some t => if afterOk c.p c.bk (Move.std x t) then some (Move.std x t) else none
    | none => none

/-- The first `some` produced by `f` over `l`. -/
def firstSome {α β : Type} (l : List α) (f : α → Option β) : Option β :=
  l.foldl (fun acc a => match acc with | some _ => acc | none => f a) none

/-- Move the piece `q` on `a` out of the way, to any acceptable square
outside `avoid`. -/
def moveAside (c : Ctx) (a : Square) (q : Piece) (avoid : List Square) : Option Move :=
  let dests := (destsFrom (c.p.board.clear a) q a).filter fun t => !(avoid.contains t)
  let ok (t : Square) : Bool := afterOk c.p c.bk (Move.std a t)
  match dests.find? (fun t => ok t && !givesCheck c.p (Move.std a t)) with
  | some t => some (Move.std a t)
  | none => (dests.find? ok).map (Move.std a)

/-- Promotion kinds to try, in order. -/
def promotionKinds : List PieceKind := [.queen, .rook, .knight, .bishop]

/-- Advance the most advanced pawn: promote, push two squares, or push one
square; if a strong piece blocks it, move that piece aside. -/
def pawnMove (c : Ctx) : Option Move :=
  match mostAdvancedPawn c.strong c.pieces with
  | none => none
  | some s =>
    match shift s 0 (pawnPushDelta c.strong) with
    | none => none
    | some a =>
      match c.p.board a with
      | none =>
        if a.rank == pawnPromotionRank c.strong then
          firstSome promotionKinds fun k =>
            let m := Move.promote s a k
            if afterOk c.p c.bk m then some m else none
        else
          let double := (shift s 0 (2 * pawnPushDelta c.strong)).bind fun a₂ =>
            let m := Move.std s a₂
            if afterOk c.p c.bk m then some m else none
          match double with
          | some m => some m
          | none =>
            let m := Move.std s a
            if afterOk c.p c.bk m then some m else none
      | some q =>
        if q.color == c.strong && q.kind != .pawn then
          moveAside c a q (pawnPath c.strong s)
        else none

/-- A waiting move: the strong king, then any non-pawn piece, then a pawn;
never landing on `avoid`, preferring not to give check. -/
def tempoMove (c : Ctx) (avoid : List Square) : Option Move :=
  let b := c.p.board
  let kingMoves := (destsFrom (b.clear c.wk) ⟨c.strong, .king⟩ c.wk).map (Move.std c.wk)
  let pieceMoves (pawn : Bool) : List Move :=
    (c.pieces.filter fun (_, k) => (k == .pawn) == pawn).flatMap fun (s, k) =>
      if k == .pawn then
        match shift s 0 (pawnPushDelta c.strong) with
        | some a => if a.rank == pawnPromotionRank c.strong then [Move.promote s a .queen]
                    else [Move.std s a]
        | none => []
      else (destsFrom (b.clear s) ⟨c.strong, k⟩ s).map (Move.std s)
  let cands := (kingMoves ++ pieceMoves false ++ pieceMoves true).filter fun m =>
    !(avoid.contains m.dst)
  match cands.find? (fun m => afterOk c.p c.bk m && !givesCheck c.p m) with
  | some m => some m
  | none => cands.find? (afterOk c.p c.bk)

/-- With only the keeper left but the ending not yet recognized (castling
rights remain), make a move that reaches a recognized non-dead state. -/
def keeperOnlyMove (c : Ctx) : Option Move :=
  let b := c.p.board
  let kingMoves := (destsFrom (b.clear c.wk) ⟨c.strong, .king⟩ c.wk).map (Move.std c.wk)
  let pieceMoves := c.pieces.flatMap fun (s, k) =>
    (destsFrom (b.clear s) ⟨c.strong, k⟩ s).map (Move.std s)
  let cands := kingMoves ++ pieceMoves
  match cands.find? (fun m => afterOk c.p c.bk m && knownState (c.p.play m).normalize) with
  | some m => some m
  | none => cands.find? (afterOk c.p c.bk)

/-! ### Two minor pieces: the corner picture

In the canonical frame (White strong, corner `a8`) the strong king stands
on `c7`, the lone king shuffles between `a8` and `a7`, one piece (the
*coverer*) waits one move away from a square attacking `a7`, and the
other (the *checker*) waits one move away from a square attacking `a8`.
With the lone king on `a7` the coverer checks it, the king returns to
`a8`, and the checker mates. A light bishop checks from `e4`; a knight
from `b6`. A dark bishop covers from `c5`; a knight from `b5`. When the
parity is wrong (lone king on `a8` and everything ready), the strong king
walks the triangle `c7–d8–d7–c7`.

A bishop must check into a corner of its own square color, so a dark
bishop with a knight uses the frame reflected onto `a1`; Black as the
strong side uses the frame rotated by 180°. -/

/-- Reflection across the middle of the board (ranks). -/
def flipV (s : Square) : Square :=
  ⟨s.file, ⟨7 - s.rank.val, by have := Nat.le_of_lt_succ s.rank.isLt; omega⟩⟩

/-- A symmetry of the board: an optional rank reflection followed by an
optional 180° rotation. Every frame is an involution. -/
structure Frame where
  /-- Reflect the ranks. -/
  flip : Bool
  /-- Rotate by 180°. -/
  rot : Bool

/-- Apply the frame to a square. -/
def Frame.map (f : Frame) (s : Square) : Square :=
  let s₁ := if f.flip then flipV s else s
  if f.rot then s₁.rot180 else s₁

/-- Corner in which the lone king is mated. -/
def corner : Square := sq 0 7
/-- The square beside the corner, on which the lone king waits. -/
def side : Square := sq 0 6
/-- Square of the strong king in the mating picture. -/
def kingTarget : Square := sq 2 6
/-- First square of the strong king's waiting triangle. -/
def tri₁ : Square := sq 3 7
/-- Second square of the strong king's waiting triangle. -/
def tri₂ : Square := sq 3 6

/-- A role in the picture: the square from which the piece acts, and the
squares from which it reaches that square in one move without attacking
the corner or the square beside it. -/
structure Role where
  /-- Final square of the piece. -/
  final : Square
  /-- Waiting squares. -/
  pre : List Square

/-- A light bishop giving the final check on `a8` from `e4`. -/
def bishopChecker : Role := ⟨sq 4 3, [sq 1 0, sq 2 1, sq 3 2, sq 5 4, sq 6 5, sq 7 6]⟩
/-- A knight giving the final check on `a8` from `b6`. -/
def knightChecker : Role := ⟨sq 1 5, [sq 0 3, sq 2 3, sq 3 4]⟩
/-- A dark bishop covering `a7` from `c5`. -/
def bishopCoverer : Role := ⟨sq 2 4, [sq 3 5, sq 1 3, sq 0 2, sq 4 6, sq 5 7]⟩
/-- A knight covering `a7` from `b5`. -/
def knightCoverer : Role := ⟨sq 1 4, [sq 0 2, sq 2 2, sq 3 3, sq 3 5]⟩

/-- The assignment of the two minor pieces to the picture. -/
structure MinorPlan where
  /-- Frame mapping canonical squares to the board. -/
  frame : Frame
  /-- Square, piece, and role of the checker. -/
  checker : Square × Piece × Role
  /-- Square, piece, and role of the coverer. -/
  coverer : Square × Piece × Role

/-- The plan for exactly two minor pieces that can mate. -/
def minorPlan (c : Ctx) : Option MinorPlan :=
  let rot := c.strong == .black
  let bn (b n : Square) : MinorPlan :=
    ⟨⟨b.color == .black, rot⟩, (b, ⟨c.strong, .bishop⟩, bishopChecker),
      (n, ⟨c.strong, .knight⟩, knightCoverer)⟩
  match c.pieces with
  | [(s₁, k₁), (s₂, k₂)] =>
    match k₁, k₂ with
    | .bishop, .bishop =>
      if s₁.color == s₂.color then none
      else
        let (l, d) := if s₁.color == .white then (s₁, s₂) else (s₂, s₁)
        some ⟨⟨false, rot⟩, (l, ⟨c.strong, .bishop⟩, bishopChecker),
          (d, ⟨c.strong, .bishop⟩, bishopCoverer)⟩
    | .bishop, .knight => some (bn s₁ s₂)
    | .knight, .bishop => some (bn s₂ s₁)
    | .knight, .knight =>
      -- The pieces are listed by square, so the assignment of the two
      -- knights must not depend on that order: take the one that is
      -- closer to completion, which then stays fixed as the knights move.
      let f := (Frame.mk false rot).map
      let q : Piece := ⟨c.strong, .knight⟩
      let cost (s : Square) (r : Role) : Nat :=
        (bfsDist (c.p.board.clear s) q (r.pre.map f) (fun _ => true) 12).getD (idx s) far
      let (ch, cv) :=
        if cost s₂ knightChecker + cost s₁ knightCoverer <
            cost s₁ knightChecker + cost s₂ knightCoverer then (s₂, s₁)
        else (s₁, s₂)
      some ⟨⟨false, rot⟩, (ch, q, knightChecker), (cv, q, knightCoverer)⟩
    | _, _ => none
  | _ => none

/-- Whether the piece `q`, imagined on `t`, would attack `u` on `b`. -/
def wouldAttack (b : Board) (q : Piece) (t u : Square) : Bool :=
  (b.place t q).attacks t u

/-- The strong side's move in the two-minor-piece picture. -/
def minorStrongMove (c : Ctx) (pl : MinorPlan) : Option Move :=
  let f := pl.frame.map
  let b := c.p.board
  let bkC := f c.bk
  let wkC := f c.wk
  let (chS, chP, chR) := pl.checker
  let (cvS, cvP, cvR) := pl.coverer
  let kingReady := wkC == kingTarget
  let chReady := chR.pre.contains (f chS)
  let cvReady := cvR.pre.contains (f cvS)
  let attempt (m : Move) : Option Move := if afterOk c.p c.bk m then some m else none
  let reserved : List Square :=
    [corner, side, kingTarget, tri₁, tri₂, chR.final, cvR.final].map f
  let quiet (q : Piece) (t : Square) : Bool :=
    !(reserved.contains t) && !(wouldAttack b q t (f corner)) && !(wouldAttack b q t (f side))
  let progress (s : Square) (q : Piece) (goals : List Square) (allowed : Square → Bool) :
      Option Move :=
    match firstStepToward b q s goals allowed with
    | some t => attempt (Move.std s t)
    | none => none
  if bkC == corner && f cvS == cvR.final && chReady && kingReady then
    attempt (Move.std chS (f chR.final))
  else if bkC == side && kingReady && chReady && cvReady then
    attempt (Move.std cvS (f cvR.final))
  else if bkC == corner && kingReady && chReady && cvReady then
    attempt (Move.std c.wk (f tri₁))
  else if wkC == tri₁ && chReady && cvReady then
    attempt (Move.std c.wk (f tri₂))
  else if wkC == tri₂ && chReady && cvReady then
    attempt (Move.std c.wk (f kingTarget))
  else
    let kingAllowed (t : Square) : Bool :=
      !(decide (KingAttacks t c.bk)) && !([corner, side].map f).contains t
    let kingStep := if kingReady then none
      else progress c.wk ⟨c.strong, .king⟩ [f kingTarget] kingAllowed
    match kingStep with
    | some m => some m
    | none =>
      let chStep := if chReady then none
        else progress chS chP (chR.pre.map f) (quiet chP)
      match chStep with
      | some m => some m
      | none =>
        let cvStep := if cvReady then none
          else progress cvS cvP (cvR.pre.map f) (quiet cvP)
        match cvStep with
        | some m => some m
        | none =>
          -- waiting: shuffle a ready piece among its waiting squares
          let shuffle (s : Square) (r : Role) : Option Move :=
            firstSome (r.pre.map f) fun t => if t == s then none else attempt (Move.std s t)
          match shuffle chS chR with
          | some m => some m
          | none =>
            match shuffle cvS cvR with
            | some m => some m
            | none => tempoMove c ([corner, side].map f)

/-! ### The lone king's policy -/

/-- Capture an adjacent unprotected strong piece that is not a keeper. -/
def loneCapture (c : Ctx) (keep : List Square) : Option Move :=
  let t? := (kingNeighbors c.bk).find? fun t =>
    match c.p.board t with
    | some q =>
      q.color == c.strong && q.kind != .king && !(keep.contains t) &&
        let m := Move.std c.bk t
        c.p.isLegalMove m &&
          let p' := (c.p.play m).normalize
          !knownDead p' && strongHasMove p' c.strong c.wk
    | none => false
  t?.map (Move.std c.bk)

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- A waiting move of the lone king: the legal step that keeps the most
mobility, stays off `avoid`, and stays central. -/
def loneTempo (c : Ctx) (avoid : List Square) : Option Move :=
  let b := c.p.board
  let cands := (kingNeighbors c.bk).filter fun t =>
    (b t).isNone && c.p.isLegalMove (Move.std c.bk t)
  let score (t : Square) : Nat :=
    let b' := b.relocate c.bk t ⟨c.lone, .king⟩
    let mobility := ((kingNeighbors t).filter fun u =>
      (b' u).isNone && !(b'.isAttackedBy c.strong u)).length
    let central := (3 - min 3 (dist t.file.val 3)) + (3 - min 3 (dist t.rank.val 3))
    (if avoid.contains t then 0 else 100) + 10 * mobility + central
  let best := cands.foldl
    (fun (acc : Option (Square × Nat)) t =>
      let sc := score t
      match acc with
      | none => some (t, sc)
      | some (_, s) => if sc > s then some (t, sc) else acc)
    none
  best.map fun (t, _) => Move.std c.bk t

/-- The lone king's move in the two-minor-piece picture: shuffle between
the corner and the square beside it, or walk to the corner. -/
def minorLoneMove (c : Ctx) (pl : MinorPlan) : Option Move :=
  let f := pl.frame.map
  let legal (t : Square) : Bool := c.p.isLegalMove (Move.std c.bk t)
  let bkC := f c.bk
  let fallback := loneTempo c []
  if bkC == corner then
    if legal (f side) then some (Move.std c.bk (f side)) else fallback
  else if bkC == side then
    if legal (f corner) then some (Move.std c.bk (f corner)) else fallback
  else
    let allowed (t : Square) : Bool := !(c.p.board.isAttackedBy c.strong t)
    match firstStepToward c.p.board ⟨c.lone, .king⟩ c.bk [f corner] allowed with
    | some t => if legal t then some (Move.std c.bk t) else fallback
    | none => fallback

/-! ### Assembling the line -/

/-- The strong side's move. -/
def strongMove (c : Ctx) : Option Move :=
  match keeper c.strong c.pieces with
  | none => none
  | some keep =>
    let targets := c.pieces.filter fun (s, k) => k != .pawn && !(keep.contains s)
    let hasPawn := c.pieces.any (·.2 == .pawn)
    match firstSome targets (fun (s, k) => sacrificeMove c s ⟨c.strong, k⟩) with
    | some m => some m
    | none =>
      if hasPawn then
        match pawnMove c with
        | some m => some m
        | none =>
          let avoid := match mostAdvancedPawn c.strong c.pieces with
            | some s => pawnPath c.strong s
            | none => []
          tempoMove c avoid
      else if targets.isEmpty then
        match keep with
        | [_] => keeperOnlyMove c
        | _ =>
          match minorPlan c with
          | some pl => minorStrongMove c pl
          | none => none
      else tempoMove c []

/-- The lone side's move. -/
def loneMove (c : Ctx) : Option Move :=
  match keeper c.strong c.pieces with
  | none => loneTempo c []
  | some keep =>
    match loneCapture c keep with
    | some m => some m
    | none =>
      let targets := c.pieces.filter fun (s, k) => k != .pawn && !(keep.contains s)
      let hasPawn := c.pieces.any (·.2 == .pawn)
      if targets.isEmpty && !hasPawn then
        match minorPlan c with
        | some pl => minorLoneMove c pl
        | none => loneTempo c []
      else
        let avoid := match mostAdvancedPawn c.strong c.pieces with
          | some s => pawnPath c.strong s
          | none => []
        loneTempo c avoid

/-- The proven mating line of a recognized three-piece ending. -/
def knownLine? (p : Position) : Option (List Move) :=
  if (KQState.ofPosition? p).isSome then some (Position.kingQueenMatingLine p)
  else if (KRState.ofPosition? p).isSome then some (Position.kingRookMatingLine p)
  else if (KPState.ofPosition? p).isSome then some (Position.kingPawnMatingLine p)
  else none

/-- Build the line ply by ply; `acc` holds the moves so far in reverse. -/
def engineer : Nat → Position → List Move → List Move
  | 0, _, acc => acc.reverse
  | fuel + 1, p, acc =>
    match Ctx.of? p with
    | none => acc.reverse
    | some c =>
      if p.toMove == c.lone && loneMated p c.bk then acc.reverse
      else
        match knownLine? p with
        | some line => acc.reverse ++ line
        | none =>
          match (if p.toMove == c.strong then strongMove c else loneMove c) with
          | none => acc.reverse
          | some m => engineer fuel (p.play m).normalize (m :: acc)

/-- Plies allowed for the engineered line. -/
def fuel : Nat := 600

end LoneKing

namespace Position

/-- The engineered mating line from a position in which one side has a
bare king: sacrifices, promotions, and then a proven three-piece line or
the two-minor-piece corner picture. The result is `[]` or an incomplete
line when the engineering does not succeed; `loneKingCheckmateReachable`
checks the outcome. -/
def loneKingMatingLine (p : Position) : List Move :=
  LoneKing.engineer LoneKing.fuel p.normalize []

/-- Whether checkmate is reachable from a position in which one side has a
bare king. A proven three-piece ending (king and queen, rook, or pawn
versus king) is answered by its state; otherwise the engineered line
must be legal and end in checkmate. Sound for every valid position
(`loneKingCheckmateReachable_sound`) and complete for the three-piece
endings (`loneKingCheckmateReachable_iff_of_card_le_three`). -/
def loneKingCheckmateReachable (p : Position) : Bool :=
  match KQState.ofPosition? p with
  | some s => !s.deadB
  | none =>
  match KRState.ofPosition? p with
  | some s => !s.deadB
  | none =>
  match KPState.ofPosition? p with
  | some s => !s.deadB
  | none =>
    let line := p.loneKingMatingLine
    pathLegalN p line && (playSeqN p line).inCheckmate

end Position

namespace LoneKing

open KQState (allSquares)

/-! ### Engineering a proof of deadness

The negative answer is also engineered rather than searched for: a
position is recognized as dead when it is a valid three-piece ending (or
two kings) without castling rights that `loneKingCheckmateReachable`
rejects, or when it is not checkmate and every legal move leads to a
position recognized as dead, to a small fixed depth. Stalemate is the case
of no legal move at all. -/

/-- Every promotion field a move can carry. -/
def promotionFields : List (Option PieceKind) :=
  [none, some .queen, some .rook, some .bishop, some .knight, some .king, some .pawn]

/-- A superset of the legal moves of `p`: every move from a square holding a
piece of the side to move (`mem_candidateMoves_of_legalMove`). -/
def candidateMoves (p : Position) : List Move :=
  (allSquares.filter fun s =>
      match p.board s with
      | some q => q.color == p.toMove
      | none => false).flatMap fun s =>
    allSquares.flatMap fun t => promotionFields.map fun pr => ⟨s, t, pr⟩

/-- A position settled as dead by the proven three-piece theories: valid,
at most three pieces, no castling rights, and rejected by
`loneKingCheckmateReachable`. -/
def deadLeaf (p : Position) : Bool :=
  Position.isValid p && p.board.occupied.card ≤ 3 && decide (p.castling = ∅) &&
    !p.loneKingCheckmateReachable

/-- Deadness to the given depth: a leaf, or not checkmate with every legal
move leading to a position dead to the smaller depth. -/
def deadWithin : Nat → Position → Bool
  | 0, p => deadLeaf p
  | fuel + 1, p =>
    deadLeaf p ||
      (!p.inCheckmate && (candidateMoves p).all fun m =>
        !p.isLegalMove m || deadWithin fuel (p.play m).normalize)

/-- Depth of the deadness check. -/
def deadFuel : Nat := 2

end LoneKing

namespace Position

/-- Whether the position is recognized as dead: a proven three-piece
verdict, stalemate, or every legal move leading to such a position within
two plies. Sound (`loneKingDead_sound`); a `false` answer proves nothing. -/
def loneKingDead (p : Position) : Bool :=
  LoneKing.deadWithin LoneKing.deadFuel p.normalize

/-- Whether the engineered procedures settle the position one way or the
other without the exhaustive fallback of `loneKingVerdict`. -/
def loneKingDecided (p : Position) : Bool :=
  loneKingCheckmateReachable p || loneKingDead p

/-! ### Positions form a finite type with decidable equality

Needed to bound the exhaustive exploration below: a list of distinct
positions has at most `Fintype.card Position` entries. Neither instance
is ever evaluated at run time. -/

instance : DecidableEq Board :=
  inferInstanceAs (DecidableEq (Square → Option Piece))

instance : Fintype Board :=
  inferInstanceAs (Fintype (Square → Option Piece))

/-- Forget the structure, viewing a position as a tuple. -/
def equivProd : Position ≃ Board × Color × CastlingRights × Option Square where
  toFun p := (p.board, p.toMove, p.castling, p.enPassant)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
  left_inv p := by
    cases p
    rfl
  right_inv q := by
    rcases q with ⟨_, _, _, _⟩
    rfl

end Position

deriving instance DecidableEq for Position

instance : Fintype Position :=
  Fintype.ofEquiv _ Position.equivProd.symm

namespace LoneKing

/-! ### Exhaustive fallback

The positions the engineered procedures leave open are explored
exhaustively. Every position met is either settled on the spot or
expanded into the positions its legal moves reach; the exploration ends
with `true` at the first position that is checkmate or whose engineered
line succeeds, and with `false` once every reachable position has been
seen without meeting one (`explore_spec` in `Chess.LoneKingTheorems`).
Positions recognized as dead are not expanded. -/

/-- The positions reached by the legal moves of `q`, with tabulated
boards. -/
def successors (q : Position) : List Position :=
  (candidateMoves q).filterMap fun m =>
    if q.isLegalMove m then some (q.play m).normalize else none

/-- A position settled as dead without expansion, the lone king being of
color `c`: a rejected three-piece ending, or the strong side left with a
king and bishops all on squares of one color. -/
def deadNode (c : Color) (q : Position) : Bool :=
  deadLeaf q || decide (Position.OnlyBishopsOn c.other .white q) ||
    decide (Position.OnlyBishopsOn c.other .black q)

/-- Plies allowed for the engineered line tried at every explored
position. Shorter than `fuel`, since a line that wanders is tried again
from the next position. -/
def probeFuel : Nat := 120

/-- Whether a legal engineered line from `q`, with `probeFuel` plies, ends
in checkmate. Sound without any hypothesis on `q`: the line is checked. -/
def probeLive (q : Position) : Bool :=
  let line := engineer probeFuel q.normalize []
  Position.pathLegalN q line && (Position.playSeqN q line).inCheckmate

/-- The members of `succ` not yet in `V`. -/
def fresh (V succ : List Position) : List Position :=
  succ.filter fun r => decide (r ∉ V)

/-- Explore the positions of the work list `W`, all of which belong to the
list `V` of positions seen so far. A position is settled as live when
`probeLive` finds a mating line from it or when it is checkmate (in check
with no successor); it is left unexpanded when `deadNode` recognizes it
as dead; otherwise its unseen successors are appended to both lists.
Terminates because `V` only grows by positions not yet in it. -/
def explore (c : Color) (V : List Position) : List Position → Bool
  | [] => false
  | q :: W =>
    if probeLive q then true
    else if deadNode c q then explore c V W
    else
      let succ := successors q
      if q.inCheck && succ.isEmpty then true
      else explore c (V ++ fresh V succ) (W ++ fresh V succ)
termination_by W => (Fintype.card Position - V.toFinset.card, W.length)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · by_cases hnew : fresh V (successors q) = []
    · rw [hnew, List.append_nil, List.append_nil]
      exact Prod.Lex.right _ (Nat.lt_succ_self _)
    · apply Prod.Lex.left
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hnew
      have hrV : r ∉ V := of_decide_eq_true (List.mem_filter.mp hr).2
      have hsub : V.toFinset ⊆ (V ++ fresh V (successors q)).toFinset := by
        rw [List.toFinset_append]
        exact Finset.subset_union_left
      have hlt : V.toFinset.card < (V ++ fresh V (successors q)).toFinset.card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
          ⟨r, by simp [hr], by simpa using hrV⟩)
      have hle := (V ++ fresh V (successors q)).toFinset.card_le_univ
      omega

end LoneKing

namespace Position

/-- Whether checkmate is reachable from a position in which one player
has only a king. The engineered procedures answer first
(`loneKingCheckmateReachable`, then `loneKingDead`); a position they leave
open is explored exhaustively by `LoneKing.explore`. Correct for every
valid position with a bare king (`loneKingVerdict_iff`), which makes
`loneKingDecidable` a `Decidable (CheckmateReachable p)`. -/
def loneKingVerdict (p : Position) : Bool :=
  if loneKingCheckmateReachable p then true
  else if loneKingDead p then false
  else
    let p' := p.normalize
    LoneKing.explore (loneColor p) [p'] [p']

end Position

end Chess
