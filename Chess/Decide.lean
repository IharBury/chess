import Chess.LoneKingTheorems
import Chess.KingKnights

/-!
# Deciding `CheckmateReachable` for an arbitrary valid position

Specialized decision procedures already cover a bare king against any
material (`Position.loneKingDecidable`) and the three- and four-piece
endings of the earlier modules. This module decides the remaining
positions: it first tries a short cooperative mating line (a checked
engineered path, including Fool's mate from the standard start, a
reduction by capture into a known ending, or a bounded help-mate search),
then recognizes material that can never mate (kings and bishops all on
one square-color), and otherwise explores the reachable graph exactly as
`LoneKing.explore` does.

The engineered answers are checked with `Position.pathLegalN` and
`Position.inCheckmate`, so a `true` verdict is sound with no extra
hypothesis. A `false` verdict from the exploration is sound for every
valid start: every reachable position is closed off, and a closed-off
graph that never meets checkmate is dead. Together these give
`Position.checkmateReachableDecidable`.
-/

namespace Chess

namespace Position

/-- Every non-king piece is a bishop standing on a square of color `χ`. -/
def BishopsOnly (χ : Color) (p : Position) : Prop :=
  ∀ s q, p.board s = some q → q.kind ≠ .king → q.kind = .bishop ∧ s.color = χ

instance {χ : Color} {p : Position} : Decidable (BishopsOnly χ p) := by
  unfold BishopsOnly
  infer_instance

/-- There is a square-color on which every bishop (and there is no other
non-king material) stands. Vacuously true of two kings alone. -/
def BishopsOnlySame (p : Position) : Prop :=
  ∃ χ, BishopsOnly χ p

instance {p : Position} : Decidable (BishopsOnlySame p) := by
  unfold BishopsOnlySame
  infer_instance

/-- Computational form of `BishopsOnlySame`. -/
def bishopsOnlySameB (p : Position) : Bool :=
  decide (BishopsOnlySame p)

/-- Material that cannot mate even with cooperation: two kings, or kings
and bishops all standing on squares of one color. -/
def materialDeadB (p : Position) : Bool :=
  bishopsOnlySameB p

end Position

namespace Decide

open KQState (allSquares kingNeighbors)
open LoneKing (fingerprint attackSquares legalFast findKing attackedFast)

/-- Promotion kinds a pawn may become. -/
def promoKinds : List PieceKind := [.queen, .rook, .bishop, .knight]

/-- A pawn move to `dst`, with the four promotions when `dst` is the last
rank. -/
def withPromo (src dst : Square) (c : Color) : List Move :=
  if dst.rank == pawnPromotionRank c then promoKinds.map (Move.promote src dst)
  else [Move.std src dst]

/-- Pawn destinations from `s` in `p`: single and double pushes, captures,
and en passant. -/
def pawnMoves (p : Position) (s : Square) (c : Color) : List Move :=
  let d := pawnPushDelta c
  let pushes : List Move :=
    match KQState.shift s 0 d with
    | none => []
    | some a =>
      let one := if (p.board a).isNone then withPromo s a c else []
      let two :=
        if s.rank == pawnStartRank c then
          match KQState.shift s 0 (2 * d) with
          | some b =>
            if (p.board a).isNone && (p.board b).isNone then [Move.std s b] else []
          | none => []
        else []
      one ++ two
  let caps : List Move :=
    [KQState.shift s 1 d, KQState.shift s (-1) d].filterMap id |>.flatMap fun t =>
      match p.board t with
      | some q =>
        if q.color != c && q.kind != .king then withPromo s t c else []
      | none => if p.enPassant == some t then [Move.std s t] else []
  pushes ++ caps

/-- Destinations of a non-pawn piece, empty or enemy non-king. -/
def pieceDests (b : Board) (q : Piece) (s : Square) : List Square :=
  (attackSquares b q s).filter fun t =>
    match b t with
    | none => true
    | some r => r.color != q.color && r.kind != .king

/-- Candidate dests of the piece on `s`, including castling king steps. -/
def rawMoves (p : Position) (s : Square) (q : Piece) : List Move :=
  match q.kind with
  | .pawn => pawnMoves p s q.color
  | .king =>
    let steps := (kingNeighbors s).filterMap fun t =>
      match p.board t with
      | none => some (Move.std s t)
      | some r =>
        if r.color != q.color && r.kind != .king then some (Move.std s t) else none
    let ks := (⟨q.color, .kingside⟩ : CastlingRight).kingDest
    let qs := (⟨q.color, .queenside⟩ : CastlingRight).kingDest
    steps ++ [Move.std s ks, Move.std s qs]
  | _ => (pieceDests p.board q s).map (Move.std s)

/-- Occupied squares holding a piece of the side to move. -/
def ownSquares (p : Position) : List Square :=
  allSquares.filter fun s =>
    match p.board s with
    | some q => q.color == p.toMove
    | none => false

/-- Fast legal moves: generated dests filtered by `legalFast`. A suggestion,
checked on any line that is returned. -/
def fastMoves (p : Position) (k : Square) : List Move :=
  (ownSquares p).flatMap (fun s =>
    match p.board s with
    | none => []
    | some q => rawMoves p s q) |>.filter (legalFast p k)

/-- Whether the player to move is checkmated according to the fast
generator: in check, with no fast-legal move. -/
def matedFast (p : Position) : Bool :=
  match findKing p.board p.toMove with
  | none => false
  | some k => attackedFast p.board p.toMove.other k && (fastMoves p k).isEmpty

/-- Whether `m` gives check. -/
def givesCheckFast (p : Position) (m : Move) : Bool :=
  let p' := (p.play m).normalize
  match findKing p'.board p'.toMove with
  | none => false
  | some k => attackedFast p'.board p.toMove k

/-- Move ordering for the help-mate search: checks, captures, queen moves,
then the e/f/g-pawn moves that produce Fool's mate, then the rest. -/
def orderedMoves (p : Position) (k : Square) : List Move :=
  let ms := fastMoves p k
  let checks := ms.filter (givesCheckFast p)
  let rest₁ := ms.filter fun m => !(checks.contains m)
  let caps := rest₁.filter fun m => (p.board m.dst).isSome
  let rest₂ := rest₁.filter fun m => (p.board m.dst).isNone
  let queens := rest₂.filter fun m =>
    match p.board m.src with
    | some q => q.kind == .queen
    | none => false
  let rest₃ := rest₂.filter fun m =>
    match p.board m.src with
    | some q => q.kind != .queen
    | none => true
  let pawns := rest₃.filter fun m =>
    let f := m.src.file.val
    (f == 4 || f == 5 || f == 6) &&
      (match p.board m.src with
       | some q => q.kind == .pawn
       | none => false)
  let rest₄ := rest₃.filter fun m => !(pawns.contains m)
  checks ++ caps ++ queens ++ pawns ++ rest₄

/-- Fool's mate, legal from the standard starting position. -/
def foolsMate : List Move :=
  [Move.std Square.f2 Square.f3, Move.std Square.e7 Square.e5,
    Move.std Square.g2 ⟨6, 3⟩, Move.std Square.d8 Square.h4]

/-- A known mating line of a recognized ending, if one applies. -/
def knownLine? (p : Position) : Option (List Move) :=
  match p.loneKingMatingLine? with
  | some ms => some ms
  | none =>
    match KNState.ofPosition? p with
    | some s => some s.matingLine
    | none =>
      match KBState.ofPosition? p with
      | some s => some s.matingLine
      | none =>
        match KQState.ofPosition? p with
        | some _ => some (Position.kingQueenMatingLine p)
        | none =>
          match KRState.ofPosition? p with
          | some _ => some (Position.kingRookMatingLine p)
          | none =>
            match KPState.ofPosition? p with
            | some _ => some (Position.kingPawnMatingLine p)
            | none => none

/-- Whether the line is legal and ends in checkmate. -/
def checkLine (p : Position) (ms : List Move) : Bool :=
  Position.pathLegalN p ms && (Position.playSeqN p ms).inCheckmate

/-- Keep a candidate line only when `checkLine` succeeds. -/
def checkedLine (p : Position) : Option (List Move) → Option (List Move)
  | some line => if checkLine p line then some line else none
  | none => none

/-- A recognized ending whose stored mating line is legal from `q`. -/
def knownLive (q : Position) : Bool :=
  match knownLine? q with
  | some line => checkLine q line
  | none => false

/-- Whether the position after `m` still has cooperative mating material. -/
def liveAfter (p : Position) (m : Move) : Bool :=
  let p' := (p.play m).normalize
  !p'.materialDeadB

/-- Non-king pieces of `p`. -/
def nonKings (p : Position) : List (Square × Piece) :=
  allSquares.filterMap fun s =>
    match p.board s with
    | some q => if q.kind == .king then none else some (s, q)
    | none => none

/-- Bishop versus knight: the bishop's side, the bishop, the knight, and
the two kings. -/
def bnSetup? (p : Position) : Option (Color × Square × Square × Square × Square) :=
  match nonKings p, findKing p.board .white, findKing p.board .black with
  | [(s₁, q₁), (s₂, q₂)], some wk, some bk =>
    match q₁.kind, q₂.kind with
    | .bishop, .knight =>
      if q₁.color == q₂.color then none
      else
        let att := q₁.color
        some (att, s₁, s₂, if att == .white then wk else bk, if att == .white then bk else wk)
    | .knight, .bishop =>
      if q₁.color == q₂.color then none
      else
        let att := q₂.color
        some (att, s₂, s₁, if att == .white then wk else bk, if att == .white then bk else wk)
    | _, _ => none
  | _, _, _ => none

/-- The four corners. -/
def corners : List Square := [⟨0, 0⟩, ⟨7, 0⟩, ⟨0, 7⟩, ⟨7, 7⟩]

/-- Step toward the center along a file. -/
def towardFile (s : Square) : Int := if s.file.val ≥ 4 then -1 else 1

/-- Step toward the center along a rank. -/
def towardRank (s : Square) : Int := if s.rank.val ≥ 4 then -1 else 1

/-- Covering square of the attacking king for a corner mate. -/
def coverSq (corner : Square) : Square :=
  (KQState.shift corner (towardFile corner) (2 * towardRank corner)).getD corner

/-- Square the defending knight occupies in the picture. -/
def blockSq (corner : Square) : Square :=
  (KQState.shift corner (towardFile corner) 0).getD corner

/-- Closest corner of color `χ` to `s`. -/
def closestCorner (χ : Color) (s : Square) : Square :=
  (corners.filter (fun c => c.color == χ)).foldl
    (fun best c => if LoneKing.cheb s c < LoneKing.cheb s best then c else best)
    (if χ == .black then ⟨0, 0⟩ else ⟨0, 7⟩)

/-- Checking squares on the diagonal into the board from `corner`, skipping
the adjacent square (the king would capture there). -/
def checkSquares (corner : Square) : List Square :=
  let df := towardFile corner
  let dr := towardRank corner
  [2, 3, 4, 5, 6, 7].filterMap fun n =>
    KQState.shift corner (n * df) (n * dr)

/-- Distance from `s` to the nearest square of `ts`. -/
def minCheb (s : Square) (ts : List Square) : Nat :=
  ts.foldl (fun n t => min n (LoneKing.cheb s t)) 64

/-- Potential of a bishop-versus-knight picture: smaller is closer to mate. -/
def bnPotential (_p : Position) (bs ns wk bk : Square) : Nat :=
  let corner := closestCorner bs.color bk
  let ready := LoneKing.cheb bk corner + LoneKing.cheb ns (blockSq corner) +
    LoneKing.cheb wk (coverSq corner)
  ready * 8 + minCheb bs (checkSquares corner)

/-- A greedy cooperative move: mate, a capture that keeps mating material,
a bishop-knight picture step, a check, otherwise the first unused dest. -/
def greedyMove (p : Position) (k : Square) (seen : List UInt64) : Option Move :=
  let ms := (orderedMoves p k).filter fun m =>
    !(seen.contains (fingerprint (p.play m).normalize))
  let mate := ms.find? fun m => matedFast (p.play m).normalize
  let cap := ms.find? fun m => (p.board m.dst).isSome && liveAfter p m
  let bn :=
    match bnSetup? p with
    | none => none
    | some (_, bs, ns, wk, bk) =>
      let cur := bnPotential p bs ns wk bk
      ms.foldl
        (fun (acc : Option (Move × Nat)) m =>
          let p' := (p.play m).normalize
          match bnSetup? p' with
          | none => acc
          | some (_, bs', ns', wk', bk') =>
            let sc := bnPotential p' bs' ns' wk' bk'
            if sc < cur then
              match acc with
              | none => some (m, sc)
              | some (_, sc') => if sc < sc' then some (m, sc) else acc
            else acc)
        none |>.map (·.1)
  let chk := ms.find? (givesCheckFast p)
  match mate with
  | some m => some m
  | none =>
    match cap with
    | some m => some m
    | none =>
      match bn with
      | some m => some m
      | none =>
        match chk with
        | some m => some m
        | none => ms.head?

mutual
/-- Bounded depth-first help-mate search. `nodes` is a global visit
budget; `depth` is the remaining plies. -/
def search : Nat → Nat → Position → List UInt64 → List Move → Option (List Move)
  | 0, _, q, _, acc =>
    if matedFast q then some acc.reverse else none
  | _ + 1, 0, q, _, acc =>
    if matedFast q then some acc.reverse else none
  | nodes + 1, depth + 1, q, seen, acc =>
    if matedFast q then some acc.reverse
    else if seen.contains (fingerprint q) then none
    else
      match findKing q.board q.toMove with
      | none => none
      | some k => searchList nodes depth q seen acc (orderedMoves q k)
termination_by nodes depth _ _ _ => (nodes, depth, (0 : Nat))
def searchList : Nat → Nat → Position → List UInt64 → List Move → List Move →
    Option (List Move)
  | _, _, _, _, _, [] => none
  | 0, _, _, _, _, _ => none
  | nodes + 1, depth, q, seen, acc, m :: rest =>
    match search nodes depth (q.play m).normalize (fingerprint q :: seen) (m :: acc) with
    | some line => some line
    | none => searchList nodes depth q seen acc rest
termination_by nodes depth _ _ _ ms => (nodes, depth, ms.length + 1)
end

/-- Iterative deepening from one ply up to `maxDepth`. -/
def iddfs (budget maxDepth : Nat) (p : Position) : Option (List Move) :=
  let rec go : Nat → Option (List Move)
    | 0 => none
    | n + 1 =>
      let d := maxDepth - n
      if d = 0 then go n
      else
        match search budget d p [] [] with
        | some line => some line
        | none => go n
  go maxDepth

/-- Score for best-first search: bishop-knight potential, else a default. -/
def nodeScore (q : Position) : Nat :=
  match bnSetup? q with
  | some (_, bs, ns, wk, bk) => bnPotential q bs ns wk bk
  | none => 50

/-- Least-score entry of a nonempty work list. -/
def pickMin (front : List (Nat × Position × List Move)) :
    Option ((Nat × Position × List Move) × List (Nat × Position × List Move)) :=
  match front with
  | [] => none
  | hd :: tl =>
    let best := tl.foldl
      (fun (b : Nat × Position × List Move) x => if x.1 < b.1 then x else b) hd
    some (best, front.filter fun x => !(x.1 == best.1 && fingerprint x.2.1 == fingerprint best.2.1))

/-- Best-first help-mate search, used for four-piece endings the greedy
policy does not finish. -/
def bestFirst : Nat → List (Nat × Position × List Move) → List UInt64 →
    Option (List Move)
  | 0, _, _ => none
  | _, [], _ => none
  | fuel + 1, front, seen =>
    match pickMin front with
    | none => none
    | some ((_, q, acc), rest) =>
      if matedFast q then some acc.reverse
      else
        match knownLine? q with
        | some line => some (acc.reverse ++ line)
        | none =>
          match findKing q.board q.toMove with
          | none => bestFirst fuel rest seen
          | some k =>
            let ms := fastMoves q k
            match ms.find? fun m => matedFast (q.play m).normalize with
            | some m => some (acc.reverse ++ [m])
            | none =>
              let seen' := fingerprint q :: seen
              let children := ms.filterMap fun m =>
                let q' := (q.play m).normalize
                let fp := fingerprint q'
                if seen'.contains fp then none
                else some (nodeScore q', q', m :: acc)
              let seen'' := children.foldl (fun s c => fingerprint c.2.1 :: s) seen'
              bestFirst fuel (rest ++ children) seen''
termination_by fuel => fuel

/-- Node budget of the four-piece best-first search. -/
def bestFirstBudget : Nat := 4000

/-- Greedy cooperative reduction: captures and checks, switching to a
known line as soon as one applies. -/
def greedy : Nat → Position → List Move → List UInt64 → Option (List Move)
  | 0, _, _, _ => none
  | fuel + 1, p, acc, seen =>
    if matedFast p then some acc.reverse
    else
      match knownLine? p with
      | some line => some (acc.reverse ++ line)
      | none =>
        match findKing p.board p.toMove with
        | none => none
        | some k =>
          match greedyMove p k seen with
          | none => none
          | some m =>
            greedy fuel (p.play m).normalize (m :: acc) (fingerprint p :: seen)
termination_by fuel => fuel

/-- Plies of iterative deepening from a busy position. Fool's mate is
four plies; a larger depth explodes. -/
def iddfsDepth : Nat := 4

/-- Node budget of the help-mate search. -/
def iddfsBudget : Nat := 40000

/-- Plies of the greedy reduction. -/
def greedyFuel : Nat := 400

/-- Depth used when at most six pieces remain. -/
def smallDepth : Nat := 4

/-- Node budget for a small help-mate search. -/
def smallBudget : Nat := 20000

/-- Occupied squares, counted by walking the board. -/
def occCount (p : Position) : Nat :=
  allSquares.foldl (fun n s => if (p.board s).isSome then n + 1 else n) 0

/-- An engineered cooperative mating line, if one is found and checked. -/
def matingLine? (p : Position) : Option (List Move) :=
  let p' := p.normalize
  let n := occCount p'
  (checkedLine p' (some foolsMate)).orElse fun _ =>
  (checkedLine p' (knownLine? p')).orElse fun _ =>
  (checkedLine p' (greedy greedyFuel p' [] [])).orElse fun _ =>
  (checkedLine p' (if n ≤ 6 then
      bestFirst bestFirstBudget [(nodeScore p', p', [])] [] else none)).orElse fun _ =>
  checkedLine p' (if n ≤ 4 then none
    else if n ≤ 8 then iddfs smallBudget smallDepth p'
    else iddfs iddfsBudget iddfsDepth p')

/-- Whether the engineered line succeeds. Sound (`probe_sound`): the line
is checked. -/
def probe (p : Position) : Bool :=
  (matingLine? p).isSome

/-- A position settled as dead without expansion. -/
def deadNode (q : Position) : Bool :=
  LoneKing.deadLeaf q || q.materialDeadB

/-- Explore the work list `W`, all of whose members belong to the seen
list `V`. A position is live when a recognized ending has a checked
mating line or it is checkmate; it is left unexpanded when `deadNode`
recognizes it as dead; otherwise its unseen successors are appended to
both lists. -/
def explore (V : List Position) : List Position → Bool
  | [] => false
  | q :: W =>
    if knownLive q then true
    else if deadNode q then explore V W
    else
      let succ := LoneKing.successors q
      if q.inCheck && succ.isEmpty then true
      else explore (V ++ LoneKing.fresh V succ) (W ++ LoneKing.fresh V succ)
termination_by W => (Fintype.card Position - V.toFinset.card, W.length)
decreasing_by
  · exact Prod.Lex.right _ (Nat.lt_succ_self _)
  · by_cases hnew : LoneKing.fresh V (LoneKing.successors q) = []
    · rw [hnew, List.append_nil, List.append_nil]
      exact Prod.Lex.right _ (Nat.lt_succ_self _)
    · apply Prod.Lex.left
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hnew
      have hrV : r ∉ V := of_decide_eq_true (List.mem_filter.mp hr).2
      have hsub : V.toFinset ⊆ (V ++ LoneKing.fresh V (LoneKing.successors q)).toFinset := by
        rw [List.toFinset_append]
        exact Finset.subset_union_left
      have hlt : V.toFinset.card < (V ++ LoneKing.fresh V (LoneKing.successors q)).toFinset.card :=
        Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr
          ⟨r, by simp [hr], by simpa using hrV⟩)
      have hle := (V ++ LoneKing.fresh V (LoneKing.successors q)).toFinset.card_le_univ
      omega

end Decide

namespace Position

/-- Whether checkmate is reachable from a valid position. Bare-king
positions are dispatched to `loneKingVerdict`. Every other position is
answered by the engineered line when it succeeds, by the material
verdict when the pieces cannot mate, and otherwise by exhaustive
exploration. -/
def checkmateVerdict (p : Position) : Bool :=
  if HasLoneKing p then loneKingVerdict p
  else if Decide.deadNode p then false
  else if Decide.probe p then true
  else
    let p' := p.normalize
    Decide.explore [p'] [p']

/-- The engineered cooperative mating line, `[]` when none is found. -/
def checkmateMatingLine (p : Position) : List Move :=
  (Decide.matingLine? p).getD []

end Position

end Chess
