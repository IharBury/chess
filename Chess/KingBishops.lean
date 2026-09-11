import Chess.SameColorBishops
import Chess.EndsGame

/-!
# King and bishop versus king and bishop

A valid position whose board holds only two kings and two bishops is
king-and-bishop versus king-and-bishop. Bishops keep their square-color,
so the two bishops stand either on the same color or on opposite colors.

Same-color bishops never reach checkmate (`Chess.SameColorBishops`).
Opposite-color bishops always can, whatever the position: the two sides
cooperate (a helpmate, not a forced win) and steer into one known mating
picture.

## The engineered mating line

Coordinates are mirrored (file `x ↦ 7 - x`) when the white bishop is on a
light square, so that in *frame coordinates* the white bishop is always
on the dark long diagonal `a1–h8`. The target picture is then

* black king on `h8`, black bishop on `g8` or `h7`,
* white king on `f6`, white bishop on the long diagonal `a1–e5`,
* White mates by `Kf6–g6` (bishop on `g8`) or `Kf6–f7` (bishop on `h7`),
  a discovered check along the long diagonal.

A potential `KBState.mu` measures the distance of the four pieces from
their targets (with a route for the black king that avoids the white
king's neighborhood, tie-breaking terms for mutual blocks, and a bonus
for being in check). The main theorem shows every legal state either is
checkmate or reaches, by a short legal sequence, a state of strictly
smaller potential. Strong induction on the potential gives
`CheckmateReachable`.

Instead of a large search over all `2 · 64⁴` states, most states are
covered by a *generic* one-ply move that does not depend on the enemy
bishop at all (a king step onto the own bishop's square-color, or a
bishop move while the own king stands on that color: such moves are
legal for every placement of the enemy bishop, which lives on the other
color). Only a few hundred thousand triples `(mover, own pieces, enemy
king)` are examined once each; the residual states are checked by a
cheap scripted policy (`KBState.chain`) with a six-ply window. The whole
check is the Boolean `KBState.checkAll`, verified by `native_decide`.

`kingBishopsCheckmateReachable` decides `CheckmateReachable` for a valid
four-piece king-and-bishop versus king-and-bishop position, and
`kingBishopsMatingLine` produces the concrete mating sequence.
-/

namespace Chess

namespace Board

/-- Whether square `s` holds a bishop of color `c`. -/
def isBishopOf (b : Board) (c : Color) (s : Square) : Bool :=
  match b s with
  | some p => (p.color == c) && (p.kind == .bishop)
  | none => false

theorem isBishopOf_eq (b : Board) (c : Color) (s : Square) :
    b.isBishopOf c s = true ↔ b s = some { color := c, kind := .bishop } := by
  unfold isBishopOf
  cases h : b s with
  | none => simp
  | some p =>
    rcases p with ⟨pc, pk⟩
    simp [beq_iff_eq]

/-- Squares occupied by a bishop of color `c`. -/
def bishopSquares (b : Board) (c : Color) : Finset Square :=
  Finset.univ.filter fun s => b.isBishopOf c s

theorem mem_bishopSquares (b : Board) (c : Color) (s : Square) :
    s ∈ b.bishopSquares c ↔ b s = some { color := c, kind := .bishop } := by
  simp [bishopSquares, isBishopOf_eq]

end Board

namespace Position

/-- `p` contains only two kings and two bishops, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingBishops (p : Position) : Prop :=
  ∃ wk bk wb bb : Square,
    wk ≠ bk ∧
      wk ≠ wb ∧
      wk ≠ bb ∧
      bk ≠ wb ∧
      bk ≠ bb ∧
      wb ≠ bb ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsBishopsBoard wk bk wb bb ∧
      p.castling = ∅ ∧
      p.enPassant = none

/-- `p` contains only two kings and two bishops on opposite square-colors,
with the kings not adjacent, no remaining castling rights, and no en
passant target. -/
def IsOppositeColorBishops (p : Position) : Prop :=
  ∃ wk bk wb bb : Square,
    wk ≠ bk ∧
      wk ≠ wb ∧
      wk ≠ bb ∧
      bk ≠ wb ∧
      bk ≠ bb ∧
      wb ≠ bb ∧
      ¬ KingAttacks wk bk ∧
      wb.color ≠ bb.color ∧
      p.board = Board.kingsBishopsBoard wk bk wb bb ∧
      p.castling = ∅ ∧
      p.enPassant = none

theorem IsSameColorBishops.toKingBishops {p : Position}
    (h : IsSameColorBishops p) : IsKingBishops p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, _, hboard, hc, he⟩ := h
  exact ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb, hna,
    hboard, hc, he⟩

theorem IsOppositeColorBishops.toKingBishops {p : Position}
    (h : IsOppositeColorBishops p) : IsKingBishops p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, _, hboard, hc, he⟩ := h
  exact ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb, hna,
    hboard, hc, he⟩

theorem IsKingBishops.same_or_opposite {p : Position} (h : IsKingBishops p) :
    IsSameColorBishops p ∨ IsOppositeColorBishops p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hboard, hc, he⟩ := h
  by_cases hcol : wb.color = bb.color
  · exact Or.inl ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
      hna, hcol, hboard, hc, he⟩
  · exact Or.inr ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
      hna, hcol, hboard, hc, he⟩

end Position

/-! ## Four-piece states -/

/-- A king-and-bishop versus king-and-bishop position by the squares of
its four pieces and the side to move. -/
structure KBState where
  /-- The side to move. -/
  toMove : Color
  /-- White king. -/
  wk : Square
  /-- Black king. -/
  bk : Square
  /-- White bishop. -/
  wb : Square
  /-- Black bishop. -/
  bb : Square
deriving DecidableEq, Repr

/-- A move of the side to move: its king or its bishop goes to `dst`. -/
inductive KBMove where
  | king (dst : Square)
  | bishop (dst : Square)
deriving DecidableEq, Repr

namespace KBState

/-- All 64 squares. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f => (List.finRange 8).map fun r => ⟨f, r⟩

theorem mem_allSquares (x : Square) : x ∈ allSquares := by
  rcases x with ⟨f, r⟩
  simp [allSquares, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- Index of a square in a 64-entry table. -/
def idx (q : Square) : Nat := q.file.val * 8 + q.rank.val

/-- The square `dx` files and `dy` ranks away from `k`, if on the board. -/
def shift (k : Square) (dx dy : Int) : Option Square :=
  let x := (k.file.val : Int) + dx
  let y := (k.rank.val : Int) + dy
  if h : 0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 then
    some ⟨⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩⟩
  else none

/-- The eight king steps. -/
def kingOffsets : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

/-- Squares a king on `k` can step to, by computation. -/
def kingNeighborsOf (k : Square) : List Square :=
  kingOffsets.filterMap fun p => shift k p.1 p.2

/-- Squares along a ray from `b`, nearest first. -/
def ray (b : Square) (dx dy : Int) : List Square :=
  go 1 7
where
  go (i : Int) : Nat → List Square
    | 0 => []
    | fuel + 1 =>
      match shift b (dx * i) (dy * i) with
      | some d => d :: go (i + 1) fuel
      | none => []

/-- Squares a bishop on `b` can move to on an empty board, by computation. -/
def bishopDestsOf (b : Square) : List Square :=
  ray b 1 1 ++ ray b 1 (-1) ++ ray b (-1) 1 ++ ray b (-1) (-1)

/-- King steps of every square, indexed by `idx`. -/
def kingNeighborsTable : Array (List Square) := (allSquares.map kingNeighborsOf).toArray

/-- Bishop destinations of every square, indexed by `idx`. -/
def bishopDestsTable : Array (List Square) := (allSquares.map bishopDestsOf).toArray

/-- Squares a king on `k` can step to. -/
def kingNeighbors (k : Square) : List Square := kingNeighborsTable.getD (idx k) []

/-- Squares a bishop on `b` can move to on an empty board. -/
def bishopDests (b : Square) : List Square := bishopDestsTable.getD (idx b) []

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- `u` lies strictly between `s` and `t`, for `s` and `t` on a common diagonal.
Agrees with `Between s t u` whenever `BishopAttacks s t`. -/
def diagBetween (s t u : Square) : Bool :=
  s != u && u != t && dist s.file.val u.file.val == dist s.rank.val u.rank.val &&
    dist s.file.val u.file.val + dist u.file.val t.file.val == dist s.file.val t.file.val &&
    dist s.rank.val u.rank.val + dist u.rank.val t.rank.val == dist s.rank.val t.rank.val

/-- Square `d` is attacked by the enemy king `ek` or enemy bishop `eb`, where
the only possible blocker of the bishop ray is the enemy king. (The own
bishop stands on the other square-color and never blocks that ray.) -/
def kingAttackedAt (d ek eb : Square) : Bool :=
  decide (KingAttacks ek d) || (decide (BishopAttacks eb d) && !diagBetween eb d ek)

/-- Geometric legality of the king step `k → d` against enemy king `ek`, enemy
bishop `eb`, and own bishop `ob`. Captures are excluded. -/
def fastKingStep (k d ek eb ob : Square) : Bool :=
  decide (KingAttacks k d) && d != ek && d != eb && d != ob && !kingAttackedAt d ek eb

/-- Geometric legality of the bishop move `b → d` with own king `k`, enemy king
`ek`, and enemy bishop `eb`. Captures are excluded. -/
def fastBishopMove (b d k ek eb : Square) : Bool :=
  decide (BishopAttacks b d) && d != k && d != ek && d != eb &&
    !diagBetween b d k && !diagBetween b d ek && !kingAttackedAt k ek eb

/-- King of `c`. -/
def king (s : KBState) : Color → Square
  | .white => s.wk
  | .black => s.bk

/-- Bishop of `c`. -/
def bishop (s : KBState) : Color → Square
  | .white => s.wb
  | .black => s.bb

/-- The king of `c` is attacked. -/
def inCheckB (s : KBState) (c : Color) : Bool :=
  kingAttackedAt (s.king c) (s.king c.other) (s.bishop c.other)

/-- The state describes a legal opposite-color position: distinct squares,
kings not adjacent, bishops on opposite colors, and the side not to move
not in check. -/
def okB (s : KBState) : Bool :=
  s.wk != s.bk && s.wk != s.wb && s.wk != s.bb && s.bk != s.wb && s.bk != s.bb &&
    s.wb != s.bb && !decide (KingAttacks s.wk s.bk) && s.wb.color != s.bb.color &&
    !s.inCheckB s.toMove.other

/-- Geometric legality of a move in an `okB` state. -/
def fastLegal (s : KBState) : KBMove → Bool
  | .king d =>
    fastKingStep (s.king s.toMove) d (s.king s.toMove.other) (s.bishop s.toMove.other)
      (s.bishop s.toMove)
  | .bishop d =>
    fastBishopMove (s.bishop s.toMove) d (s.king s.toMove) (s.king s.toMove.other)
      (s.bishop s.toMove.other)

/-- The state after a move. -/
def apply (s : KBState) : KBMove → KBState
  | .king d =>
    match s.toMove with
    | .white => { s with toMove := .black, wk := d }
    | .black => { s with toMove := .white, bk := d }
  | .bishop d =>
    match s.toMove with
    | .white => { s with toMove := .black, wb := d }
    | .black => { s with toMove := .white, bb := d }

/-- The side to move is checkmated: in check, and every king step is onto
the own bishop or onto an attacked square. -/
def mateB (s : KBState) : Bool :=
  let c := s.toMove
  let k := s.king c
  let ob := s.bishop c
  let ek := s.king c.other
  let eb := s.bishop c.other
  kingAttackedAt k ek eb && (kingNeighbors k).all fun d => d == ob || kingAttackedAt d ek eb

/-- The chess position of the state. -/
def toPosition (s : KBState) : Position where
  board := Board.kingsBishopsBoard s.wk s.bk s.wb s.bb
  toMove := s.toMove
  castling := ∅
  enPassant := none

/-- The chess move of a state move. -/
def move (s : KBState) : KBMove → Move
  | .king d => Move.std (s.king s.toMove) d
  | .bishop d => Move.std (s.bishop s.toMove) d

/-! ### Potential -/

/-- Mirror files so that the white bishop is on the `a1–h8` color. -/
def mir (s : KBState) : Bool := s.wb.color == .white

/-- The mirroring for the bishop `ob` of the side to move `c`. -/
def mirOf (c : Color) (ob : Square) : Bool :=
  match c with
  | .white => ob.color == .white
  | .black => ob.color == .black

/-- Frame file. -/
def fx (m : Bool) (q : Square) : Nat := if m then 7 - q.file.val else q.file.val

/-- Frame rank. -/
def fy (q : Square) : Nat := q.rank.val

/-- Chebyshev distance. -/
def cheb (x y x' y' : Nat) : Nat := max (dist x x') (dist y y')

/-- Frame square of the `a1–h8` color. -/
def darkF (x y : Nat) : Bool := (x + y) % 2 == 0

/-- Weighted route length for the black king to `(7,7)` avoiding the neighborhood of
`(5,5)`, indexed by `x * 8 + y` in frame coordinates. -/
def dbTable : Array Nat :=
  #[44, 40, 36, 32, 32, 32, 32, 32, 40, 40, 36, 32, 28, 28, 28, 28, 36, 36, 36, 32, 28, 24, 24,
    24, 32, 32, 32, 32, 28, 24, 20, 20, 32, 28, 28, 28, 40, 40, 40, 16, 32, 28, 24, 24, 40, 40,
    40, 10, 32, 28, 24, 20, 40, 40, 40, 6, 32, 28, 24, 20, 16, 10, 6, 0]

/-- Penalty keeping the white king out of Black's corner. -/
def zoneW (x y : Nat) : Nat :=
  if x == 7 && y == 7 then 4 else if (x == 7 && y == 6) || (x == 6 && y == 7) then 1 else 0

/-- White king distance to `f6`. -/
def baseW (x y : Nat) : Nat := 4 * cheb x y 5 5 + (if darkF x y then 0 else 2) + zoneW x y

/-- Black king distance to `h8`. -/
def baseB (x y : Nat) : Nat :=
  dbTable.getD (x * 8 + y) 0 + (if darkF x y && !(x == 7 && y == 7) then 2 else 0)

/-- Target squares of the white bishop: the long diagonal `a1–e5`. -/
def inD (x y : Nat) : Bool := x == y && x ≤ 4

/-- White bishop distance to its target. -/
def workWB (x y : Nat) : Nat :=
  if inD x y then 0
  else if x + y ≤ 8 then 1
  else if x != y then 2
  else if x == 7 then 4
  else 3

/-- Target squares of the black bishop: `g8` and `h7`. -/
def inT (x y : Nat) : Bool := (x == 6 && y == 7) || (x == 7 && y == 6)

/-- Black bishop distance to its target, given the black king's frame square. -/
def workBB (bkx bky x y : Nat) : Nat :=
  if bkx == 7 && bky == 7 then (if inT x y then 0 else if dist x y == 1 then 1 else 2)
  else (if dist x y == 1 then 0 else 1)

/-- White king potential including a block by the own bishop. -/
def workWK (m : Bool) (wk wb : Square) : Nat :=
  baseW (fx m wk) (fy wk) +
    (if decide (KingAttacks wk wb) && baseW (fx m wb) (fy wb) < baseW (fx m wk) (fy wk)
      then 1 else 0)

/-- Black king potential including a block by the own bishop. -/
def workBK (m : Bool) (bk bb : Square) : Nat :=
  baseB (fx m bk) (fy bk) +
    (if decide (KingAttacks bk bb) && baseB (fx m bb) (fy bb) < baseB (fx m bk) (fy bk)
      then 1 else 0)

/-- Potential of the white pieces. -/
def whitePart (m : Bool) (wk wb : Square) : Nat :=
  workWK m wk wb + workWB (fx m wb) (fy wb)

/-- Potential of the black pieces. -/
def blackPart (m : Bool) (bk bb : Square) : Nat :=
  workBK m bk bb + workBB (fx m bk) (fy bk) (fx m bb) (fy bb)

/-- Mutual block: the white king sits in Black's mating corner while the black king
waits on one of its two entry squares. Black retreats first. -/
def cornerBlock (m : Bool) (wk bk : Square) : Nat :=
  if fx m wk == 7 && fy wk == 7 &&
      ((fx m bk == 7 && fy bk == 5) || (fx m bk == 5 && fy bk == 7)) then 5 else 0

/-- Tempo term: the side to move has finished its own work (its part of the
potential and the corner term vanish). A finished side has no progress
move, so its waiting moves must count as progress. -/
def tempo (c : Color) (w b : Nat) : Nat :=
  match c with
  | .white => if w == 0 then 1 else 0
  | .black => if b == 0 then 1 else 0

/-- The potential without the check bonus: twice the piece terms plus the
tempo term (`w`, `b` are the White and Black terms including the corner
term). -/
def muBase (s : KBState) : Nat :=
  let m := s.mir
  let c := cornerBlock m s.wk s.bk
  let wp := whitePart m s.wk s.wb
  let bp := blackPart m s.bk s.bb
  2 * (wp + bp + c) + tempo s.toMove (wp + c) (bp + c)

/-- The potential: the base plus a bonus for the side to move being in check. -/
def mu (s : KBState) : Nat :=
  s.muBase + (if s.inCheckB s.toMove then 64 else 0)

/-! ### Generic one-ply progress (independent of the enemy bishop) -/

/-- Upper bound on the tempo term of Black after White's move: Black can only
be finished with its king on `h8`. -/
def tempoBoundB (m : Bool) (bk : Square) : Nat :=
  if fx m bk == 7 && fy bk == 7 then 1 else 0

/-- Upper bound on the tempo term of White after Black's move: White can only
be finished with its king on `f6`. -/
def tempoBoundW (m : Bool) (wk : Square) : Nat :=
  if fx m wk == 5 && fy wk == 5 then 1 else 0

/-- A white king step `wk → d` that is legal for every placement of the black
bishop: `d` has the white bishop's color, the black king does not cover it,
the step gives no check, and the potential (whose White-dependent part is
currently `own`; `wbT` is the white bishop's term) drops below `own + bound`. -/
def genericKingStepW (m : Bool) (wk bk wb : Square) (wbT own bound : Nat) (d : Square) : Bool :=
  d.color == wb.color && decide (KingAttacks wk d) && d != bk && d != wb &&
    !decide (KingAttacks bk d) && !kingAttackedAt bk d wb &&
    2 * (workWK m d wb + wbT + cornerBlock m d bk) + tempoBoundB m bk < own + bound

/-- A black king step `bk → d` that is legal for every placement of the white
bishop. -/
def genericKingStepB (m : Bool) (wk bk bb : Square) (own bound : Nat) (d : Square) : Bool :=
  d.color == bb.color && decide (KingAttacks bk d) && d != wk && d != bb &&
    !decide (KingAttacks wk d) && !kingAttackedAt wk d bb &&
    2 * (blackPart m d bb + cornerBlock m wk d) + tempoBoundW m wk < own + bound

/-- A white bishop move `wb → d` that is legal for every placement of the black
bishop: the white king has the white bishop's color (so it is immune to the
black bishop), the move gives no check, and the potential drops below
`own + bound`. -/
def genericBishopMoveW (m : Bool) (wk bk wb : Square) (own bound : Nat) (d : Square) : Bool :=
  wk.color == wb.color && decide (BishopAttacks wb d) && d != wk && d != bk &&
    !diagBetween wb d wk && !diagBetween wb d bk &&
    !(decide (BishopAttacks d bk) && !diagBetween d bk wk) &&
    2 * (whitePart m wk d + cornerBlock m wk bk) + tempoBoundB m bk < own + bound

/-- A black bishop move `bb → d` that is legal for every placement of the white
bishop. -/
def genericBishopMoveB (m : Bool) (wk bk bb : Square) (own bound : Nat) (d : Square) : Bool :=
  bk.color == bb.color && decide (BishopAttacks bb d) && d != bk && d != wk &&
    !diagBetween bb d bk && !diagBetween bb d wk &&
    !(decide (BishopAttacks d wk) && !diagBetween d wk bk) &&
    2 * (blackPart m bk d + cornerBlock m wk bk) + tempoBoundW m wk < own + bound

/-- First generic move of White with king `wk`, bishop `wb`, and enemy king `bk`,
in frame `m`. -/
def genericMoveW (m : Bool) (wk bk wb : Square) (bound : Nat) : Option KBMove :=
  let w := whitePart m wk wb + cornerBlock m wk bk
  let own := 2 * w + (if w == 0 then 1 else 0)
  let wbT := workWB (fx m wb) (fy wb)
  match (kingNeighbors wk).find? (genericKingStepW m wk bk wb wbT own bound) with
  | some d => some (.king d)
  | none =>
    match (bishopDests wb).find? (genericBishopMoveW m wk bk wb own bound) with
    | some d => some (.bishop d)
    | none => none

/-- First generic move of Black with king `bk`, bishop `bb`, and enemy king `wk`,
in frame `m`. -/
def genericMoveB (m : Bool) (wk bk bb : Square) (bound : Nat) : Option KBMove :=
  let b := blackPart m bk bb + cornerBlock m wk bk
  let own := 2 * b + (if b == 0 then 1 else 0)
  match (kingNeighbors bk).find? (genericKingStepB m wk bk bb own bound) with
  | some d => some (.king d)
  | none =>
    match (bishopDests bb).find? (genericBishopMoveB m wk bk bb own bound) with
    | some d => some (.bishop d)
    | none => none

/-- First generic move of `c` with kings `wk`, `bk` and own bishop `ob`, in frame `m`. -/
def genericMoveP (c : Color) (m : Bool) (wk bk ob : Square) (bound : Nat) : Option KBMove :=
  match c with
  | .white => genericMoveW m wk bk ob bound
  | .black => genericMoveB m wk bk ob bound

/-! ### Cheap per-state script -/

/-- The move is legal and leads to a legal state. -/
def oneOk (s : KBState) (m : KBMove) : Bool :=
  s.fastLegal m && (s.apply m).okB

/-- The move is legal and mates or lowers the potential (`x` is the current
potential). -/
def progressMove (s : KBState) (x : Nat) (m : KBMove) : Bool :=
  s.fastLegal m &&
    let s1 := s.apply m
    s1.mateB || s1.mu < x

/-- Score of a move: `0` for mate, otherwise one more than the new potential
without the check bonus (a check may be the only way to make the other side
move). -/
def score (s : KBState) (m : KBMove) : Nat :=
  let s1 := s.apply m
  if s1.mateB then 0 else s1.muBase + 1

/-- The legal move with the smallest score, first wins ties. -/
def bestOf (s : KBState) (ms : List KBMove) : Option KBMove :=
  let best := ms.foldl (init := (none : Option (KBMove × Nat))) fun best m =>
    if s.oneOk m then
      let sc := s.score m
      match best with
      | none => some (m, sc)
      | some (_, bsc) => if sc < bsc then some (m, sc) else best
    else best
  best.map (·.1)

/-- First legal bishop move that does not raise the potential: a waiting move
(or a progress move) of the side to move. -/
def waitMove (s : KBState) : Option KBMove :=
  let x := s.mu
  (bishopDests (s.bishop s.toMove)).findSome? fun d =>
    let m := KBMove.bishop d
    if s.fastLegal m && (s.apply m).mu ≤ x then some m else none

/-- The scripted move. In check: the king step with the best score. Otherwise
the first king step or bishop move that mates or lowers the potential, else a
waiting bishop move, else the legal move with the best score. -/
def scriptMove (s : KBState) : Option KBMove :=
  let k := s.king s.toMove
  let ob := s.bishop s.toMove
  let kingMoves := (kingNeighbors k).map KBMove.king
  if s.inCheckB s.toMove then bestOf s kingMoves
  else
    let x := s.mu
    match (kingNeighbors k).find? fun d => s.progressMove x (.king d) with
    | some d => some (.king d)
    | none =>
      match (bishopDests ob).find? fun d => s.progressMove x (.bishop d) with
      | some d => some (.bishop d)
      | none =>
        match s.waitMove with
        | some m => some m
        | none => bestOf s (kingMoves ++ (bishopDests ob).map KBMove.bishop)

/-- The generic move of the state itself, with the check bonus as bound. -/
def genericMove (s : KBState) : Option KBMove :=
  genericMoveP s.toMove s.mir s.wk s.bk (s.bishop s.toMove)
    (if s.inCheckB s.toMove then 64 else 0)

/-- The state has reached the goal relative to `s0`: it is checkmate, its
potential is below that of `s0`, or its potential is not above that of `s0`
and a generic move lowers it further. -/
def goal (s0 s : KBState) : Bool :=
  let x := s.mu
  let x0 := s0.mu
  s.mateB || x < x0 || (x ≤ x0 && s.genericMove.isSome)

/-- Within `n` plies of scripted play from `s`, the goal relative to `s0` is
reached. Each ply first probes a waiting bishop move (two-ply pattern: the
side to move waits, the other side then has a generic progress move), then
follows the script. Every played move is checked with `oneOk`. -/
def chain (s0 : KBState) : KBState → Nat → Bool
  | _, 0 => false
  | s, n + 1 =>
    (match s.waitMove with
      | some m => s.oneOk m && goal s0 (s.apply m)
      | none => false) ||
    match s.scriptMove with
    | none => false
    | some m =>
      s.oneOk m &&
      let s1 := s.apply m
      (goal s0 s1 || chain s0 s1 n)

/-- Plies of scripted play allowed to lower the potential. -/
def window : Nat := 6

/-- A residual state passes: it is checkmate or the script lowers its potential. -/
def checkState (s : KBState) : Bool :=
  s.mateB || chain s s window

/-! ### The exhaustive check -/

/-- The state with `c` to move, own bishop `ob`, and enemy bishop `eb`. -/
def mkState (c : Color) (wk bk ob eb : Square) : KBState :=
  match c with
  | .white => ⟨c, wk, bk, ob, eb⟩
  | .black => ⟨c, wk, bk, eb, ob⟩

/-- A legal state is covered: in check with a generic move of its triple
available (`g64`), or it passes `checkState`. -/
def stateOk (s : KBState) (g64 : Bool) : Bool :=
  !s.okB || (s.inCheckB s.toMove && g64) || s.checkState

/-- Every state of the triple with enemy bishop on the other color is covered. -/
def residualOk (c : Color) (wk bk ob : Square) (g64 : Bool) : Bool :=
  allSquares.all fun eb => eb.color == ob.color || stateOk (mkState c wk bk ob eb) g64

/-- Every legal state with `c` to move, kings `wk`, `bk`, and own bishop `ob`
is covered: either the triple has a generic move without the check bonus
(then every state of the triple is covered), or each state is examined. -/
def tripleOk (c : Color) (wk bk ob : Square) : Bool :=
  let k := match c with | .white => wk | .black => bk
  let ek := match c with | .white => bk | .black => wk
  let m := mirOf c ob
  wk == bk || decide (KingAttacks wk bk) || wk == ob || bk == ob || kingAttackedAt ek k ob ||
  (genericMoveP c m wk bk ob 0).isSome ||
  residualOk c wk bk ob (genericMoveP c m wk bk ob 64).isSome

/-- Every legal state is covered. -/
def checkAll : Bool :=
  allSquares.all fun wk => allSquares.all fun bk => allSquares.all fun ob =>
    tripleOk .white wk bk ob && tripleOk .black wk bk ob

theorem checkAll_true : checkAll = true := by native_decide

end KBState

end Chess
