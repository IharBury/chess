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

/-- A valid position with exactly four occupied squares, a white
bishop, and a black bishop holds only the two kings and those bishops,
with the kings not adjacent. -/
theorem isKingBishops_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop }) :
    IsKingBishops p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨wb, hwb'⟩ := hwb
  obtain ⟨bb, hbb'⟩ := hbb
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_wb : wk ≠ wb := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hwb')
  have hwk_bb : wk ≠ bb := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hbb')
  have hbk_wb : bk ≠ wb := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hwb')
  have hbk_bb : bk ≠ bb := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hbb')
  have hwb_bb : wb ≠ bb := by
    intro heq
    rw [heq] at hwb'
    cases hwb'.symm.trans hbb'
  have hoccEq : p.board.occupied = {wk, bk, wb, bb} := by
    have hsub : ({wk, bk, wb, bb} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hwb']
      · simp [Board.mem_occupied, h, hbb']
    have hcard : ({wk, bk, wb, bb} : Finset Square).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hwb_bb]
      · simp [hbk_wb, hbk_bb]
      · simp [hwk_bk, hwk_wb, hwk_bb]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsBishopsBoard wk bk wb bb := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsBishopsBoard_whiteKing]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = wb
        · rw [hs, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
          exact hwb'
        · by_cases hs' : s = bb
          · rw [hs', Board.kingsBishopsBoard_blackBishop wk bk wb bb
              hwk_bb hbk_bb hwb_bb]
            exact hbb'
          · have hsocc : s ∉ p.board.occupied := by
              rw [hoccEq]
              simp [hw, hb, hs, hs']
            rw [eq_none_of_not_mem_occupied hsocc,
              Board.kingsBishopsBoard_other wk bk wb bb s hw hb hs hs']
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsBishopsBoard_kingIsAttacked_black wk bk wb bb
          hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsBishopsBoard_kingIsAttacked_white wk bk wb bb
          hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb).mpr
          (Or.inl (kingAttacks_symmetric.mp hk))
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
  have hc : p.castling = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro r hr
    obtain ⟨_, hrook⟩ := hcast r hr
    have hmem : r.rookSquare ∈ p.board.occupied := by
      simp [Board.mem_occupied, hrook]
    rw [hoccEq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hsq | hsq | hsq | hsq
    · rw [hsq, hboard, Board.kingsBishopsBoard_whiteKing] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
        at hrook
      exact some_bishop_ne_rook hrook
    · rw [hsq, hboard,
        Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb] at hrook
      exact some_bishop_ne_rook hrook
  have he : p.enPassant = none := by
    cases hep' : p.enPassant with
    | none => rfl
    | some ep =>
      obtain ⟨_, _, hcap⟩ :=
        (enPassantOk_some p ep hep').mp (by simpa [hep'] using hep)
      obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp hcap
      have hpawn := (hasPawn_eq_true_iff _ _ _).mp hs
      have hmem : s ∈ p.board.occupied := by
        simp [Board.mem_occupied, hpawn]
      rw [hoccEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsq | hsq | hsq | hsq
      · rw [hsq, hboard, Board.kingsBishopsBoard_whiteKing] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
          at hpawn
        cases some_bishop_ne_pawn hpawn
      · rw [hsq, hboard,
          Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb]
          at hpawn
        cases some_bishop_ne_pawn hpawn
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

/-- Bonus of the potential for the side to move being in check. -/
def checkBonus (s : KBState) : Nat :=
  if s.inCheckB s.toMove then 64 else 0

/-- The potential: the base plus the check bonus. -/
def mu (s : KBState) : Nat :=
  s.muBase + s.checkBonus

/-! ### Generic one-ply progress (independent of the enemy bishop) -/

/-- Upper bound on the tempo term of Black after White's move: Black can only
be finished with its king on `h8`. -/
def tempoBoundB (m : Bool) (bk : Square) : Nat :=
  if fx m bk == 7 && fy bk == 7 then 1 else 0

/-- Upper bound on the tempo term of White after Black's move: White can only
be finished with its king on `f6`. -/
def tempoBoundW (m : Bool) (wk : Square) : Nat :=
  if fx m wk == 5 && fy wk == 5 then 1 else 0

/-- White's share of the potential: twice its part (including the corner
term) plus its tempo term. -/
def ownW (m : Bool) (wk bk wb : Square) : Nat :=
  let w := whitePart m wk wb + cornerBlock m wk bk
  2 * w + (if w == 0 then 1 else 0)

/-- Black's share of the potential: twice its part (including the corner
term) plus its tempo term. -/
def ownB (m : Bool) (wk bk bb : Square) : Nat :=
  let b := blackPart m bk bb + cornerBlock m wk bk
  2 * b + (if b == 0 then 1 else 0)

/-- A white king step `wk → d` that is legal for every placement of the black
bishop: `d` has the white bishop's color, the black king does not cover it,
the step gives no check, and the potential (whose White-dependent part is
currently `own`) drops below `own + bound`. -/
def genericKingStepW (m : Bool) (wk bk wb : Square) (own bound : Nat) (d : Square) : Bool :=
  d.color == wb.color && decide (KingAttacks wk d) && d != bk && d != wb &&
    !decide (KingAttacks bk d) && !kingAttackedAt bk d wb &&
    2 * (whitePart m d wb + cornerBlock m d bk) + tempoBoundB m bk < own + bound

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
  let own := ownW m wk bk wb
  match (kingNeighbors wk).find? (genericKingStepW m wk bk wb own bound) with
  | some d => some (.king d)
  | none =>
    match (bishopDests wb).find? (genericBishopMoveW m wk bk wb own bound) with
    | some d => some (.bishop d)
    | none => none

/-- First generic move of Black with king `bk`, bishop `bb`, and enemy king `wk`,
in frame `m`. -/
def genericMoveB (m : Bool) (wk bk bb : Square) (bound : Nat) : Option KBMove :=
  let own := ownB m wk bk bb
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
  genericMoveP s.toMove s.mir s.wk s.bk (s.bishop s.toMove) s.checkBonus

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

/-- The king of `c` among `wk`, `bk`. -/
def kingOf (c : Color) (wk bk : Square) : Square :=
  match c with
  | .white => wk
  | .black => bk

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
  let m := mirOf c ob
  wk == bk || decide (KingAttacks wk bk) || wk == ob || bk == ob ||
  kingAttackedAt (kingOf c.other wk bk) (kingOf c wk bk) ob ||
  (genericMoveP c m wk bk ob 0).isSome ||
  residualOk c wk bk ob (genericMoveP c m wk bk ob 64).isSome

/-- Every legal state is covered. -/
def checkAll : Bool :=
  allSquares.all fun wk => allSquares.all fun bk => allSquares.all fun ob =>
    tripleOk .white wk bk ob && tripleOk .black wk bk ob

theorem checkAll_true : checkAll = true := by native_decide

/-! ### The mating line

The scripted play behind `checkState`, replayed to produce the actual moves.
Its correctness is not proved in general; the examples below verify concrete
lines with `pathLegal`. -/

/-- The moves of a successful `chain` from `s` relative to `s0`, if any. -/
def chainPath (s0 : KBState) : KBState → Nat → Option (List KBMove)
  | _, 0 => none
  | s, n + 1 =>
    let viaWait : Option (List KBMove) :=
      match s.waitMove with
      | some m => if s.oneOk m && goal s0 (s.apply m) then some [m] else none
      | none => none
    match viaWait with
    | some ms => some ms
    | none =>
      match s.scriptMove with
      | none => none
      | some m =>
        if s.oneOk m then
          let s1 := s.apply m
          if goal s0 s1 then some [m] else (chainPath s0 s1 n).map (m :: ·)
        else none

/-- The state after a sequence of moves. -/
def applyAll (s : KBState) (ms : List KBMove) : KBState :=
  ms.foldl apply s

/-- The mating line in state moves: a generic move when available, otherwise
the scripted chain; `fuel` bounds the number of rounds. -/
def matingLineAux : KBState → Nat → List KBMove
  | _, 0 => []
  | s, fuel + 1 =>
    if s.mateB then []
    else
      match s.genericMove with
      | some m => m :: matingLineAux (s.apply m) fuel
      | none =>
        match chainPath s s window with
        | some ms => ms ++ matingLineAux (s.applyAll ms) fuel
        | none => []

/-- The chess moves of a sequence of state moves. -/
def toMoves : KBState → List KBMove → List Move
  | _, [] => []
  | s, m :: ms => s.move m :: toMoves (s.apply m) ms

/-- The engineered mating line from `s`, as chess moves. Every round lowers
the potential or mates, so `2 * s.mu + 2` rounds suffice. -/
def matingLine (s : KBState) : List Move :=
  s.toMoves (matingLineAux s (2 * s.mu + 2))

/-- The four-piece state of a position whose board holds exactly two kings and
two bishops in a legal opposite-color arrangement, with no castling rights and
no en passant target. -/
def ofPosition? (p : Position) : Option KBState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .white, kind := .bishop }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .bishop }) with
  | some wk, some bk, some wb, some bb =>
    let s : KBState := ⟨p.toMove, wk, bk, wb, bb⟩
    if s.okB && (allSquares.all fun q => p.board q == Board.kingsBishopsBoard wk bk wb bb q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some s
    else none
  | _, _, _, _ => none

/-! ## Soundness -/

open Position

/-! ### Geometry of the computational primitives -/

theorem kingAttacks_ne {s t : Square} (h : KingAttacks s t) : s ≠ t := h.1

theorem bishopAttacks_ne {s t : Square} (h : BishopAttacks s t) : s ≠ t := h.1

theorem diagBetween_eq {s t : Square} (h : BishopAttacks s t) (u : Square) :
    diagBetween s t u = decide (Between s t u) := by
  revert s t u
  native_decide

theorem between_color {s t u : Square} (h : BishopAttacks s t) (hb : Between s t u) :
    u.color = s.color := by
  revert s t u
  native_decide

theorem mem_kingNeighbors {k d : Square} (h : KingAttacks k d) : d ∈ kingNeighbors k := by
  revert k d
  native_decide

theorem castlingSide_none_of_kingAttacks (c : Color) {s t : Square} (h : KingAttacks s t) :
    (Move.std s t).castlingSide? c = none := by
  revert c s t
  native_decide

theorem kingAttackedAt_iff (d ek eb : Square) :
    kingAttackedAt d ek eb = true ↔
      KingAttacks ek d ∨ (BishopAttacks eb d ∧ ¬ Between eb d ek) := by
  unfold kingAttackedAt
  by_cases hb : BishopAttacks eb d
  · rw [diagBetween_eq hb]
    simp [hb]
  · simp [hb]

theorem kingAttackedAt_eq_false (d ek eb : Square) :
    kingAttackedAt d ek eb = false ↔
      ¬ KingAttacks ek d ∧ (BishopAttacks eb d → Between eb d ek) := by
  rw [← Bool.not_eq_true, kingAttackedAt_iff]
  constructor
  · intro h
    exact ⟨fun hk => h (Or.inl hk), fun hb => by_contra fun hn => h (Or.inr ⟨hb, hn⟩)⟩
  · rintro ⟨hk, hb⟩ (h | ⟨h1, h2⟩)
    · exact hk h
    · exact h2 (hb h1)

/-- The bishop of the other square-color never blocks a bishop ray. -/
theorem not_between_of_color_ne {s t u : Square} (h : BishopAttacks s t)
    (hc : s.color ≠ u.color) : ¬ Between s t u :=
  fun hb => hc (between_color h hb).symm

/-! ### The state as a position -/

theorem okB_iff (s : KBState) :
    s.okB = true ↔
      s.wk ≠ s.bk ∧ s.wk ≠ s.wb ∧ s.wk ≠ s.bb ∧ s.bk ≠ s.wb ∧ s.bk ≠ s.bb ∧ s.wb ≠ s.bb ∧
        ¬ KingAttacks s.wk s.bk ∧ s.wb.color ≠ s.bb.color ∧
        s.inCheckB s.toMove.other = false := by
  simp [okB, and_assoc]

/-- Attack on the white king of a `kingsBishopsBoard` with opposite-color
bishops is `kingAttackedAt`. -/
theorem kingIsAttacked_white_eq (wk bk wb bb : Square)
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hcol : wb.color ≠ bb.color) :
    (Board.kingsBishopsBoard wk bk wb bb).kingIsAttacked .white = kingAttackedAt wk bk bb := by
  rw [Bool.eq_iff_iff, Board.kingsBishopsBoard_kingIsAttacked_white wk bk wb bb hwk_bk hwk_wb
    hwk_bb hbk_wb hbk_bb hwb_bb, kingAttackedAt_iff]
  constructor
  · rintro (h | ⟨h1, h2, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, not_between_of_color_ne h1 (Ne.symm hcol)⟩

/-- Attack on the black king of a `kingsBishopsBoard` with opposite-color
bishops is `kingAttackedAt`. -/
theorem kingIsAttacked_black_eq (wk bk wb bb : Square)
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hcol : wb.color ≠ bb.color) :
    (Board.kingsBishopsBoard wk bk wb bb).kingIsAttacked .black = kingAttackedAt bk wk wb := by
  rw [Bool.eq_iff_iff, Board.kingsBishopsBoard_kingIsAttacked_black wk bk wb bb hwk_bk hwk_wb
    hwk_bb hbk_wb hbk_bb hwb_bb, kingAttackedAt_iff]
  constructor
  · rintro (h | ⟨h1, h2, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, not_between_of_color_ne h1 hcol⟩

theorem kingIsAttacked_eq (s : KBState) (hok : s.okB = true) (c : Color) :
    s.toPosition.board.kingIsAttacked c = s.inCheckB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, hcol, _⟩ := (okB_iff s).mp hok
  cases c with
  | white => exact kingIsAttacked_white_eq _ _ _ _ h1 h2 h3 h4 h5 h6 hcol
  | black => exact kingIsAttacked_black_eq _ _ _ _ h1 h2 h3 h4 h5 h6 hcol

theorem fastKingStep_iff (k d ek eb ob : Square) :
    fastKingStep k d ek eb ob = true ↔
      KingAttacks k d ∧ d ≠ ek ∧ d ≠ eb ∧ d ≠ ob ∧ kingAttackedAt d ek eb = false := by
  simp [fastKingStep, and_assoc]

theorem fastBishopMove_iff (b d k ek eb : Square) :
    fastBishopMove b d k ek eb = true ↔
      BishopAttacks b d ∧ d ≠ k ∧ d ≠ ek ∧ d ≠ eb ∧ diagBetween b d k = false ∧
        diagBetween b d ek = false ∧ kingAttackedAt k ek eb = false := by
  simp [fastBishopMove, and_assoc]

/-- Boolean skeleton of a bishop `isLegalMove` check. -/
theorem legal_bishop_move_bool {unused₁ unused₂ : Bool} (att promoNone attacked : Bool)
    (hatt : att = true) (hpromo : promoNone = true) (hsafe : attacked = false) :
    ((if false = true then unused₁
      else if false && unused₂ = true then unused₂
      else att && promoNone) && !attacked) = true := by
  simp [hatt, hpromo, hsafe]

/-- A white king step of an `okB` state is legal and leads to the applied state. -/
theorem play_whiteKing {s : KBState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : fastKingStep s.wk d s.bk s.bb s.wb = true) :
    isLegalMove s.toPosition (Move.std s.wk d) = true ∧
      s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdbk, hdbb, hdwb, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hm
  have hdwk : d ≠ s.wk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.wk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsBishopsBoard s.wk s.bk s.wb s.bb s.wk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsBishopsBoard_whiteKing _ _ _ _
  have hdstNone : s.toPosition.board (Move.std s.wk d).dst = none :=
    Board.kingsBishopsBoard_other _ _ _ _ d hdwk hdbk hdwb hdbb
  have hside : (Move.std s.wk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.wk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.wk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsBishopsBoard d s.bk s.wb s.bb := by
    rw [hba]
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.wk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsBishopsBoard_whiteKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwb hdbb
  have hplay' : s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_king]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.wk d).src (Move.std s.wk d).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.wk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .black, wk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsBishopsBoard d s.bk s.wb s.bb).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq d s.bk s.wb s.bb hdbk hdwb hdbb h4 h5 h6 hcol]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.wk d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.wk d).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

/-- A black king step of an `okB` state is legal and leads to the applied state. -/
theorem play_blackKing {s : KBState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .black)
    (hm : fastKingStep s.bk d s.wk s.wb s.bb = true) :
    isLegalMove s.toPosition (Move.std s.bk d) = true ∧
      s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdwk, hdwb, hdbb, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hm
  have hdbk : d ≠ s.bk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.bk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsBishopsBoard s.wk s.bk s.wb s.bb s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsBishopsBoard_blackKing _ _ _ _ h1
  have hdstNone : s.toPosition.board (Move.std s.bk d).dst = none :=
    Board.kingsBishopsBoard_other _ _ _ _ d hdwk hdbk hdwb hdbb
  have hside : (Move.std s.bk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsBishopsBoard s.wk d s.wb s.bb := by
    rw [hba]
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.bk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsBishopsBoard_blackKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwb hdbb
  have hplay' : s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_king]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.bk d).src (Move.std s.bk d).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.bk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .white, bk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsBishopsBoard s.wk d s.wb s.bb).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk d s.wb s.bb hdwk.symm h2 h3 hdwb hdbb h6 hcol]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.bk d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.bk d).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

/-- A white bishop move of an `okB` state is legal and leads to the applied state. -/
theorem play_whiteBishop {s : KBState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastBishopMove s.wb d s.wk s.bk s.bb = true) :
    isLegalMove s.toPosition (Move.std s.wb d) = true ∧
      s.toPosition.play (Move.std s.wb d) = (s.apply (.bishop d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hba, hdwk, hdbk, hdbb, hnwk, hnbk, hsafe⟩ := (fastBishopMove_iff _ _ _ _ _).mp hm
  have hdwb : d ≠ s.wb := (bishopAttacks_ne hba).symm
  have hdcol : d.color = s.wb.color := (bishopAttacks_same_color hba).symm
  have hsrcP : s.toPosition.board (Move.std s.wb d).src =
      some { color := s.toPosition.toMove, kind := .bishop } := by
    change Board.kingsBishopsBoard s.wk s.bk s.wb s.bb s.wb =
      some { color := s.toMove, kind := .bishop }
    rw [ht]
    exact Board.kingsBishopsBoard_whiteBishop _ _ _ _ h2 h4
  have hdstNone : s.toPosition.board (Move.std s.wb d).dst = none :=
    Board.kingsBishopsBoard_other _ _ _ _ d hdwk hdbk hdwb hdbb
  have hplay := play_of_some s.toPosition (Move.std s.wb d) hsrcP
  have hboard' : s.toPosition.boardAfter (Move.std s.wb d)
      { color := s.toPosition.toMove, kind := .bishop } =
      Board.kingsBishopsBoard s.wk s.bk d s.bb := by
    rw [boardAfter_bishop _ _ rfl]
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.wb d
      { color := s.toMove, kind := .bishop } = _
    rw [ht]
    exact Board.relocate_kingsBishopsBoard_whiteBishop _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwb
      hdbb
  have hplay' : s.toPosition.play (Move.std s.wb d) = (s.apply (.bishop d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_bishop]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.wb d).src (Move.std s.wb d).dst = true := by
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks s.wb d = true
    rw [Board.kingsBishopsBoard_attacks_whiteBishop_iff h2 h4]
    refine ⟨hba, ?_, ?_, not_between_of_color_ne hba hcol⟩
    · rw [diagBetween_eq hba] at hnwk
      exact of_decide_eq_false hnwk
    · rw [diagBetween_eq hba] at hnbk
      exact of_decide_eq_false hnbk
  have hsafe' : (s.toPosition.play (Move.std s.wb d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.bishop d) = { s with toMove := .black, wb := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsBishopsBoard s.wk s.bk d s.bb).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq s.wk s.bk d s.bb h1 hdwk.symm h3 hdbk.symm h5 hdbb
      (hdcol ▸ hcol)]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.wb d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.bishop == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.bishop == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

/-- A black bishop move of an `okB` state is legal and leads to the applied state. -/
theorem play_blackBishop {s : KBState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : fastBishopMove s.bb d s.bk s.wk s.wb = true) :
    isLegalMove s.toPosition (Move.std s.bb d) = true ∧
      s.toPosition.play (Move.std s.bb d) = (s.apply (.bishop d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hba, hdbk, hdwk, hdwb, hnbk, hnwk, hsafe⟩ := (fastBishopMove_iff _ _ _ _ _).mp hm
  have hdbb : d ≠ s.bb := (bishopAttacks_ne hba).symm
  have hdcol : d.color = s.bb.color := (bishopAttacks_same_color hba).symm
  have hsrcP : s.toPosition.board (Move.std s.bb d).src =
      some { color := s.toPosition.toMove, kind := .bishop } := by
    change Board.kingsBishopsBoard s.wk s.bk s.wb s.bb s.bb =
      some { color := s.toMove, kind := .bishop }
    rw [ht]
    exact Board.kingsBishopsBoard_blackBishop _ _ _ _ h3 h5 h6
  have hdstNone : s.toPosition.board (Move.std s.bb d).dst = none :=
    Board.kingsBishopsBoard_other _ _ _ _ d hdwk hdbk hdwb hdbb
  have hplay := play_of_some s.toPosition (Move.std s.bb d) hsrcP
  have hboard' : s.toPosition.boardAfter (Move.std s.bb d)
      { color := s.toPosition.toMove, kind := .bishop } =
      Board.kingsBishopsBoard s.wk s.bk s.wb d := by
    rw [boardAfter_bishop _ _ rfl]
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.bb d
      { color := s.toMove, kind := .bishop } = _
    rw [ht]
    exact Board.relocate_kingsBishopsBoard_blackBishop _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwb
      hdbb
  have hplay' : s.toPosition.play (Move.std s.bb d) = (s.apply (.bishop d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_bishop]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.bb d).src (Move.std s.bb d).dst = true := by
    change (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks s.bb d = true
    rw [Board.kingsBishopsBoard_attacks_blackBishop_iff h3 h5 h6]
    refine ⟨hba, ?_, ?_, not_between_of_color_ne hba hcol.symm⟩
    · rw [diagBetween_eq hba] at hnwk
      exact of_decide_eq_false hnwk
    · rw [diagBetween_eq hba] at hnbk
      exact of_decide_eq_false hnbk
  have hsafe' : (s.toPosition.play (Move.std s.bb d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.bishop d) = { s with toMove := .white, bb := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsBishopsBoard s.wk s.bk s.wb d).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk s.bk s.wb d h1 h2 hdwk.symm h4 hdbk.symm hdwb.symm
      (hdcol ▸ hcol)]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.bb d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.bishop == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.bishop == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

/-- A geometrically legal move of an `okB` state is a legal chess move, and
playing it gives the position of the applied state. -/
theorem fastLegal_sound {s : KBState} {m : KBMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    isLegalMove s.toPosition (s.move m) = true ∧
      s.toPosition.play (s.move m) = (s.apply m).toPosition := by
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht, king, bishop, Color.other] at hm
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.wk d) ▸
        play_whiteKing hok ht hm
    | black =>
      simp only [fastLegal, ht, king, bishop, Color.other] at hm
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.bk d) ▸
        play_blackKing hok ht hm
  | bishop d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht, king, bishop, Color.other] at hm
      exact (by simp [move, ht, bishop] : s.move (.bishop d) = Move.std s.wb d) ▸
        play_whiteBishop hok ht hm
    | black =>
      simp only [fastLegal, ht, king, bishop, Color.other] at hm
      exact (by simp [move, ht, bishop] : s.move (.bishop d) = Move.std s.bb d) ▸
        play_blackBishop hok ht hm

theorem legalMove_of_fastLegal {s : KBState} {m : KBMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) : LegalMove s.toPosition (s.move m) :=
  (fastLegal_sound hok hm).1

theorem play_move_eq {s : KBState} {m : KBMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    s.toPosition.play (s.move m) = (s.apply m).toPosition :=
  (fastLegal_sound hok hm).2

/-! ### Checkmate -/

theorem mateB_iff (s : KBState) :
    s.mateB = true ↔
      kingAttackedAt (s.king s.toMove) (s.king s.toMove.other) (s.bishop s.toMove.other) = true ∧
        ∀ d ∈ kingNeighbors (s.king s.toMove),
          d = s.bishop s.toMove ∨
            kingAttackedAt d (s.king s.toMove.other) (s.bishop s.toMove.other) = true := by
  simp [mateB, List.all_eq_true]

theorem ne_of_kingsBishopsBoard_eq_none {wk bk wb bb s : Square}
    (h : Board.kingsBishopsBoard wk bk wb bb s = none) :
    s ≠ wk ∧ s ≠ bk ∧ s ≠ wb ∧ s ≠ bb := by
  unfold Board.kingsBishopsBoard at h
  split_ifs at h with h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem play_board_of_src {p : Position} {m : Move} {piece : Piece}
    (h : p.board m.src = some piece) : (p.play m).board = p.boardAfter m piece := by
  rw [play_of_some p m h]

/-- In a state with White to move and `mateB`, no move is legal. -/
theorem mateB_white_no_legalMove {s : KBState} (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : s.mateB = true) (m : Move) : ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hchk, hall⟩ := (mateB_iff s).mp hm
  simp only [ht, king, bishop, Color.other] at hchk hall
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    sameColorBishops_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .white = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .white := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsBishopsBoard s.wk s.bk s.wb s.bb m.src = some ⟨.white, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.wk := Board.kingsBishopsBoard_eq_white_king hsrc'
    have hka : KingAttacks s.wk m.dst := by
      have hatt' : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .white = none := ht ▸ hside rfl
    have hboard : (s.toPosition.play m).board =
        (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.wk m.dst
          { color := .white, kind := .king } := by
      rw [play_board_of_src hsrc, boardAfter_king_no_castle _ _ hside' hpromo, hsq]
      rfl
    have hmem := hall m.dst (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hwb | hbb
    · obtain ⟨hdwk, hdbk, hdwb, hdbb⟩ := ne_of_kingsBishopsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsBishopsBoard_whiteKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk
        hdwb hdbb, kingIsAttacked_white_eq _ _ _ _ hdbk hdwb hdbb h4 h5 h6 hcol] at hsafe'
      rcases hmem with hmem | hmem
      · exact hdwb hmem
      · exact Bool.false_ne_true (hsafe'.symm.trans hmem)
    · have this : s.toMove = .black := destOk_toMove_of_dst_whiteBishop rfl h2 h4 hwb hdestOk
      exact Color.other_ne .white (ht.symm.trans this).symm
    · rw [hboard, hbb, Board.relocate_capture_blackBishop_whiteKing _ _ _ _ h1 h2 h3 h4 h5 h6]
        at hsafe'
      have hiff := Board.kingsBishopBoard_kingIsAttacked_white s.bb s.bk s.wb .white h5.symm
        h6.symm h4
      rw [hbb] at hmem
      rcases hmem with hmem | hmem
      · exact h6 hmem.symm
      · rcases (kingAttackedAt_iff _ _ _).mp hmem with hk | ⟨hb, _⟩
        · exact Bool.false_ne_true (hsafe'.symm.trans (hiff.mpr (Or.inl hk)))
        · exact bishopAttacks_ne hb rfl
  · simp only at hk
    subst hk
    have hsq : m.src = s.wb := Board.kingsBishopsBoard_eq_white_bishop hsrc'
    have hatt0 : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks s.wb m.dst = true := by
      have hatt' : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks m.src m.dst = true := hatt
      rwa [hsq] at hatt'
    have hatt' := (Board.kingsBishopsBoard_attacks_whiteBishop_iff h2 h4).mp hatt0
    have hba : BishopAttacks s.wb m.dst := hatt'.1
    have hboard : (s.toPosition.play m).board =
        (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.wb m.dst
          { color := .white, kind := .bishop } := by
      rw [play_board_of_src hsrc, boardAfter_bishop _ _ hpromo, hsq]
      rfl
    rcases hdstOr with hempty | hwb | hbb
    · obtain ⟨hdwk, hdbk, hdwb, hdbb⟩ := ne_of_kingsBishopsBoard_eq_none hempty
      have hdcol : m.dst.color ≠ s.bb.color := (bishopAttacks_same_color hba).symm ▸ hcol
      rw [hboard, Board.relocate_kingsBishopsBoard_whiteBishop _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk
        hdbk hdwb hdbb, kingIsAttacked_white_eq _ _ _ _ h1 hdwk.symm h3 hdbk.symm h5 hdbb hdcol]
        at hsafe'
      exact Bool.false_ne_true (hsafe'.symm.trans hchk)
    · exact bishopAttacks_ne hba hwb.symm
    · exact hcol (hbb ▸ bishopAttacks_same_color hba)

/-- In a state with Black to move and `mateB`, no move is legal. -/
theorem mateB_black_no_legalMove {s : KBState} (hok : s.okB = true) (ht : s.toMove = .black)
    (hm : s.mateB = true) (m : Move) : ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, _⟩ := (okB_iff s).mp hok
  obtain ⟨hchk, hall⟩ := (mateB_iff s).mp hm
  simp only [ht, king, bishop, Color.other] at hchk hall
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    sameColorBishops_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .black := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsBishopsBoard s.wk s.bk s.wb s.bb m.src = some ⟨.black, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.bk := Board.kingsBishopsBoard_eq_black_king hsrc'
    have hka : KingAttacks s.bk m.dst := by
      have hatt' : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .black = none := ht ▸ hside rfl
    have hboard : (s.toPosition.play m).board =
        (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.bk m.dst
          { color := .black, kind := .king } := by
      rw [play_board_of_src hsrc, boardAfter_king_no_castle _ _ hside' hpromo, hsq]
      rfl
    have hmem := hall m.dst (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hwb | hbb
    · obtain ⟨hdwk, hdbk, hdwb, hdbb⟩ := ne_of_kingsBishopsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsBishopsBoard_blackKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk
        hdwb hdbb, kingIsAttacked_black_eq _ _ _ _ hdwk.symm h2 h3 hdwb hdbb h6 hcol] at hsafe'
      rcases hmem with hmem | hmem
      · exact hdbb hmem
      · exact Bool.false_ne_true (hsafe'.symm.trans hmem)
    · rw [hboard, hwb, Board.relocate_capture_whiteBishop_blackKing _ _ _ _ h1 h2 h3 h4 h5 h6]
        at hsafe'
      have hiff := Board.kingsBishopBoard_kingIsAttacked_black s.wk s.wb s.bb .black h2 h3 h6
      rw [hwb] at hmem
      rcases hmem with hmem | hmem
      · exact h6 hmem
      · rcases (kingAttackedAt_iff _ _ _).mp hmem with hk | ⟨hb, _⟩
        · exact Bool.false_ne_true (hsafe'.symm.trans (hiff.mpr (Or.inl hk)))
        · exact bishopAttacks_ne hb rfl
    · have this : s.toMove = .white := destOk_toMove_of_dst_blackBishop rfl h3 h5 h6 hbb hdestOk
      exact Color.other_ne .black (ht.symm.trans this).symm
  · simp only at hk
    subst hk
    have hsq : m.src = s.bb := Board.kingsBishopsBoard_eq_black_bishop hsrc'
    have hatt0 : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks s.bb m.dst = true := by
      have hatt' : (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).attacks m.src m.dst = true := hatt
      rwa [hsq] at hatt'
    have hatt' := (Board.kingsBishopsBoard_attacks_blackBishop_iff h3 h5 h6).mp hatt0
    have hba : BishopAttacks s.bb m.dst := hatt'.1
    have hboard : (s.toPosition.play m).board =
        (Board.kingsBishopsBoard s.wk s.bk s.wb s.bb).relocate s.bb m.dst
          { color := .black, kind := .bishop } := by
      rw [play_board_of_src hsrc, boardAfter_bishop _ _ hpromo, hsq]
      rfl
    rcases hdstOr with hempty | hwb | hbb
    · obtain ⟨hdwk, hdbk, hdwb, hdbb⟩ := ne_of_kingsBishopsBoard_eq_none hempty
      have hdcol : s.wb.color ≠ m.dst.color := (bishopAttacks_same_color hba).symm ▸ hcol
      rw [hboard, Board.relocate_kingsBishopsBoard_blackBishop _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk
        hdbk hdwb hdbb, kingIsAttacked_black_eq _ _ _ _ h1 h2 hdwk.symm h4 hdbk.symm hdwb.symm
        hdcol] at hsafe'
      exact Bool.false_ne_true (hsafe'.symm.trans hchk)
    · exact hcol (hwb ▸ bishopAttacks_same_color hba).symm
    · exact bishopAttacks_ne hba hbb.symm

/-- A `mateB` state of an `okB` state is a checkmate position. -/
theorem inCheckmate_of_mateB {s : KBState} (hok : s.okB = true) (hm : s.mateB = true) :
    InCheckmate s.toPosition := by
  rw [InCheckmate_iff_forall_not_LegalMove]
  refine ⟨?_, ?_⟩
  · change s.toPosition.board.kingIsAttacked s.toPosition.toMove = true
    rw [kingIsAttacked_eq s hok]
    exact ((mateB_iff s).mp hm).1
  · cases ht : s.toMove with
    | white => exact mateB_white_no_legalMove hok ht hm
    | black => exact mateB_black_no_legalMove hok ht hm

/-! ### Generic moves lower the potential -/

theorem tempoBoundB_of_blackPart_eq_zero (m : Bool) (bk bb : Square)
    (h : blackPart m bk bb = 0) : tempoBoundB m bk = 1 := by
  revert m bk bb
  native_decide

theorem tempoBoundW_of_whitePart_eq_zero (m : Bool) (wk wb : Square)
    (h : whitePart m wk wb = 0) : tempoBoundW m wk = 1 := by
  revert m wk wb
  native_decide

theorem tempo_white (w b : Nat) : tempo .white w b = if w == 0 then 1 else 0 := rfl

theorem tempo_black (w b : Nat) : tempo .black w b = if b == 0 then 1 else 0 := rfl

theorem tempo_black_le (m : Bool) (bk bb : Square) (w c : Nat) :
    tempo .black w (blackPart m bk bb + c) ≤ tempoBoundB m bk := by
  rw [tempo_black]
  split_ifs with h
  · have := tempoBoundB_of_blackPart_eq_zero m bk bb (by have := beq_iff_eq.mp h; omega)
    omega
  · exact Nat.zero_le _

theorem tempo_white_le (m : Bool) (wk wb : Square) (c b : Nat) :
    tempo .white (whitePart m wk wb + c) b ≤ tempoBoundW m wk := by
  rw [tempo_white]
  split_ifs with h
  · have := tempoBoundW_of_whitePart_eq_zero m wk wb (by have := beq_iff_eq.mp h; omega)
    omega
  · exact Nat.zero_le _

theorem mu_white (wk bk wb bb : Square) :
    mu ⟨.white, wk, bk, wb, bb⟩ =
      ownW (wb.color == .white) wk bk wb + 2 * blackPart (wb.color == .white) bk bb +
        checkBonus ⟨.white, wk, bk, wb, bb⟩ := by
  simp only [mu, muBase, ownW, tempo_white, mir]
  omega

theorem mu_black (wk bk wb bb : Square) :
    mu ⟨.black, wk, bk, wb, bb⟩ =
      ownB (wb.color == .white) wk bk bb + 2 * whitePart (wb.color == .white) wk wb +
        checkBonus ⟨.black, wk, bk, wb, bb⟩ := by
  simp only [mu, muBase, ownB, tempo_black, mir]
  omega

theorem genericKingStepW_sound {wk bk wb bb d : Square} {m : Bool} {bound : Nat}
    (hm : m = (wb.color == .white))
    (hok : okB ⟨.white, wk, bk, wb, bb⟩ = true)
    (hb : bound ≤ checkBonus ⟨.white, wk, bk, wb, bb⟩)
    (h : genericKingStepW m wk bk wb (ownW m wk bk wb) bound d = true) :
    fastLegal ⟨.white, wk, bk, wb, bb⟩ (.king d) = true ∧ okB ⟨.black, d, bk, wb, bb⟩ = true ∧
      mu ⟨.black, d, bk, wb, bb⟩ < mu ⟨.white, wk, bk, wb, bb⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, hnc⟩ := (okB_iff _).mp hok
  simp only at h1 h2 h3 h4 h5 h6 hna hcol hnc
  simp only [genericKingStepW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff, bne_iff_ne,
    Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨hdcol, hka, hdbk, hdwb, hnk, hnchk, hlt⟩ := h
  have hdbb : d ≠ bb := fun e => hcol (hdcol.symm.trans (congrArg Square.color e))
  have hsafe : kingAttackedAt d bk bb = false := by
    rw [kingAttackedAt_eq_false]
    exact ⟨hnk, fun hb =>
      absurd (bishopAttacks_same_color hb) fun e => hcol (hdcol.symm.trans e.symm)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (fastKingStep_iff _ _ _ _ _).mpr ⟨hka, hdbk, hdbb, hdwb, hsafe⟩
  · rw [okB_iff]
    exact ⟨hdbk, hdwb, hdbb, h4, h5, h6, fun hk => hnk (kingAttacks_symmetric.mp hk), hcol, hsafe⟩
  · have hnc' : inCheckB ⟨.black, d, bk, wb, bb⟩ .black = false := hnchk
    have hmu1 : mu ⟨.black, d, bk, wb, bb⟩ =
        2 * (whitePart m d wb + blackPart m bk bb + cornerBlock m d bk) +
          tempo .black (whitePart m d wb + cornerBlock m d bk)
            (blackPart m bk bb + cornerBlock m d bk) := by
      simp only [mu, checkBonus, muBase, mir, hnc', ← hm]
      simp
    have hmu0 := mu_white wk bk wb bb
    rw [← hm] at hmu0
    have ht := tempo_black_le m bk bb (whitePart m d wb + cornerBlock m d bk) (cornerBlock m d bk)
    omega

theorem genericBishopMoveW_sound {wk bk wb bb d : Square} {m : Bool} {bound : Nat}
    (hm : m = (wb.color == .white))
    (hok : okB ⟨.white, wk, bk, wb, bb⟩ = true)
    (hb : bound ≤ checkBonus ⟨.white, wk, bk, wb, bb⟩)
    (h : genericBishopMoveW m wk bk wb (ownW m wk bk wb) bound d = true) :
    fastLegal ⟨.white, wk, bk, wb, bb⟩ (.bishop d) = true ∧ okB ⟨.black, wk, bk, d, bb⟩ = true ∧
      mu ⟨.black, wk, bk, d, bb⟩ < mu ⟨.white, wk, bk, wb, bb⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, hnc⟩ := (okB_iff _).mp hok
  simp only at h1 h2 h3 h4 h5 h6 hna hcol hnc
  simp only [genericBishopMoveW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff, bne_iff_ne,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false',
    and_assoc] at h
  obtain ⟨hkcol, hba, hdwk, hdbk, hnwk, hnbk, hnchk, hlt⟩ := h
  have hdcol : d.color = wb.color := (bishopAttacks_same_color hba).symm
  have hdbb : d ≠ bb := fun e => hcol (hdcol.symm.trans (congrArg Square.color e))
  have hsafe : kingAttackedAt wk bk bb = false := by
    rw [kingAttackedAt_eq_false]
    exact ⟨fun hk => hna (kingAttacks_symmetric.mp hk), fun hb =>
      absurd (bishopAttacks_same_color hb) fun e => hcol (hkcol.symm.trans e.symm)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (fastBishopMove_iff _ _ _ _ _).mpr ⟨hba, hdwk, hdbk, hdbb, hnwk, hnbk, hsafe⟩
  · rw [okB_iff]
    exact ⟨h1, hdwk.symm, h3, hdbk.symm, h5, hdbb, hna, hdcol ▸ hcol, hsafe⟩
  · have hnc' : inCheckB ⟨.black, wk, bk, d, bb⟩ .black = false := by
      change kingAttackedAt bk wk d = false
      rw [kingAttackedAt_eq_false]
      refine ⟨hna, fun hb => ?_⟩
      rcases hnchk with hnb | hbt
      · exact absurd hb hnb
      · rw [diagBetween_eq hb] at hbt
        exact of_decide_eq_true hbt
    have hmu1 : mu ⟨.black, wk, bk, d, bb⟩ =
        2 * (whitePart m wk d + blackPart m bk bb + cornerBlock m wk bk) +
          tempo .black (whitePart m wk d + cornerBlock m wk bk)
            (blackPart m bk bb + cornerBlock m wk bk) := by
      simp only [mu, checkBonus, muBase, mir, hnc', hdcol, ← hm]
      simp
    have hmu0 := mu_white wk bk wb bb
    rw [← hm] at hmu0
    have ht := tempo_black_le m bk bb (whitePart m wk d + cornerBlock m wk bk)
      (cornerBlock m wk bk)
    omega

theorem genericKingStepB_sound {wk bk wb bb d : Square} {m : Bool} {bound : Nat}
    (hm : m = (wb.color == .white))
    (hok : okB ⟨.black, wk, bk, wb, bb⟩ = true)
    (hb : bound ≤ checkBonus ⟨.black, wk, bk, wb, bb⟩)
    (h : genericKingStepB m wk bk bb (ownB m wk bk bb) bound d = true) :
    fastLegal ⟨.black, wk, bk, wb, bb⟩ (.king d) = true ∧ okB ⟨.white, wk, d, wb, bb⟩ = true ∧
      mu ⟨.white, wk, d, wb, bb⟩ < mu ⟨.black, wk, bk, wb, bb⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, hnc⟩ := (okB_iff _).mp hok
  simp only at h1 h2 h3 h4 h5 h6 hna hcol hnc
  simp only [genericKingStepB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff, bne_iff_ne,
    Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at h
  obtain ⟨hdcol, hka, hdwk, hdbb, hnk, hnchk, hlt⟩ := h
  have hdwb : d ≠ wb := fun e => hcol ((congrArg Square.color e).symm.trans hdcol)
  have hsafe : kingAttackedAt d wk wb = false := by
    rw [kingAttackedAt_eq_false]
    exact ⟨hnk, fun hb =>
      absurd (bishopAttacks_same_color hb) fun e => hcol (e.trans hdcol)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (fastKingStep_iff _ _ _ _ _).mpr ⟨hka, hdwk, hdwb, hdbb, hsafe⟩
  · rw [okB_iff]
    exact ⟨hdwk.symm, h2, h3, hdwb, hdbb, h6, hnk, hcol, hsafe⟩
  · have hnc' : inCheckB ⟨.white, wk, d, wb, bb⟩ .white = false := hnchk
    have hmu1 : mu ⟨.white, wk, d, wb, bb⟩ =
        2 * (whitePart m wk wb + blackPart m d bb + cornerBlock m wk d) +
          tempo .white (whitePart m wk wb + cornerBlock m wk d)
            (blackPart m d bb + cornerBlock m wk d) := by
      simp only [mu, checkBonus, muBase, mir, hnc', ← hm]
      simp
    have hmu0 := mu_black wk bk wb bb
    rw [← hm] at hmu0
    have ht := tempo_white_le m wk wb (cornerBlock m wk d) (blackPart m d bb + cornerBlock m wk d)
    omega

theorem genericBishopMoveB_sound {wk bk wb bb d : Square} {m : Bool} {bound : Nat}
    (hm : m = (wb.color == .white))
    (hok : okB ⟨.black, wk, bk, wb, bb⟩ = true)
    (hb : bound ≤ checkBonus ⟨.black, wk, bk, wb, bb⟩)
    (h : genericBishopMoveB m wk bk bb (ownB m wk bk bb) bound d = true) :
    fastLegal ⟨.black, wk, bk, wb, bb⟩ (.bishop d) = true ∧ okB ⟨.white, wk, bk, wb, d⟩ = true ∧
      mu ⟨.white, wk, bk, wb, d⟩ < mu ⟨.black, wk, bk, wb, bb⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, hnc⟩ := (okB_iff _).mp hok
  simp only at h1 h2 h3 h4 h5 h6 hna hcol hnc
  simp only [genericBishopMoveB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff, bne_iff_ne,
    Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.not_eq_false',
    and_assoc] at h
  obtain ⟨hkcol, hba, hdbk, hdwk, hnbk, hnwk, hnchk, hlt⟩ := h
  have hdcol : d.color = bb.color := (bishopAttacks_same_color hba).symm
  have hdwb : d ≠ wb := fun e => hcol ((congrArg Square.color e).symm.trans hdcol)
  have hsafe : kingAttackedAt bk wk wb = false := by
    rw [kingAttackedAt_eq_false]
    exact ⟨hna, fun hb =>
      absurd (bishopAttacks_same_color hb) fun e => hcol (e.trans hkcol)⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (fastBishopMove_iff _ _ _ _ _).mpr ⟨hba, hdbk, hdwk, hdwb, hnbk, hnwk, hsafe⟩
  · rw [okB_iff]
    exact ⟨h1, h2, hdwk.symm, h4, hdbk.symm, hdwb.symm, hna, hdcol ▸ hcol, hsafe⟩
  · have hnc' : inCheckB ⟨.white, wk, bk, wb, d⟩ .white = false := by
      change kingAttackedAt wk bk d = false
      rw [kingAttackedAt_eq_false]
      refine ⟨fun hk => hna (kingAttacks_symmetric.mp hk), fun hb => ?_⟩
      rcases hnchk with hnb | hbt
      · exact absurd hb hnb
      · rw [diagBetween_eq hb] at hbt
        exact of_decide_eq_true hbt
    have hmu1 : mu ⟨.white, wk, bk, wb, d⟩ =
        2 * (whitePart m wk wb + blackPart m bk d + cornerBlock m wk bk) +
          tempo .white (whitePart m wk wb + cornerBlock m wk bk)
            (blackPart m bk d + cornerBlock m wk bk) := by
      simp only [mu, checkBonus, muBase, mir, hnc', ← hm]
      simp
    have hmu0 := mu_black wk bk wb bb
    rw [← hm] at hmu0
    have ht := tempo_white_le m wk wb (cornerBlock m wk bk) (blackPart m bk d + cornerBlock m wk bk)
    omega

theorem genericMoveW_spec {m : Bool} {wk bk wb : Square} {bound : Nat} {mv : KBMove}
    (h : genericMoveW m wk bk wb bound = some mv) :
    (∃ d, mv = .king d ∧ genericKingStepW m wk bk wb (ownW m wk bk wb) bound d = true) ∨
      (∃ d, mv = .bishop d ∧ genericBishopMoveW m wk bk wb (ownW m wk bk wb) bound d = true) := by
  unfold genericMoveW at h
  simp only at h
  split at h
  · rename_i d hd
    exact Or.inl ⟨d, (Option.some.inj h).symm, List.find?_some hd⟩
  · split at h
    · rename_i d hd
      exact Or.inr ⟨d, (Option.some.inj h).symm, List.find?_some hd⟩
    · cases h

theorem genericMoveB_spec {m : Bool} {wk bk bb : Square} {bound : Nat} {mv : KBMove}
    (h : genericMoveB m wk bk bb bound = some mv) :
    (∃ d, mv = .king d ∧ genericKingStepB m wk bk bb (ownB m wk bk bb) bound d = true) ∨
      (∃ d, mv = .bishop d ∧ genericBishopMoveB m wk bk bb (ownB m wk bk bb) bound d = true) := by
  unfold genericMoveB at h
  simp only at h
  split at h
  · rename_i d hd
    exact Or.inl ⟨d, (Option.some.inj h).symm, List.find?_some hd⟩
  · split at h
    · rename_i d hd
      exact Or.inr ⟨d, (Option.some.inj h).symm, List.find?_some hd⟩
    · cases h

/-- A generic move of an `okB` state (with a bound not above the check bonus)
is legal, leads to an `okB` state, and lowers the potential. -/
theorem genericMoveP_sound {s : KBState} {bound : Nat} {mv : KBMove} (hok : s.okB = true)
    (hb : bound ≤ s.checkBonus)
    (h : genericMoveP s.toMove s.mir s.wk s.bk (s.bishop s.toMove) bound = some mv) :
    s.fastLegal mv = true ∧ (s.apply mv).okB = true ∧ (s.apply mv).mu < s.mu := by
  rcases s with ⟨c, wk, bk, wb, bb⟩
  cases c with
  | white =>
    simp only [genericMoveP, bishop] at h
    rcases genericMoveW_spec h with ⟨d, rfl, hd⟩ | ⟨d, rfl, hd⟩
    · exact genericKingStepW_sound rfl hok hb hd
    · exact genericBishopMoveW_sound rfl hok hb hd
  | black =>
    simp only [genericMoveP, bishop] at h
    rcases genericMoveB_spec h with ⟨d, rfl, hd⟩ | ⟨d, rfl, hd⟩
    · exact genericKingStepB_sound rfl hok hb hd
    · exact genericBishopMoveB_sound rfl hok hb hd

theorem genericMove_sound {s : KBState} {mv : KBMove} (hok : s.okB = true)
    (h : s.genericMove = some mv) :
    s.fastLegal mv = true ∧ (s.apply mv).okB = true ∧ (s.apply mv).mu < s.mu :=
  genericMoveP_sound hok le_rfl h

/-! ### Soundness of the scripted check -/

/-- `s1` is a legal state reachable from `s0` that is checkmate or has a
smaller potential than `s0`. -/
def Progress (s0 s1 : KBState) : Prop :=
  s1.okB = true ∧ Reachable s0.toPosition s1.toPosition ∧ (s1.mateB = true ∨ s1.mu < s0.mu)

theorem reachable_apply {s0 s : KBState} {m : KBMove}
    (hr : Reachable s0.toPosition s.toPosition) (hok : s.okB = true)
    (hm : s.fastLegal m = true) : Reachable s0.toPosition (s.apply m).toPosition := by
  have := Reachable.step (s.move m) hr (legalMove_of_fastLegal hok hm)
  rwa [play_move_eq hok hm] at this

theorem goal_sound {s0 s : KBState} (hok : s.okB = true)
    (hr : Reachable s0.toPosition s.toPosition) (hg : goal s0 s = true) :
    ∃ s1, Progress s0 s1 := by
  simp only [goal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff,
    Option.isSome_iff_exists] at hg
  rcases hg with (hm | hlt) | ⟨hle, mv, hmv⟩
  · exact ⟨s, hok, hr, Or.inl hm⟩
  · exact ⟨s, hok, hr, Or.inr hlt⟩
  · obtain ⟨hfl, hok1, hmu⟩ := genericMove_sound hok hmv
    exact ⟨s.apply mv, hok1, reachable_apply hr hok hfl, Or.inr (lt_of_lt_of_le hmu hle)⟩

theorem oneOk_iff (s : KBState) (m : KBMove) :
    s.oneOk m = true ↔ s.fastLegal m = true ∧ (s.apply m).okB = true := by
  simp [oneOk]

theorem chain_sound {s0 : KBState} :
    ∀ (n : Nat) (s : KBState), s.okB = true → Reachable s0.toPosition s.toPosition →
      chain s0 s n = true → ∃ s1, Progress s0 s1 := by
  intro n
  induction n with
  | zero =>
    intro s _ _ h
    simp [chain] at h
  | succ n ih =>
    intro s hok hr h
    simp only [chain, Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · rename_i m _
        obtain ⟨hone, hg⟩ := Bool.and_eq_true_iff.mp h
        obtain ⟨hfl, hok1⟩ := (oneOk_iff s m).mp hone
        exact goal_sound hok1 (reachable_apply hr hok hfl) hg
      · cases h
    · split at h
      · cases h
      · rename_i m _
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨hone, hrest⟩ := h
        obtain ⟨hfl, hok1⟩ := (oneOk_iff s m).mp hone
        have hr1 := reachable_apply hr hok hfl
        rcases hrest with hg | hc
        · exact goal_sound hok1 hr1 hg
        · exact ih _ hok1 hr1 hc

theorem checkState_sound {s : KBState} (hok : s.okB = true) (h : s.checkState = true) :
    ∃ s1, Progress s s1 := by
  simp only [checkState, Bool.or_eq_true] at h
  rcases h with hm | hc
  · exact ⟨s, hok, Reachable.refl, Or.inl hm⟩
  · exact chain_sound window s hok Reachable.refl hc

theorem mirOf_black {wb bb : Square} (hcol : wb.color ≠ bb.color) :
    (bb.color == Color.black) = (wb.color == Color.white) := by
  generalize wb.color = a at hcol ⊢
  generalize bb.color = b at hcol ⊢
  cases a <;> cases b <;> simp_all

theorem residualOk_sound {s : KBState} (hok : s.okB = true) {g64 : Bool}
    (hg : g64 = true → s.inCheckB s.toMove = true →
      ∃ s1, Progress s s1)
    (h : residualOk s.toMove s.wk s.bk (s.bishop s.toMove) g64 = true)
    (hmk : mkState s.toMove s.wk s.bk (s.bishop s.toMove) (s.bishop s.toMove.other) = s)
    (hcol : (s.bishop s.toMove.other).color ≠ (s.bishop s.toMove).color) :
    ∃ s1, Progress s s1 := by
  simp only [residualOk, List.all_eq_true] at h
  have h' := h (s.bishop s.toMove.other) (mem_allSquares _)
  rw [hmk] at h'
  simp only [Bool.or_eq_true, beq_iff_eq, stateOk, Bool.and_eq_true, Bool.not_eq_true'] at h'
  rcases h' with hc | (hno | ⟨hchk, hg64⟩) | hcs
  · exact absurd hc hcol
  · exact absurd (hno.symm.trans hok) Bool.false_ne_true
  · exact hg hg64 hchk
  · exact checkState_sound hok hcs

theorem tripleOk_sound {s : KBState} (hok : s.okB = true)
    (h : tripleOk s.toMove s.wk s.bk (s.bishop s.toMove) = true) : ∃ s1, Progress s s1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, hna, hcol, hnc⟩ := (okB_iff s).mp hok
  have hgen : ∀ bound, bound ≤ s.checkBonus →
      (genericMoveP s.toMove (mirOf s.toMove (s.bishop s.toMove)) s.wk s.bk (s.bishop s.toMove)
        bound).isSome = true → ∃ s1, Progress s s1 := by
    intro bound hb hsome
    obtain ⟨mv, hmv⟩ := Option.isSome_iff_exists.mp hsome
    have hmir : mirOf s.toMove (s.bishop s.toMove) = s.mir := by
      rcases s with ⟨c, wk, bk, wb, bb⟩
      cases c
      · rfl
      · exact mirOf_black hcol
    rw [hmir] at hmv
    obtain ⟨hfl, hok1, hmu⟩ := genericMoveP_sound hok hb hmv
    exact ⟨s.apply mv, hok1, reachable_apply Reachable.refl hok hfl, Or.inr hmu⟩
  have hmk : mkState s.toMove s.wk s.bk (s.bishop s.toMove) (s.bishop s.toMove.other) = s := by
    rcases s with ⟨c, wk, bk, wb, bb⟩
    cases c <;> rfl
  have hcol' : (s.bishop s.toMove.other).color ≠ (s.bishop s.toMove).color := by
    rcases s with ⟨c, wk, bk, wb, bb⟩
    cases c
    · exact Ne.symm hcol
    · exact hcol
  have hk : ∀ c, kingOf c s.wk s.bk = s.king c := by
    intro c
    cases c <;> rfl
  have hnc' : kingAttackedAt (s.king s.toMove.other) (s.king s.toMove) (s.bishop s.toMove) =
      false := by
    have : s.inCheckB s.toMove.other = kingAttackedAt (s.king s.toMove.other)
        (s.king s.toMove) (s.bishop s.toMove) := by
      simp [inCheckB]
    rwa [this] at hnc
  simp only [tripleOk, hk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_iff, hnc',
    Bool.false_eq_true, or_false] at h
  rcases h with ((((hwb | hka) | hwo) | hbo) | hg0) | hres
  · exact absurd hwb h1
  · exact absurd hka hna
  · rcases s with ⟨c, wk, bk, wb, bb⟩
    cases c
    · exact absurd hwo h2
    · exact absurd hwo h3
  · rcases s with ⟨c, wk, bk, wb, bb⟩
    cases c
    · exact absurd hbo h4
    · exact absurd hbo h5
  · exact hgen 0 (Nat.zero_le _) hg0
  · exact residualOk_sound hok (fun hg hchk => hgen 64 (by simp [checkBonus, hchk]) hg) hres hmk
      hcol'

/-- Every legal state makes progress: the exhaustive check `checkAll`. -/
theorem progress_exists {s : KBState} (hok : s.okB = true) : ∃ s1, Progress s s1 := by
  have hall := checkAll_true
  simp only [checkAll, List.all_eq_true, Bool.and_eq_true] at hall
  obtain ⟨hw, hb⟩ := hall s.wk (mem_allSquares _) s.bk (mem_allSquares _) (s.bishop s.toMove)
    (mem_allSquares _)
  rcases s with ⟨c, wk, bk, wb, bb⟩
  cases c
  · exact tripleOk_sound hok hw
  · exact tripleOk_sound hok hb

/-! ### The main theorem -/

theorem checkmateReachable_of_okB_aux :
    ∀ n (s : KBState), s.okB = true → s.mu = n → CheckmateReachable s.toPosition := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hok hn
    obtain ⟨s1, hok1, hr, hp⟩ := progress_exists hok
    rcases hp with hm | hlt
    · exact ⟨s1.toPosition, hr, inCheckmate_of_mateB hok1 hm⟩
    · obtain ⟨q, hrq, hq⟩ := ih s1.mu (hn ▸ hlt) s1 hok1 rfl
      exact ⟨q, hr.trans hrq, hq⟩

/-- From every legal opposite-color king-and-bishop state, checkmate is reachable. -/
theorem checkmateReachable_of_okB {s : KBState} (hok : s.okB = true) :
    CheckmateReachable s.toPosition :=
  checkmateReachable_of_okB_aux s.mu s hok rfl

end KBState

namespace Position

theorem exists_kbState_of_oppositeColorBishops {p : Position} (hv : Valid p)
    (h : IsOppositeColorBishops p) : ∃ s : KBState, s.okB = true ∧ s.toPosition = p := by
  obtain ⟨wk, bk, wb, bb, h1, h2, h3, h4, h5, h6, hna, hcol, hboard, hc, he⟩ := h
  refine ⟨⟨p.toMove, wk, bk, wb, bb⟩, ?_, ?_⟩
  · rw [KBState.okB_iff]
    refine ⟨h1, h2, h3, h4, h5, h6, hna, hcol, ?_⟩
    have hnc := hv.2.1
    rw [hboard] at hnc
    have key : ∀ c : Color,
        (Board.kingsBishopsBoard wk bk wb bb).kingIsAttacked c.other = false →
          KBState.inCheckB ⟨c, wk, bk, wb, bb⟩ c.other = false := by
      intro c hc'
      cases c
      · rw [Color.other_white, KBState.kingIsAttacked_black_eq wk bk wb bb h1 h2 h3 h4 h5 h6 hcol]
          at hc'
        exact hc'
      · rw [Color.other_black, KBState.kingIsAttacked_white_eq wk bk wb bb h1 h2 h3 h4 h5 h6 hcol]
          at hc'
        exact hc'
    exact key p.toMove hnc
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

/-- Opposite-color bishops: checkmate is reachable from every valid position. -/
theorem IsOppositeColorBishops.checkmateReachable {p : Position} (hv : Valid p)
    (h : IsOppositeColorBishops p) : CheckmateReachable p := by
  obtain ⟨s, hok, rfl⟩ := exists_kbState_of_oppositeColorBishops hv h
  exact KBState.checkmateReachable_of_okB hok

/-- Same-color bishops: checkmate is never reachable. -/
theorem IsSameColorBishops.not_checkmateReachable {p : Position} (h : IsSameColorBishops p) :
    ¬ CheckmateReachable p := by
  rintro ⟨q, hr, hq⟩
  exact not_InCheckmate_of_scb_or_kb_or_tk (h.of_reachable hr) hq

/-- Whether some white bishop and some black bishop stand on opposite square-colors. -/
def oppositeColorBishops (p : Position) : Bool :=
  decide (∃ w ∈ p.board.bishopSquares .white, ∃ b ∈ p.board.bishopSquares .black,
    w.color ≠ b.color)

theorem IsOppositeColorBishops.oppositeColorBishops_eq_true {p : Position}
    (h : IsOppositeColorBishops p) : p.oppositeColorBishops = true := by
  obtain ⟨wk, bk, wb, bb, h1, h2, h3, h4, h5, h6, hna, hcol, hboard, hc, he⟩ := h
  simp only [Position.oppositeColorBishops, decide_eq_true_iff, Board.mem_bishopSquares, hboard]
  exact ⟨wb, Board.kingsBishopsBoard_whiteBishop _ _ _ _ h2 h4, bb,
    Board.kingsBishopsBoard_blackBishop _ _ _ _ h3 h5 h6, hcol⟩

theorem IsKingBishops.oppositeColorBishops_iff {p : Position} (h : IsKingBishops p) :
    p.oppositeColorBishops = true ↔ IsOppositeColorBishops p := by
  refine ⟨fun ho => ?_, IsOppositeColorBishops.oppositeColorBishops_eq_true⟩
  obtain ⟨wk, bk, wb, bb, h1, h2, h3, h4, h5, h6, hna, hboard, hc, he⟩ := h
  simp only [oppositeColorBishops, decide_eq_true_iff, Board.mem_bishopSquares, hboard] at ho
  obtain ⟨w, hw, b, hb, hcol⟩ := ho
  rw [Board.kingsBishopsBoard_eq_white_bishop hw, Board.kingsBishopsBoard_eq_black_bishop hb]
    at hcol
  exact ⟨wk, bk, wb, bb, h1, h2, h3, h4, h5, h6, hna, hcol, hboard, hc, he⟩

/-- In a valid king-and-bishop versus king-and-bishop position, checkmate is
reachable exactly when the bishops stand on opposite square-colors. -/
theorem IsKingBishops.checkmateReachable_iff {p : Position} (hv : Valid p)
    (h : IsKingBishops p) : CheckmateReachable p ↔ p.oppositeColorBishops = true := by
  constructor
  · intro hcr
    rcases h.same_or_opposite with hs | ho
    · exact absurd hcr hs.not_checkmateReachable
    · exact ho.oppositeColorBishops_eq_true
  · intro ho
    exact (h.oppositeColorBishops_iff.mp ho).checkmateReachable hv

/-- Decides whether checkmate is reachable from a valid king-and-bishop versus
king-and-bishop position: exactly when the bishops stand on opposite
square-colors. -/
def kingBishopsCheckmateReachable (p : Position) (hv : Valid p) (h : IsKingBishops p) :
    Decidable (CheckmateReachable p) :=
  decidable_of_iff (p.oppositeColorBishops = true) (h.checkmateReachable_iff hv).symm

/-- Same-color bishops: the position is dead. -/
theorem IsSameColorBishops.deadPosition {p : Position} (h : IsSameColorBishops p) :
    DeadPosition p :=
  (DeadPosition_iff_not_CheckmateReachable p).mpr h.not_checkmateReachable

/-- Opposite-color bishops: the position is not dead. -/
theorem IsOppositeColorBishops.not_deadPosition {p : Position} (hv : Valid p)
    (h : IsOppositeColorBishops p) : ¬ DeadPosition p :=
  not_deadPosition_of_checkmateReachable (h.checkmateReachable hv)

/-- The engineered mating line of a king-and-bishop versus king-and-bishop
position with opposite-color bishops; `[]` for other positions. -/
def kingBishopsMatingLine (p : Position) : List Move :=
  match KBState.ofPosition? p with
  | some s => s.matingLine
  | none => []

/-! ### Example: kings on `e1` and `e8`, bishops on `c1` and `c8` -/

/-- White king on `e1`, black king on `e8`, white bishop on `c1` (dark), black
bishop on `c8` (light), White to move. -/
def kingBishopsStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c1 then some { color := .white, kind := .bishop }
    else if s = Square.c8 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingBishopsStart_isValid : isValid kingBishopsStart = true := by
  native_decide

theorem kingBishopsStart_valid : Valid kingBishopsStart :=
  (isValid_eq_true_iff _).mp kingBishopsStart_isValid

theorem kingBishopsStart_isKingBishops : IsKingBishops kingBishopsStart :=
  isKingBishops_of_valid kingBishopsStart_valid (by native_decide)
    ⟨Square.c1, by native_decide⟩ ⟨Square.c8, by native_decide⟩

theorem kingBishopsStart_oppositeColorBishops :
    kingBishopsStart.oppositeColorBishops = true := by
  native_decide

/-- Checkmate is reachable from the starting example. -/
theorem kingBishopsStart_CheckmateReachable : CheckmateReachable kingBishopsStart :=
  (kingBishopsStart_isKingBishops.checkmateReachable_iff kingBishopsStart_valid).mpr
    kingBishopsStart_oppositeColorBishops

/-- The decision procedure agrees. -/
theorem kingBishopsStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingBishopsStart)
      (kingBishopsCheckmateReachable kingBishopsStart kingBishopsStart_valid
        kingBishopsStart_isKingBishops) = true := by
  native_decide

theorem kingBishopsStart_not_deadPosition : ¬ DeadPosition kingBishopsStart :=
  not_deadPosition_of_checkmateReachable kingBishopsStart_CheckmateReachable

/-- The engineered line is legal ... -/
theorem kingBishopsStart_matingLine_legal :
    pathLegal kingBishopsStart (kingBishopsMatingLine kingBishopsStart) = true := by
  native_decide

/-- ... and ends in checkmate. -/
theorem kingBishopsStart_matingLine_inCheckmate :
    (playSeq kingBishopsStart (kingBishopsMatingLine kingBishopsStart)).inCheckmate = true := by
  native_decide

/-- The concrete line: the white king walks to `f6` while the black bishop
shuttles between `g8` and `h7`, the white bishop reaches the long diagonal,
the black king goes to `h8`, and `Kf6–f7` mates by discovered check. -/
theorem kingBishopsStart_matingLine_eq :
    kingBishopsMatingLine kingBishopsStart =
      [Move.std Square.e1 Square.d2, Move.std Square.c8 Square.e6,
        Move.std Square.d2 Square.c3, Move.std Square.e6 Square.f7,
        Move.std Square.c3 Square.d4, Move.std Square.f7 Square.g8,
        Move.std Square.d4 Square.e5, Move.std Square.g8 Square.h7,
        Move.std Square.e5 Square.f6, Move.std Square.h7 Square.g8,
        Move.std Square.c1 ⟨1, 1⟩, Move.std Square.e8 Square.f8,
        Move.std ⟨1, 1⟩ Square.c3, Move.std Square.g8 Square.h7,
        Move.std Square.c3 Square.d4, Move.std Square.f8 Square.g8,
        Move.std Square.d4 Square.e5, Move.std Square.g8 Square.h8,
        Move.std Square.f6 Square.f7] := by
  native_decide

/-- Checkmate is reachable from the starting example, by its concrete line. -/
theorem kingBishopsStart_CheckmateReachable' : CheckmateReachable kingBishopsStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingBishopsStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingBishopsStart_matingLine_inCheckmate)

/-! ### Example: kings on `e1` and `e8`, bishops on `c1` and `f8` -/

/-- White king on `e1`, black king on `e8`, white bishop on `c1`, black bishop
on `f8` (both dark), White to move. -/
def kingBishopsSame : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c1 then some { color := .white, kind := .bishop }
    else if s = Square.f8 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingBishopsSame_isValid : isValid kingBishopsSame = true := by
  native_decide

theorem kingBishopsSame_valid : Valid kingBishopsSame :=
  (isValid_eq_true_iff _).mp kingBishopsSame_isValid

theorem kingBishopsSame_isKingBishops : IsKingBishops kingBishopsSame :=
  isKingBishops_of_valid kingBishopsSame_valid (by native_decide)
    ⟨Square.c1, by native_decide⟩ ⟨Square.f8, by native_decide⟩

theorem kingBishopsSame_oppositeColorBishops :
    kingBishopsSame.oppositeColorBishops = false := by
  native_decide

/-- Checkmate is not reachable with same-color bishops. -/
theorem kingBishopsSame_not_CheckmateReachable : ¬ CheckmateReachable kingBishopsSame :=
  fun h => Bool.false_ne_true (kingBishopsSame_oppositeColorBishops.symm.trans
    ((kingBishopsSame_isKingBishops.checkmateReachable_iff kingBishopsSame_valid).mp h))

/-- The decision procedure agrees. -/
theorem kingBishopsSame_decide_CheckmateReachable :
    @decide (CheckmateReachable kingBishopsSame)
      (kingBishopsCheckmateReachable kingBishopsSame kingBishopsSame_valid
        kingBishopsSame_isKingBishops) = false := by
  native_decide

theorem kingBishopsSame_deadPosition : DeadPosition kingBishopsSame :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr kingBishopsSame_not_CheckmateReachable

end Position

end Chess
