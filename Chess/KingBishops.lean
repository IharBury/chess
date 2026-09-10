import Chess.SameColorBishops
import Chess.EndsGame

/-!
# King and bishop versus king and bishop

A valid position whose board holds only two kings and two bishops is
the material of king-and-bishop versus king and bishop. Bishops stay on
one square-color, so the two bishops either occupy squares of the same
color or of opposite colors.

Same-color bishops cannot reach checkmate: `IsSameColorBishops` and
the captures that leave king-and-bishop versus king, or two kings, are
already treated in `Chess.SameColorBishops`. Opposite-color bishops can
mate. A typical mate puts the defending king in a corner of the
attacking bishop's square-color, with its own bishop occupying a flight
square of the other color and the attacking king covering the rest.

`kingBishopsCheckmateReachable` decides which case a four-piece
king-and-bishop versus king-and-bishop position is in: it returns
`isTrue` exactly when the two bishops stand on opposite square-colors.
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

theorem isOppositeColorBishops_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hopp : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color ≠ t.color) :
    IsOppositeColorBishops p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hboard, hc, he⟩ := isKingBishops_of_valid hv hocc hwb hbb
  have hcol : wb.color ≠ bb.color := by
    have hwb' : p.board wb = some { color := .white, kind := .bishop } := by
      rw [hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
    have hbb' : p.board bb = some { color := .black, kind := .bishop } := by
      rw [hboard, Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb
        hwb_bb]
    exact hopp hwb' hbb'
  exact ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb, hna,
    hcol, hboard, hc, he⟩

theorem IsKingBishops.same_or_opposite {p : Position} (h : IsKingBishops p) :
    IsSameColorBishops p ∨ IsOppositeColorBishops p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hboard, hc, he⟩ := h
  by_cases hcol : wb.color = bb.color
  · exact Or.inl ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
      hna, hcol, hboard, hc, he⟩
  · exact Or.inr ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
      hna, hcol, hboard, hc, he⟩

theorem IsKingBishops.occupied_card {p : Position} (h : IsKingBishops p) :
    p.board.occupied.card = 4 := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    _, hboard, _, _⟩ := h
  have hocc : p.board.occupied = {wk, bk, wb, bb} := by
    rw [hboard, Board.kingsBishopsBoard_occupied wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb]
  have hcard : ({wk, bk, wb, bb} : Finset Square).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hwb_bb]
    · simp [hbk_wb, hbk_bb]
    · simp [hwk_bk, hwk_wb, hwk_bb]
  rw [hocc, hcard]

/-- Opposite-color white/black bishop pairs on `b`. -/
def oppositeColorBishopPairs (b : Board) : Finset (Square × Square) :=
  (b.bishopSquares .white ×ˢ b.bishopSquares .black).filter
    fun pair => pair.1.color != pair.2.color

/-- Checkmate is reachable from a king-and-bishop versus king-and-bishop
position, as a proposition.

The board must hold exactly four pieces, including a white bishop and a
black bishop. Those bishops stay on one square-color, so checkmate is
reachable (by a helpmate, not necessarily forcible) exactly when they
stand on opposite colors. Same-color bishops cannot mate, even after a
capture reduces the material to king-and-bishop versus king or two
kings. -/
def KingBishopsCheckmateReachable (p : Position) : Prop :=
  p.board.occupied.card = 4 ∧
    ∃ wb bb : Square,
      p.board wb = some { color := .white, kind := .bishop } ∧
        p.board bb = some { color := .black, kind := .bishop } ∧
        wb.color ≠ bb.color

/-- Decide whether checkmate is reachable from a king-and-bishop versus
king-and-bishop position. -/
def kingBishopsCheckmateReachable (p : Position) :
    Decidable (KingBishopsCheckmateReachable p) :=
  if hcard : p.board.occupied.card = 4 then
    if hne : (oppositeColorBishopPairs p.board).Nonempty then
      isTrue <| by
        obtain ⟨⟨wb, bb⟩, hfilt⟩ := hne
        simp only [oppositeColorBishopPairs, Finset.mem_filter, Finset.mem_product,
          Board.mem_bishopSquares] at hfilt
        obtain ⟨⟨hwb, hbb⟩, hcolB⟩ := hfilt
        have hcol : wb.color ≠ bb.color := by
          simpa [bne_iff_ne] using hcolB
        exact ⟨hcard, wb, bb, hwb, hbb, hcol⟩
    else
      isFalse fun h => by
        obtain ⟨_, hrest⟩ := h
        obtain ⟨wb, hrest⟩ := hrest
        obtain ⟨bb, hrest⟩ := hrest
        obtain ⟨hwb, hrest⟩ := hrest
        obtain ⟨hbb, hcol⟩ := hrest
        have : (oppositeColorBishopPairs p.board).Nonempty := by
          refine ⟨⟨wb, bb⟩, ?_⟩
          simp only [oppositeColorBishopPairs, Finset.mem_filter, Finset.mem_product,
            Board.mem_bishopSquares]
          exact ⟨⟨hwb, hbb⟩, by simp [bne_iff_ne, hcol]⟩
        exact hne this
  else
    isFalse fun h => hcard h.1

instance {p : Position} : Decidable (KingBishopsCheckmateReachable p) :=
  kingBishopsCheckmateReachable p

theorem IsOppositeColorBishops.kingBishopsCheckmateReachable
    {p : Position} (h : IsOppositeColorBishops p) :
    KingBishopsCheckmateReachable p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hcol, hboard, hc, he⟩ := h
  have hkb : IsKingBishops p :=
    ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb, hna,
      hboard, hc, he⟩
  refine ⟨hkb.occupied_card, wb, bb, ?_, ?_, hcol⟩
  · rw [hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
  · rw [hboard, Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb
      hwb_bb]

theorem IsSameColorBishops.not_KingBishopsCheckmateReachable
    {p : Position} (h : IsSameColorBishops p) :
    ¬ KingBishopsCheckmateReachable p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    _, hsame, hboard, _, _⟩ := h
  intro ⟨_, wb', bb', hwb', hbb', hcol⟩
  have hwbEq : wb' = wb :=
    Board.kingsBishopsBoard_eq_white_bishop (by rw [← hboard, hwb'])
  have hbbEq : bb' = bb :=
    Board.kingsBishopsBoard_eq_black_bishop (by rw [← hboard, hbb'])
  rw [hwbEq, hbbEq] at hcol
  exact hcol hsame

/-- From same-color bishops, checkmate is not reachable. -/
theorem IsSameColorBishops.not_CheckmateReachable {p : Position}
    (h : IsSameColorBishops p) : ¬ CheckmateReachable p := by
  intro ⟨q, hr, hm⟩
  exact not_InCheckmate_of_scb_or_kb_or_tk (IsSameColorBishops.of_reachable h hr) hm

/-- A same-color king-and-bishop versus king-and-bishop position is dead. -/
theorem deadPosition_of_isSameColorBishops {p : Position}
    (h : IsSameColorBishops p) : DeadPosition p :=
  (DeadPosition_iff_not_CheckmateReachable p).mpr h.not_CheckmateReachable

/-- If the four-piece checker reports that checkmate is not reachable,
then the bishops are on the same square-color (or the material is not
king-and-bishop versus king-and-bishop). -/
theorem not_CheckmateReachable_of_not_KingBishopsCheckmateReachable
    {p : Position} (h : IsKingBishops p)
    (hf : ¬ KingBishopsCheckmateReachable p) :
    ¬ CheckmateReachable p := by
  rcases h.same_or_opposite with hsame | hopp
  · exact hsame.not_CheckmateReachable
  · exact (hf hopp.kingBishopsCheckmateReachable).elim

/-- A valid four-piece king-and-bishop versus king-and-bishop position
has reachable checkmate iff the bishops stand on opposite square-colors. -/
theorem KingBishopsCheckmateReachable_iff_opposite {p : Position}
    (h : IsKingBishops p) :
    KingBishopsCheckmateReachable p ↔ IsOppositeColorBishops p := by
  constructor
  · intro ht
    rcases h.same_or_opposite with hsame | hopp
    · exact (hsame.not_KingBishopsCheckmateReachable ht).elim
    · exact hopp
  · intro hopp
    exact hopp.kingBishopsCheckmateReachable

/-- Same-color bishops: the checker is negative, and checkmate is not
reachable. -/
theorem kingBishops_sameColor_not_checkmateReachable {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color) :
    ¬ KingBishopsCheckmateReachable p ∧ ¬ CheckmateReachable p := by
  have hscb := isSameColorBishops_of_valid hv hocc hwb hbb hsame
  exact ⟨hscb.not_KingBishopsCheckmateReachable, hscb.not_CheckmateReachable⟩

/-- Opposite-color bishops: the checker is affirmative. -/
theorem kingBishops_oppositeColor_KingBishopsCheckmateReachable {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hopp : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color ≠ t.color) :
    KingBishopsCheckmateReachable p :=
  (isOppositeColorBishops_of_valid hv hocc hwb hbb hopp).kingBishopsCheckmateReachable

/-! ### Examples -/

/-- White king `a6`, white bishop `c6`, black king `a8`, black bishop `b8`
(opposite square-colors), Black to move: checkmate.

The bishop on `c6` checks `a8` along the light-square diagonal. The flight
squares `a7` and `b7` are covered by the white king; `b8` is occupied by
Black's own bishop, which cannot block or capture on light squares. -/
def oppositeColorBishopsMate : Position where
  board := fun s =>
    if s = Square.a6 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.c6 then some { color := .white, kind := .bishop }
    else if s = Square.b8 then some { color := .black, kind := .bishop }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem oppositeColorBishopsMate_isValid :
    isValid oppositeColorBishopsMate = true := by
  native_decide

theorem oppositeColorBishopsMate_occupied_card :
    oppositeColorBishopsMate.board.occupied.card = 4 := by
  native_decide

theorem oppositeColorBishopsMate_inCheckmate :
    oppositeColorBishopsMate.inCheckmate = true := by
  native_decide

theorem oppositeColorBishopsMate_InCheckmate :
    InCheckmate oppositeColorBishopsMate :=
  (inCheckmate_eq_true_iff _).mp oppositeColorBishopsMate_inCheckmate

theorem oppositeColorBishopsMate_has_whiteBishop :
    ∃ s, oppositeColorBishopsMate.board s =
      some { color := .white, kind := .bishop } :=
  ⟨Square.c6, by native_decide⟩

theorem oppositeColorBishopsMate_has_blackBishop :
    ∃ s, oppositeColorBishopsMate.board s =
      some { color := .black, kind := .bishop } :=
  ⟨Square.b8, by native_decide⟩

def oppositeColorBishopsMateIsWhiteBishop (s : Square) : Bool :=
  decide (oppositeColorBishopsMate.board s =
    some { color := .white, kind := .bishop })

def oppositeColorBishopsMateIsBlackBishop (s : Square) : Bool :=
  decide (oppositeColorBishopsMate.board s =
    some { color := .black, kind := .bishop })

theorem oppositeColorBishopsMate_whiteBishop_eq {s : Square}
    (h : oppositeColorBishopsMate.board s =
      some { color := .white, kind := .bishop }) :
    s = Square.c6 := by
  have hb : oppositeColorBishopsMateIsWhiteBishop s = true := by
    unfold oppositeColorBishopsMateIsWhiteBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter (fun t => oppositeColorBishopsMateIsWhiteBishop t = true) =
        {Square.c6} := by
    native_decide
  have : s ∈ ({Square.c6} : Finset Square) := by
    have : s ∈ Finset.univ.filter
        (fun t => oppositeColorBishopsMateIsWhiteBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem oppositeColorBishopsMate_blackBishop_eq {s : Square}
    (h : oppositeColorBishopsMate.board s =
      some { color := .black, kind := .bishop }) :
    s = Square.b8 := by
  have hb : oppositeColorBishopsMateIsBlackBishop s = true := by
    unfold oppositeColorBishopsMateIsBlackBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter (fun t => oppositeColorBishopsMateIsBlackBishop t = true) =
        {Square.b8} := by
    native_decide
  have : s ∈ ({Square.b8} : Finset Square) := by
    have : s ∈ Finset.univ.filter
        (fun t => oppositeColorBishopsMateIsBlackBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem oppositeColorBishopsMate_opposite_square_color {s t : Square}
    (hs : oppositeColorBishopsMate.board s =
      some { color := .white, kind := .bishop })
    (ht : oppositeColorBishopsMate.board t =
      some { color := .black, kind := .bishop }) :
    s.color ≠ t.color := by
  rw [oppositeColorBishopsMate_whiteBishop_eq hs,
    oppositeColorBishopsMate_blackBishop_eq ht]
  decide

theorem oppositeColorBishopsMate_kingBishopsCheckmateReachable :
    KingBishopsCheckmateReachable oppositeColorBishopsMate :=
  kingBishops_oppositeColor_KingBishopsCheckmateReachable
    ((isValid_eq_true_iff oppositeColorBishopsMate).mp
      oppositeColorBishopsMate_isValid)
    oppositeColorBishopsMate_occupied_card
    oppositeColorBishopsMate_has_whiteBishop
    oppositeColorBishopsMate_has_blackBishop
    oppositeColorBishopsMate_opposite_square_color

/-- The mating position can reach checkmate (it already is checkmate). -/
theorem oppositeColorBishopsMate_CheckmateReachable :
    CheckmateReachable oppositeColorBishopsMate :=
  checkmateReachable_of_inCheckmate oppositeColorBishopsMate_InCheckmate

theorem oppositeColorBishopsMate_not_deadPosition :
    ¬ DeadPosition oppositeColorBishopsMate :=
  not_deadPosition_of_checkmateReachable
    oppositeColorBishopsMate_CheckmateReachable

/-- The same pieces one bishop-move earlier: White to move plays `a4–c6`
and checkmates. -/
def oppositeColorBishopsBeforeMate : Position where
  board := fun s =>
    if s = Square.a6 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a4 then some { color := .white, kind := .bishop }
    else if s = Square.b8 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem oppositeColorBishopsBeforeMate_isValid :
    isValid oppositeColorBishopsBeforeMate = true := by
  native_decide

theorem oppositeColorBishopsBeforeMate_occupied_card :
    oppositeColorBishopsBeforeMate.board.occupied.card = 4 := by
  native_decide

theorem oppositeColorBishopsBeforeMate_not_inCheckmate :
    oppositeColorBishopsBeforeMate.inCheckmate = false := by
  native_decide

theorem oppositeColorBishopsBeforeMate_a4c6_legal :
    LegalMove oppositeColorBishopsBeforeMate
      (Move.std Square.a4 Square.c6) := by
  native_decide

theorem oppositeColorBishopsBeforeMate_a4c6_inCheckmate :
    InCheckmate
      (oppositeColorBishopsBeforeMate.play (Move.std Square.a4 Square.c6)) := by
  native_decide

theorem oppositeColorBishopsBeforeMate_legalSeq :
    LegalSeq oppositeColorBishopsBeforeMate
      [Move.std Square.a4 Square.c6] :=
  ⟨oppositeColorBishopsBeforeMate_a4c6_legal, trivial⟩

/-- From the position before `Bc6#`, checkmate is reachable in one legal
move. -/
theorem oppositeColorBishopsBeforeMate_CheckmateReachable :
    CheckmateReachable oppositeColorBishopsBeforeMate :=
  checkmateReachable_of_legalSeq oppositeColorBishopsBeforeMate_legalSeq
    oppositeColorBishopsBeforeMate_a4c6_inCheckmate

theorem oppositeColorBishopsBeforeMate_has_whiteBishop :
    ∃ s, oppositeColorBishopsBeforeMate.board s =
      some { color := .white, kind := .bishop } :=
  ⟨Square.a4, by native_decide⟩

theorem oppositeColorBishopsBeforeMate_has_blackBishop :
    ∃ s, oppositeColorBishopsBeforeMate.board s =
      some { color := .black, kind := .bishop } :=
  ⟨Square.b8, by native_decide⟩

def oppositeColorBishopsBeforeMateIsWhiteBishop (s : Square) : Bool :=
  decide (oppositeColorBishopsBeforeMate.board s =
    some { color := .white, kind := .bishop })

def oppositeColorBishopsBeforeMateIsBlackBishop (s : Square) : Bool :=
  decide (oppositeColorBishopsBeforeMate.board s =
    some { color := .black, kind := .bishop })

theorem oppositeColorBishopsBeforeMate_whiteBishop_eq {s : Square}
    (h : oppositeColorBishopsBeforeMate.board s =
      some { color := .white, kind := .bishop }) :
    s = Square.a4 := by
  have hb : oppositeColorBishopsBeforeMateIsWhiteBishop s = true := by
    unfold oppositeColorBishopsBeforeMateIsWhiteBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter
        (fun t => oppositeColorBishopsBeforeMateIsWhiteBishop t = true) =
          {Square.a4} := by
    native_decide
  have : s ∈ ({Square.a4} : Finset Square) := by
    have : s ∈ Finset.univ.filter
        (fun t => oppositeColorBishopsBeforeMateIsWhiteBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem oppositeColorBishopsBeforeMate_blackBishop_eq {s : Square}
    (h : oppositeColorBishopsBeforeMate.board s =
      some { color := .black, kind := .bishop }) :
    s = Square.b8 := by
  have hb : oppositeColorBishopsBeforeMateIsBlackBishop s = true := by
    unfold oppositeColorBishopsBeforeMateIsBlackBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter
        (fun t => oppositeColorBishopsBeforeMateIsBlackBishop t = true) =
          {Square.b8} := by
    native_decide
  have : s ∈ ({Square.b8} : Finset Square) := by
    have : s ∈ Finset.univ.filter
        (fun t => oppositeColorBishopsBeforeMateIsBlackBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem oppositeColorBishopsBeforeMate_opposite_square_color {s t : Square}
    (hs : oppositeColorBishopsBeforeMate.board s =
      some { color := .white, kind := .bishop })
    (ht : oppositeColorBishopsBeforeMate.board t =
      some { color := .black, kind := .bishop }) :
    s.color ≠ t.color := by
  rw [oppositeColorBishopsBeforeMate_whiteBishop_eq hs,
    oppositeColorBishopsBeforeMate_blackBishop_eq ht]
  decide

theorem oppositeColorBishopsBeforeMate_kingBishopsCheckmateReachable :
    KingBishopsCheckmateReachable oppositeColorBishopsBeforeMate :=
  kingBishops_oppositeColor_KingBishopsCheckmateReachable
    ((isValid_eq_true_iff oppositeColorBishopsBeforeMate).mp
      oppositeColorBishopsBeforeMate_isValid)
    oppositeColorBishopsBeforeMate_occupied_card
    oppositeColorBishopsBeforeMate_has_whiteBishop
    oppositeColorBishopsBeforeMate_has_blackBishop
    oppositeColorBishopsBeforeMate_opposite_square_color

theorem oppositeColorBishopsBeforeMate_not_deadPosition :
    ¬ DeadPosition oppositeColorBishopsBeforeMate :=
  not_deadPosition_of_checkmateReachable
    oppositeColorBishopsBeforeMate_CheckmateReachable

/-- Same-color bishops: the checker reports that checkmate is not
reachable. -/
theorem sameColorBishops_not_KingBishopsCheckmateReachable :
    ¬ KingBishopsCheckmateReachable sameColorBishops :=
  (kingBishops_sameColor_not_checkmateReachable
    ((isValid_eq_true_iff sameColorBishops).mp sameColorBishops_isValid)
    sameColorBishops_occupied_card
    sameColorBishops_has_whiteBishop
    sameColorBishops_has_blackBishop
    sameColorBishops_same_square_color).1

theorem sameColorBishops_not_CheckmateReachable :
    ¬ CheckmateReachable sameColorBishops :=
  (kingBishops_sameColor_not_checkmateReachable
    ((isValid_eq_true_iff sameColorBishops).mp sameColorBishops_isValid)
    sameColorBishops_occupied_card
    sameColorBishops_has_whiteBishop
    sameColorBishops_has_blackBishop
    sameColorBishops_same_square_color).2

/-- Two kings alone are not a king-and-bishop versus king-and-bishop
position, so the checker is negative. -/
theorem kingsOnly_not_KingBishopsCheckmateReachable :
    ¬ KingBishopsCheckmateReachable kingsOnly := by
  native_decide

/-- The starting position has 32 pieces, so it is not this material. -/
theorem starting_not_KingBishopsCheckmateReachable :
    ¬ KingBishopsCheckmateReachable starting := by
  native_decide

end Position

end Chess
