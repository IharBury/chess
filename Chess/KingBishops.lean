import Chess.SameColorBishops
import Chess.EndsGame
import Mathlib.Logic.Relation

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

`kingBishopsCheckmateReachable` decides `CheckmateReachable` for a
four-piece king-and-bishop versus king-and-bishop position: whether any
legally reachable position is checkmate. Same-color bishops never mate.
Opposite-color bishops can (a helpmate, not necessarily a forced win).
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

theorem kingsBishopsBoard_bishopSquares_white (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).bishopSquares .white = {wb} := by
  ext s
  simp only [mem_bishopSquares, Finset.mem_singleton]
  constructor
  · intro h
    exact kingsBishopsBoard_eq_white_bishop h
  · intro h
    rw [h, kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]

theorem kingsBishopsBoard_bishopSquares_black (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).bishopSquares .black = {bb} := by
  ext s
  simp only [mem_bishopSquares, Finset.mem_singleton]
  constructor
  · intro h
    exact kingsBishopsBoard_eq_black_bishop h
  · intro h
    rw [h, kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb]

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

/-- A legal move from opposite-color bishops either keeps both bishops
(still on opposite square-colors) or captures a bishop, leaving
king-and-bishop versus king. Opposite-color bishops cannot capture
each other. -/
theorem IsOppositeColorBishops.of_play {p : Position} {m : Move}
    (h : IsOppositeColorBishops p) (hm : LegalMove p m) :
    IsOppositeColorBishops (p.play m) ∨ IsKingAndBishop (p.play m) := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hcol, hboard, hcstl, _hep⟩ := h
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrcP, hcol', hkind, hside⟩ :=
    sameColorBishops_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = wb ∨ m.src = bb :=
    (Board.kingsBishopsBoard_isSome wk bk wb bb m.src).mp (by
      have : (p.board m.src).isSome = true := by simp [hsrcP]
      simpa [hboard] using this)
  have hcast' : (p.play m).castling = ∅ := by
    rw [hplay]
    cases hkind with
    | inl hk =>
      have hpiece : piece = { color := p.toMove, kind := .king } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_king_no_castle p m (c := p.toMove)
        (hside (by simp [hpiece])) hpromo, hcstl]
      exact castlingAfter_empty _
    | inr hb =>
      have hpiece : piece = { color := p.toMove, kind := .bishop } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_bishop p m (c := p.toMove) hpromo, hcstl]
      exact castlingAfter_empty _
  have hep' : (p.play m).enPassant = none := by
    cases hkind with
    | inl hk =>
      have hpiece : piece = { color := p.toMove, kind := .king } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .king }
              (p.boardAfter m { color := p.toMove, kind := .king }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_king _ _ _
    | inr hb =>
      have hpiece : piece = { color := p.toMove, kind := .bishop } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .bishop }
              (p.boardAfter m { color := p.toMove, kind := .bishop }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_bishop _ _ _
  rcases hdstOr with hdstNone | hdstWb | hdstBb
  · -- Empty destination: the four pieces remain.
    have hdstW : m.dst ≠ wk := by
      intro heq
      rw [heq, hboard, Board.kingsBishopsBoard_whiteKing] at hdstNone
      cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk] at hdstNone
      cases hdstNone
    have hdstWB : m.dst ≠ wb := by
      intro heq
      rw [heq, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
        at hdstNone
      cases hdstNone
    have hdstBB : m.dst ≠ bb := by
      intro heq
      rw [heq, hboard,
        Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb]
        at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcWB | hsrcBB
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcW, hboard, Board.kingsBishopsBoard_whiteKing])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsBishopsBoard_whiteKing wk bk wb bb m.dst
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb hdstW hdstB hdstWB hdstBB
      have hboard' : (p.play m).board = Board.kingsBishopsBoard m.dst bk wb bb := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsBishopsBoard m.dst bk wb bb := hrel
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [ht] using hsafe
        have hiff := Board.kingsBishopsBoard_kingIsAttacked_white m.dst bk wb bb
          hdstB hdstWB hdstBB hbk_wb hbk_bb hwb_bb
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨m.dst, bk, wb, bb, hdstB, hdstWB, hdstBB, hbk_wb, hbk_bb, hwb_bb,
        hna', hcol, hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsBishopsBoard_blackKing wk bk wb bb m.dst
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb hdstW hdstB hdstWB hdstBB
      have hboard' : (p.play m).board = Board.kingsBishopsBoard wk m.dst wb bb := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsBishopsBoard wk m.dst wb bb := hrel
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [ht] using hsafe
        have hiff := Board.kingsBishopsBoard_kingIsAttacked_black wk m.dst wb bb
          hdstW.symm hwk_wb hwk_bb hdstWB hdstBB hwb_bb
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨wk, m.dst, wb, bb, hdstW.symm, hwk_wb, hwk_bb, hdstWB,
        hdstBB, hwb_bb, hna', hcol, hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .white, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcWB, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb
            hwk_wb hbk_wb])
      have hba := boardAfter_bishop p m (c := .white) hpromo
      have hrel := Board.relocate_kingsBishopsBoard_whiteBishop wk bk wb bb m.dst
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb hdstW hdstB hdstWB hdstBB
      have hboard' : (p.play m).board = Board.kingsBishopsBoard wk bk m.dst bb := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .bishop } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .bishop } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate wb m.dst
                { color := .white, kind := .bishop } := by
              rw [hboard, hsrcWB]
          _ = Board.kingsBishopsBoard wk bk m.dst bb := hrel
      have hAtt : BishopAttacks wb m.dst := by
        have : (Board.kingsBishopsBoard wk bk wb bb).attacks wb m.dst = true := by
          simpa [hboard, hsrcWB] using hatt
        exact ((Board.kingsBishopsBoard_attacks_whiteBishop_iff (t := m.dst)
          hwk_wb hbk_wb).mp this).1
      have hcol' : m.dst.color ≠ bb.color :=
        mt (fun heq => (bishopAttacks_same_color hAtt).trans heq) hcol
      exact Or.inl ⟨wk, bk, m.dst, bb, hwk_bk, hdstW.symm, hwk_bb, hdstB.symm,
        hbk_bb, hdstBB, hna, hcol', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcBB, hboard,
            Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb])
      have hba := boardAfter_bishop p m (c := .black) hpromo
      have hrel := Board.relocate_kingsBishopsBoard_blackBishop wk bk wb bb m.dst
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb hdstW hdstB hdstWB hdstBB
      have hboard' : (p.play m).board = Board.kingsBishopsBoard wk bk wb m.dst := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .bishop } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .bishop } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate bb m.dst
                { color := .black, kind := .bishop } := by
              rw [hboard, hsrcBB]
          _ = Board.kingsBishopsBoard wk bk wb m.dst := hrel
      have hAtt : BishopAttacks bb m.dst := by
        have : (Board.kingsBishopsBoard wk bk wb bb).attacks bb m.dst = true := by
          simpa [hboard, hsrcBB] using hatt
        exact ((Board.kingsBishopsBoard_attacks_blackBishop_iff (t := m.dst)
          hwk_bb hbk_bb hwb_bb).mp this).1
      have hcol' : wb.color ≠ m.dst.color :=
        fun heq => hcol (heq.trans (bishopAttacks_same_color hAtt).symm)
      exact Or.inl ⟨wk, bk, wb, m.dst, hwk_bk, hwk_wb, hdstW.symm, hbk_wb,
        hdstB.symm, hdstWB.symm, hna, hcol', hboard', hcast', hep'⟩
  · -- Capture on the white bishop's square: only the black king can do this.
    have ht : p.toMove = Color.black :=
      destOk_toMove_of_dst_whiteBishop hboard hwk_wb hbk_wb hdstWb hdestOk
    have hsrcNeWb : m.src ≠ wb := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
        at hsrcP'
      have hpc : Color.white = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      cases hpc
    rcases hsrcEq with hsrcW | hsrcB | hsrcWB | hsrcBB
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcW, hboard, Board.kingsBishopsBoard_whiteKing])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      exact nomatch ht.symm.trans htW
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk])
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_whiteBishop_blackKing wk bk wb bb
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
      have hboard' : (p.play m).board = Board.kingsBishopBoard wk wb bb .black := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate bk wb
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstWb]
          _ = Board.kingsBishopBoard wk wb bb .black := hrel
      have hna' : ¬ KingAttacks wk wb := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [ht] using hsafe
        have hiff := Board.kingsBishopBoard_kingIsAttacked_black wk wb bb .black
          hwk_wb hwk_bb hwb_bb
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inr ⟨wk, wb, bb, Color.black, hwk_wb, hwk_bb, hwb_bb,
        hna', hboard', hcast', hep'⟩
    · exact (hsrcNeWb hsrcWB).elim
    · -- Black bishop cannot capture the white bishop: opposite colors.
      have hpiece : piece = { color := .black, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcBB, hboard,
            Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb])
      have : (Board.kingsBishopsBoard wk bk wb bb).attacks bb wb = true := by
        simpa [hboard, hsrcBB, hdstWb] using hatt
      have hAtt : BishopAttacks bb wb :=
        ((Board.kingsBishopsBoard_attacks_blackBishop_iff (t := wb)
          hwk_bb hbk_bb hwb_bb).mp this).1
      exact (hcol (bishopAttacks_same_color hAtt).symm).elim
  · -- Capture on the black bishop's square: only the white king can do this.
    have ht : p.toMove = Color.white :=
      destOk_toMove_of_dst_blackBishop hboard hwk_bb hbk_bb hwb_bb hdstBb hdestOk
    have hsrcNeBb : m.src ≠ bb := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hboard,
        Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb]
        at hsrcP'
      have hpc : Color.black = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      cases hpc
    rcases hsrcEq with hsrcW | hsrcB | hsrcWB | hsrcBB
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcW, hboard, Board.kingsBishopsBoard_whiteKing])
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_blackBishop_whiteKing wk bk wb bb
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
      have hboard' : (p.play m).board = Board.kingsBishopBoard bb bk wb .white := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate wk bb
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstBb]
          _ = Board.kingsBishopBoard bb bk wb .white := hrel
      have hna' : ¬ KingAttacks bb bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [ht] using hsafe
        have hiff := Board.kingsBishopBoard_kingIsAttacked_white bb bk wb .white
          hbk_bb.symm hwb_bb.symm hbk_wb
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inr ⟨bb, bk, wb, Color.white, hbk_bb.symm, hwb_bb.symm, hbk_wb,
        hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      exact nomatch ht.symm.trans htB
    · have hpiece : piece = { color := .white, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcWB, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb
            hwk_wb hbk_wb])
      have : (Board.kingsBishopsBoard wk bk wb bb).attacks wb bb = true := by
        simpa [hboard, hsrcWB, hdstBb] using hatt
      have hAtt : BishopAttacks wb bb :=
        ((Board.kingsBishopsBoard_attacks_whiteBishop_iff (t := bb)
          hwk_wb hbk_wb).mp this).1
      exact (hcol (bishopAttacks_same_color hAtt)).elim
    · exact (hsrcNeBb hsrcBB).elim

theorem IsKingBishops.of_play {p : Position} {m : Move}
    (h : IsKingBishops p) (hm : LegalMove p m) :
    IsKingBishops (p.play m) ∨ IsKingAndBishop (p.play m) := by
  rcases h.same_or_opposite with hsame | hopp
  · exact (hsame.of_play hm).imp (fun h => h.toKingBishops) id
  · exact (hopp.of_play hm).imp (fun h => h.toKingBishops) id

theorem IsKingBishops.legalMove_promotion_none {p : Position} {m : Move}
    (h : IsKingBishops p) (hm : LegalMove p m) : m.promotion = none := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    _, hboard, hc, _⟩ := h
  exact (sameColorBishops_legalMove_core hboard hc hm).1

theorem IsOppositeColorBishops.of_reachable {p q : Position}
    (h : IsOppositeColorBishops p) (hr : Reachable p q) :
    IsOppositeColorBishops q ∨ IsKingAndBishop q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    rcases ih with hopp | hkb | htk
    · rcases hopp.of_play hleg with hopp' | hkb'
      · exact Or.inl hopp'
      · exact Or.inr (Or.inl hkb')
    · rcases hkb.of_play hleg with hkb' | htk'
      · exact Or.inr (Or.inl hkb')
      · exact Or.inr (Or.inr htk')
    · exact Or.inr (Or.inr (htk.of_play hleg))

theorem IsKingAndBishop.occupied_card {p : Position} (h : IsKingAndBishop p) :
    p.board.occupied.card = 3 := by
  obtain ⟨wk, bk, bs, c, hwk_bk, hwk_bs, hbk_bs, _, hboard, _, _⟩ := h
  have hocc : p.board.occupied = {wk, bk, bs} := by
    rw [hboard, Board.kingsBishopBoard_occupied wk bk bs c hwk_bk hwk_bs hbk_bs]
  have hcard : ({wk, bk, bs} : Finset Square).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hbk_bs]
    · simp [hwk_bk, hwk_bs]
  rw [hocc, hcard]

theorem IsTwoKings.occupied_card {p : Position} (h : IsTwoKings p) :
    p.board.occupied.card = 2 := by
  obtain ⟨wk, bk, hne, _, hboard, _, _⟩ := h
  have hocc : p.board.occupied = {wk, bk} := by
    rw [hboard, Board.kingsBoard_occupied wk bk hne]
  have hcard : ({wk, bk} : Finset Square).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne]
  rw [hocc, hcard]

theorem IsKingAndBishop.not_IsKingBishops {p : Position}
    (h : IsKingAndBishop p) : ¬ IsKingBishops p := by
  intro hkb
  have := hkb.occupied_card
  have := h.occupied_card
  omega

theorem IsTwoKings.not_IsKingBishops {p : Position}
    (h : IsTwoKings p) : ¬ IsKingBishops p := by
  intro hkb
  have := hkb.occupied_card
  have := h.occupied_card
  omega

theorem IsKingBishops.of_reachable {p q : Position}
    (h : IsKingBishops p) (hr : Reachable p q) :
    IsKingBishops q ∨ IsKingAndBishop q ∨ IsTwoKings q := by
  refine Reachable.rec (motive := fun q' _ =>
      IsKingBishops q' ∨ IsKingAndBishop q' ∨ IsTwoKings q') (Or.inl h) ?_ hr
  intro r m _hr hleg ih
  rcases ih with hkb | hkab | htk
  · exact (hkb.of_play hleg).elim (fun h' => Or.inl h')
      (fun h' => Or.inr (Or.inl h'))
  · exact (hkab.of_play hleg).elim (fun h' => Or.inr (Or.inl h'))
      (fun h' => Or.inr (Or.inr h'))
  · exact Or.inr (Or.inr (htk.of_play hleg))

theorem IsKingBishops.of_reachable_of_InCheckmate {p q : Position}
    (hp : IsKingBishops p) (hr : Reachable p q) (hm : InCheckmate q) :
    IsKingBishops q := by
  rcases hp.of_reachable hr with hkb | hkab | htk
  · exact hkb
  · exact (hkab.not_InCheckmate hm).elim
  · exact (htk.not_InCheckmate hm).elim

theorem not_IsKingBishops_of_reduced {p q : Position}
    (h : IsKingAndBishop p ∨ IsTwoKings p) (hr : Reachable p q) :
    ¬ IsKingBishops q := by
  intro hq
  rcases h with hkab | htk
  · rcases hkab.of_reachable hr with hkab' | htk'
    · exact hkab'.not_IsKingBishops hq
    · exact htk'.not_IsKingBishops hq
  · exact (htk.of_reachable hr).not_IsKingBishops hq

theorem IsKingBishops.of_reachable_between {p r q : Position}
    (hp : IsKingBishops p) (hq : IsKingBishops q)
    (hpr : Reachable p r) (hrq : Reachable r q) :
    IsKingBishops r := by
  rcases hp.of_reachable hpr with hrKB | hred
  · exact hrKB
  · exact (not_IsKingBishops_of_reduced hred hrq hq).elim

theorem not_InCheckmate_of_ocb_play_capture {q : Position}
    (h : IsKingAndBishop q ∨ IsTwoKings q) : ¬ InCheckmate q := by
  rcases h with hkb | htk
  · exact hkb.not_InCheckmate
  · exact htk.not_InCheckmate

/-- Canonical listing of the 64 squares, used instead of the
noncomputable `Finset.toList`. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f =>
    (List.finRange 8).map fun r => ⟨f, r⟩

theorem mem_allSquares (x : Square) : x ∈ allSquares := by
  simp only [allSquares, List.mem_flatMap, List.mem_map]
  exact ⟨x.file, List.mem_finRange _, x.rank, List.mem_finRange _, rfl⟩

theorem allSquares_nodup : allSquares.Nodup := by
  native_decide

/-- The unique element of a singleton set of squares, if any. -/
def uniqueSquare (s : Finset Square) : Option Square :=
  match allSquares.filter (fun x => x ∈ s) with
  | [x] => some x
  | _ => none

theorem filter_eq_singleton_of_nodup {α : Type*} [DecidableEq α]
    {l : List α} {x : α} (hnd : l.Nodup) (hx : x ∈ l) :
    l.filter (fun y => y = x) = [x] := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.nodup_cons] at hnd
    obtain ⟨hnotin, hys⟩ := hnd
    simp only [List.filter_cons]
    by_cases hy : y = x
    · subst hy
      have hnil : ys.filter (fun z => z = y) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hz hdec
        exact hnotin ((of_decide_eq_true hdec) ▸ hz)
      simp only [hnil, ↓reduceIte, decide_true]
    · have hxys : x ∈ ys := by
        simp only [List.mem_cons] at hx
        exact hx.resolve_left (Ne.symm hy)
      simp [hy, ih hys hxys]

theorem uniqueSquare_eq_some {s : Finset Square} {x : Square} :
    uniqueSquare s = some x ↔ s = {x} := by
  constructor
  · intro h
    cases hf : allSquares.filter (fun y => y ∈ s) with
    | nil =>
      simp [uniqueSquare, hf] at h
    | cons a as =>
      cases as with
      | nil =>
        simp only [uniqueSquare, hf] at h
        have hax : a = x := by
          simpa using h
        ext y
        constructor
        · intro hy
          have hymem :
              y ∈ allSquares.filter (fun z => z ∈ s) :=
            List.mem_filter.mpr ⟨mem_allSquares y, decide_eq_true hy⟩
          have : y = a := by
            simpa [hf] using hymem
          exact Finset.mem_singleton.mpr (this.trans hax)
        · intro hy
          simp only [Finset.mem_singleton] at hy
          subst hy
          have : a ∈ allSquares.filter (fun z => z ∈ s) := by
            simp [hf]
          have : a ∈ s := of_decide_eq_true (List.mem_filter.mp this).2
          rwa [hax] at this
      | cons _b _bs =>
        simp [uniqueSquare, hf] at h
  · intro hs
    subst hs
    have hfilt : allSquares.filter (fun y => y ∈ ({x} : Finset Square)) = [x] := by
      have hcongr : allSquares.filter (fun y => y ∈ ({x} : Finset Square)) =
          allSquares.filter (fun y => y = x) := by
        apply List.filter_congr
        intro y _
        simp
      rw [hcongr, filter_eq_singleton_of_nodup allSquares_nodup (mem_allSquares x)]
    simp only [uniqueSquare]
    rw [hfilt]

theorem uniqueSquare_singleton (x : Square) : uniqueSquare {x} = some x :=
  uniqueSquare_eq_some.mpr rfl

theorem uniqueSquare_empty : uniqueSquare ∅ = none := by
  have hnil : allSquares.filter (fun y => y ∈ (∅ : Finset Square)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro _ _ hdec
    simp at hdec
  simp only [uniqueSquare]
  rw [hnil]

/-- Four-piece king-and-bishop versus king-and-bishop state, for a
search that does not range over `Finset.univ` of all such states. -/
structure KingBishopsState where
  whiteKing : Square
  blackKing : Square
  whiteBishop : Square
  blackBishop : Square
  toMove : Color
deriving DecidableEq, Repr

namespace KingBishopsState

def toTuple (s : KingBishopsState) :
    Square × Square × Square × Square × Color :=
  (s.whiteKing, s.blackKing, s.whiteBishop, s.blackBishop, s.toMove)

theorem toTuple_injective : Function.Injective toTuple := by
  intro s₁ s₂ h
  cases s₁
  cases s₂
  simp only [toTuple] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem card_le (s : Finset KingBishopsState) : s.card ≤ 33554432 := by
  have himg : (s.image toTuple).card = s.card :=
    Finset.card_image_of_injective s toTuple_injective
  have hle : (s.image toTuple).card ≤
      Fintype.card (Square × Square × Square × Square × Color) :=
    Finset.card_le_univ _
  have hc : Fintype.card (Square × Square × Square × Square × Color) =
      33554432 := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
      Square.card, Color.card]
  rw [← himg]
  exact hle.trans (le_of_eq hc)

def toPosition (s : KingBishopsState) : Position where
  board := Board.kingsBishopsBoard s.whiteKing s.blackKing s.whiteBishop s.blackBishop
  toMove := s.toMove
  castling := ∅
  enPassant := none

end KingBishopsState

/-- Recover the four piece squares from a position, if each side has
exactly one king and one bishop. -/
def ofPosition? (p : Position) : Option KingBishopsState := do
  let wk ← uniqueSquare (p.board.kingSquares .white)
  let bk ← uniqueSquare (p.board.kingSquares .black)
  let wb ← uniqueSquare (p.board.bishopSquares .white)
  let bb ← uniqueSquare (p.board.bishopSquares .black)
  pure { whiteKing := wk, blackKing := bk, whiteBishop := wb,
         blackBishop := bb, toMove := p.toMove }

theorem ofPosition?_eq_some {p : Position} {s : KingBishopsState} :
    ofPosition? p = some s ↔
      uniqueSquare (p.board.kingSquares .white) = some s.whiteKing ∧
        uniqueSquare (p.board.kingSquares .black) = some s.blackKing ∧
        uniqueSquare (p.board.bishopSquares .white) = some s.whiteBishop ∧
        uniqueSquare (p.board.bishopSquares .black) = some s.blackBishop ∧
        s.toMove = p.toMove := by
  constructor
  · intro h
    simp only [ofPosition?] at h
    cases hwk : uniqueSquare (p.board.kingSquares .white) with
    | none => simp [hwk] at h
    | some wk =>
      cases hbk : uniqueSquare (p.board.kingSquares .black) with
      | none => simp [hwk, hbk] at h
      | some bk =>
        cases hwb : uniqueSquare (p.board.bishopSquares .white) with
        | none => simp [hwk, hbk, hwb] at h
        | some wb =>
          cases hbb : uniqueSquare (p.board.bishopSquares .black) with
          | none => simp [hwk, hbk, hwb, hbb] at h
          | some bb =>
            simp only [hwk, hbk, hwb, hbb, Option.pure_def] at h
            cases h
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro ⟨hwk, hbk, hwb, hbb, htm⟩
    cases s
    simpa [ofPosition?, hwk, hbk, hwb, hbb] using (htm.symm)

theorem ofPosition?_of_isKingBishops {p : Position} (h : IsKingBishops p) :
    ∃ s, ofPosition? p = some s ∧ s.toPosition = p := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    _hna, hboard, hc, he⟩ := h
  have hwk : uniqueSquare (p.board.kingSquares .white) = some wk := by
    rw [hboard, Board.kingsBishopsBoard_kingSquares_white wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb, uniqueSquare_singleton]
  have hbk : uniqueSquare (p.board.kingSquares .black) = some bk := by
    rw [hboard, Board.kingsBishopsBoard_kingSquares_black wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb, uniqueSquare_singleton]
  have hwb : uniqueSquare (p.board.bishopSquares .white) = some wb := by
    rw [hboard, Board.kingsBishopsBoard_bishopSquares_white wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb, uniqueSquare_singleton]
  have hbb : uniqueSquare (p.board.bishopSquares .black) = some bb := by
    rw [hboard, Board.kingsBishopsBoard_bishopSquares_black wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb, uniqueSquare_singleton]
  refine ⟨{ whiteKing := wk, blackKing := bk, whiteBishop := wb,
            blackBishop := bb, toMove := p.toMove }, ?_, ?_⟩
  · simp [ofPosition?, hwk, hbk, hwb, hbb]
  · apply Position.ext
    · simp [KingBishopsState.toPosition, hboard]
    · rfl
    · simp [KingBishopsState.toPosition, hc]
    · simp [KingBishopsState.toPosition, he]

theorem ofPosition?_isSome_of_isKingBishops {p : Position}
    (h : IsKingBishops p) : ∃ s, ofPosition? p = some s :=
  (ofPosition?_of_isKingBishops h).imp fun _ ⟨hs, _⟩ => hs

theorem ofPosition?_eq_none_of_isKingAndBishop {p : Position}
    (h : IsKingAndBishop p) : ofPosition? p = none := by
  obtain ⟨wk, bk, bs, c, hwk_bk, hwk_bs, hbk_bs, _, hboard, _, _⟩ := h
  cases c with
  | white =>
    have hbb : p.board.bishopSquares .black = ∅ := by
      ext s
      simp only [Board.mem_bishopSquares, Finset.notMem_empty, iff_false]
      intro hb
      rw [hboard] at hb
      unfold Board.kingsBishopBoard at hb
      split_ifs at hb <;> simp_all
    have : uniqueSquare (p.board.bishopSquares .black) = none := by
      rw [hbb, uniqueSquare_empty]
    simp [ofPosition?, this]
  | black =>
    have hwb : p.board.bishopSquares .white = ∅ := by
      ext s
      simp only [Board.mem_bishopSquares, Finset.notMem_empty, iff_false]
      intro hb
      rw [hboard] at hb
      unfold Board.kingsBishopBoard at hb
      split_ifs at hb <;> simp_all
    have : uniqueSquare (p.board.bishopSquares .white) = none := by
      rw [hwb, uniqueSquare_empty]
    simp [ofPosition?, this]

def allPromotions : List (Option PieceKind) :=
  [none, some .queen, some .rook, some .bishop, some .knight]

/-- Canonical listing of moves, used instead of the noncomputable
`Finset.toList`. King-and-bishop legal moves have `promotion = none`. -/
def allMoves : List Move :=
  allSquares.flatMap fun src =>
    allSquares.flatMap fun dst =>
      allPromotions.map fun pr => ⟨src, dst, pr⟩

theorem mem_allMoves_of_promotion_none (m : Move) (h : m.promotion = none) :
    m ∈ allMoves := by
  rcases m with ⟨src, dst, promo⟩
  simp only [allMoves, List.mem_flatMap, List.mem_map]
  refine ⟨src, mem_allSquares _, dst, mem_allSquares _, none, ?_, ?_⟩
  · simp [allPromotions]
  · simp only at h
    subst h
    rfl

/-- Quiet (non-capturing) legal successors that remain four-piece
king-and-bishop versus king-and-bishop. -/
def KingBishopsState.quietSuccessors (s : KingBishopsState) :
    List (Move × KingBishopsState) :=
  allMoves.filterMap fun m =>
    if s.toPosition.isLegalMove m then
      match ofPosition? (s.toPosition.play m) with
      | some t => some (m, t)
      | none => none
    else
      none

theorem mem_quietSuccessors {s : KingBishopsState} {m : Move}
    {t : KingBishopsState} :
    (m, t) ∈ s.quietSuccessors ↔
      m ∈ allMoves ∧ LegalMove s.toPosition m ∧
        ofPosition? (s.toPosition.play m) = some t := by
  simp only [KingBishopsState.quietSuccessors, List.mem_filterMap]
  constructor
  · intro ⟨m', hm', hopt⟩
    by_cases hleg : s.toPosition.isLegalMove m'
    · cases hpos : ofPosition? (s.toPosition.play m') with
      | none => simp [hleg, hpos] at hopt
      | some t' =>
        simp only [hleg, hpos] at hopt
        cases hopt
        exact ⟨hm', hleg, hpos⟩
    · simp [hleg] at hopt
  · intro ⟨hmAll, hm, ht⟩
    refine ⟨m, hmAll, ?_⟩
    simp [show s.toPosition.isLegalMove m = true from hm, ht]

def KingBishopsState.Succ (s t : KingBishopsState) : Prop :=
  ∃ m, (m, t) ∈ s.quietSuccessors

def QuietReachable (s t : KingBishopsState) : Prop :=
  Relation.ReflTransGen KingBishopsState.Succ s t

theorem succ_of_play {s t : KingBishopsState} {m : Move}
    (hs : IsKingBishops s.toPosition) (hm : LegalMove s.toPosition m)
    (ht : ofPosition? (s.toPosition.play m) = some t) :
    KingBishopsState.Succ s t :=
  ⟨m, mem_quietSuccessors.mpr ⟨mem_allMoves_of_promotion_none m
    (hs.legalMove_promotion_none hm), hm, ht⟩⟩

theorem quietReachable_of_reachable {p q : Position} {s t : KingBishopsState}
    (hp : IsKingBishops p) (hq : IsKingBishops q) (hr : Reachable p q)
    (hs : ofPosition? p = some s) (ht : ofPosition? q = some t) :
    QuietReachable s t := by
  have haux : ∀ r : Position, Reachable p r → IsKingBishops r →
      ∃ u, ofPosition? r = some u ∧ QuietReachable s u := by
    intro r hr rKB
    refine Reachable.rec (motive := fun r' hr' =>
        IsKingBishops r' → ∃ u, ofPosition? r' = some u ∧ QuietReachable s u)
      ?_ ?_ hr rKB
    · intro _
      exact ⟨s, hs, Relation.ReflTransGen.refl⟩
    · intro r' m hr' hleg ih hr'playKB
      have hr'KB : IsKingBishops r' :=
        IsKingBishops.of_reachable_between hp hr'playKB hr'
          (Reachable.step m Reachable.refl hleg)
      obtain ⟨u, hu, hquiet⟩ := ih hr'KB
      obtain ⟨u', hu', hueq⟩ := ofPosition?_of_isKingBishops hr'KB
      have : u = u' := Option.some_inj.mp (hu.symm.trans hu')
      subst this
      rcases hr'KB.of_play hleg with hkb' | hkab
      · obtain ⟨v, hv, _⟩ := ofPosition?_of_isKingBishops hkb'
        have hsucc : KingBishopsState.Succ u v := by
          have hm' : LegalMove u.toPosition m := by
            simpa [hueq] using hleg
          have ht' : ofPosition? (u.toPosition.play m) = some v := by
            simpa [hueq] using hv
          exact succ_of_play (by simpa [hueq] using hr'KB) hm' ht'
        exact ⟨v, hv, hquiet.tail hsucc⟩
      · exact (hkab.not_IsKingBishops hr'playKB).elim
  obtain ⟨u, hu, hquiet⟩ := haux q hr hq
  have : u = t := Option.some_inj.mp (hu.symm.trans ht)
  subst this
  exact hquiet

/-- Bound on the number of four-piece states (`64 ^ 4 * 2`). -/
def kingBishopsStateBound : Nat := 33554432

/-- Breadth-first search for a quiet path to checkmate. Stops at the
first mate and never enumerates `Finset.univ` of all states. -/
def kingBishopsSearchGo (visited : Finset KingBishopsState)
    (queue : List (KingBishopsState × List Move)) : Option (List Move) :=
  match queue with
  | [] => none
  | (s, path) :: rest =>
    if s.toPosition.inCheckmate then
      some path
    else
      let nxt := s.quietSuccessors.filter (fun p => !decide (p.2 ∈ visited))
      kingBishopsSearchGo
        (visited ∪ (nxt.map (·.2)).toFinset)
        (rest ++ nxt.map fun p => (p.2, path ++ [p.1]))
termination_by (kingBishopsStateBound - visited.card, queue.length)
decreasing_by
  simp_wf
  by_cases hnil :
      List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors = []
  · simp only [hnil, List.map_nil, List.length_nil, List.toFinset_nil,
      Finset.union_empty]
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    set nxt' := List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors
    have ⟨p, hp⟩ : ∃ p : Move × KingBishopsState, p ∈ nxt' := by
      cases hnxt : nxt' with
      | nil => exact (hnil hnxt).elim
      | cons p _ => exact ⟨p, by simp⟩
    have hp2 : p.2 ∈ (nxt'.map (·.2)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hss : visited ⊂ visited ∪ (nxt'.map (·.2)).toFinset := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · exact Finset.subset_union_left
      · intro heq
        have hin : p.2 ∈ visited := by
          rw [heq]
          exact Finset.mem_union.mpr (Or.inr hp2)
        have hnot : p.2 ∉ visited := by
          have hdec := (List.mem_filter.mp hp).2
          simpa using hdec
        exact hnot hin
    have hlt := Finset.card_lt_card hss
    have hle := KingBishopsState.card_le (visited ∪ (nxt'.map (·.2)).toFinset)
    have hle0 := KingBishopsState.card_le visited
    simp only [kingBishopsStateBound]
    omega

def kingBishopsSearch (p : Position) : Option (List Move) :=
  match ofPosition? p with
  | none => none
  | some s => kingBishopsSearchGo {s} [(s, [])]

theorem kingBishopsSearchGo_sound (origin : Position)
    (visited : Finset KingBishopsState)
    (queue : List (KingBishopsState × List Move))
    (hpath : ∀ pair ∈ queue,
      pathLegal origin pair.2 = true ∧
        playSeq origin pair.2 = pair.1.toPosition)
    (hkb : ∀ pair ∈ queue, IsKingBishops pair.1.toPosition)
    {ms : List Move}
    (hres : kingBishopsSearchGo visited queue = some ms) :
    pathLegal origin ms = true ∧
      (playSeq origin ms).inCheckmate = true := by
  match queue with
  | [] =>
    simp [kingBishopsSearchGo] at hres
  | (s, path) :: rest =>
    simp only [kingBishopsSearchGo] at hres
    split_ifs at hres with hc
    · have hp := hpath (s, path) (by simp)
      injection hres with hms
      subst hms
      exact ⟨hp.1, hp.2 ▸ hc⟩
    · apply kingBishopsSearchGo_sound origin _ _ ?_ ?_ hres
      · intro pair hp
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hpath pair (by simp [hp])
        · simp only [List.mem_map] at hp
          obtain ⟨q, hqnxt, hpair⟩ := hp
          cases hpair
          have hsp := hpath (s, path) (by simp)
          have hqmem := List.mem_filter.mp hqnxt
          have hsucc := mem_quietSuccessors.mp hqmem.1
          have hmleg : LegalMove s.toPosition q.1 := hsucc.2.1
          have hpos : ofPosition? (s.toPosition.play q.1) = some q.2 := hsucc.2.2
          have hsKB : IsKingBishops s.toPosition := hkb (s, path) (by simp)
          rcases hsKB.of_play hmleg with hkb' | hkab
          · obtain ⟨t', ht', heq⟩ := ofPosition?_of_isKingBishops hkb'
            have htq : q.2 = t' := Option.some_inj.mp (hpos.symm.trans ht')
            subst htq
            constructor
            · exact (pathLegal_iff origin _).mpr
                (legalSeq_snoc ((pathLegal_iff origin path).mp hsp.1)
                  (hsp.2 ▸ hmleg))
            · rw [playSeq_snoc, hsp.2, heq]
          · exact (Option.some_ne_none _ (hpos.symm.trans
              (ofPosition?_eq_none_of_isKingAndBishop hkab))).elim
      · intro pair hp
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact hkb pair (by simp [hp])
        · simp only [List.mem_map] at hp
          obtain ⟨q, hqnxt, hpair⟩ := hp
          cases hpair
          have hqmem := List.mem_filter.mp hqnxt
          have hsucc := mem_quietSuccessors.mp hqmem.1
          have hmleg : LegalMove s.toPosition q.1 := hsucc.2.1
          have hpos : ofPosition? (s.toPosition.play q.1) = some q.2 := hsucc.2.2
          have hsKB : IsKingBishops s.toPosition := hkb (s, path) (by simp)
          rcases hsKB.of_play hmleg with hkb' | hkab
          · obtain ⟨t', ht', heq⟩ := ofPosition?_of_isKingBishops hkb'
            have htq : q.2 = t' := Option.some_inj.mp (hpos.symm.trans ht')
            subst htq
            simpa [heq] using hkb'
          · exact (Option.some_ne_none _ (hpos.symm.trans
              (ofPosition?_eq_none_of_isKingAndBishop hkab))).elim
termination_by (kingBishopsStateBound - visited.card, queue.length)
decreasing_by
  simp_wf
  by_cases hnil :
      List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors = []
  · simp only [hnil, List.map_nil, List.length_nil, List.toFinset_nil,
      Finset.union_empty]
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    set nxt' := List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors
    have ⟨p, hp⟩ : ∃ p : Move × KingBishopsState, p ∈ nxt' := by
      cases hnxt : nxt' with
      | nil => exact (hnil hnxt).elim
      | cons p _ => exact ⟨p, by simp⟩
    have hp2 : p.2 ∈ (nxt'.map (·.2)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hss : visited ⊂ visited ∪ (nxt'.map (·.2)).toFinset := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · exact Finset.subset_union_left
      · intro heq
        have hin : p.2 ∈ visited := by
          rw [heq]
          exact Finset.mem_union.mpr (Or.inr hp2)
        have hnot : p.2 ∉ visited := by
          have hdec := (List.mem_filter.mp hp).2
          simpa using hdec
        exact hnot hin
    have hlt := Finset.card_lt_card hss
    have hle := KingBishopsState.card_le (visited ∪ (nxt'.map (·.2)).toFinset)
    have hle0 := KingBishopsState.card_le visited
    simp only [kingBishopsStateBound]
    omega

theorem kingBishopsSearch_sound {p : Position} {ms : List Move}
    (hp : IsKingBishops p) (hres : kingBishopsSearch p = some ms) :
    pathLegal p ms = true ∧ (playSeq p ms).inCheckmate = true := by
  unfold kingBishopsSearch at hres
  obtain ⟨s, hs, heq⟩ := ofPosition?_of_isKingBishops hp
  simp only [hs] at hres
  refine kingBishopsSearchGo_sound p {s} [(s, [])] ?_ ?_ hres
  · intro pair hpair
    simp only [List.mem_singleton] at hpair
    subst hpair
    constructor
    · simp [pathLegal]
    · simp [playSeq, heq]
  · intro pair hpair
    simp only [List.mem_singleton] at hpair
    subst hpair
    simpa [heq] using hp

theorem kingBishopsSearch_checkmateReachable {p : Position} {ms : List Move}
    (hp : IsKingBishops p) (hres : kingBishopsSearch p = some ms) :
    CheckmateReachable p :=
  have h := kingBishopsSearch_sound hp hres
  checkmateReachable_of_legalSeq ((pathLegal_iff p ms).mp h.1)
    ((inCheckmate_eq_true_iff _).mp h.2)

theorem kingBishopsSearchGo_isSome_of_mate_in_queue
    (visited : Finset KingBishopsState)
    (queue : List (KingBishopsState × List Move))
    (h : ∃ pair ∈ queue, pair.1.toPosition.inCheckmate = true) :
    (kingBishopsSearchGo visited queue).isSome := by
  match queue with
  | [] =>
    obtain ⟨_, hmem, _⟩ := h
    simp at hmem
  | (s, path) :: rest =>
    simp only [kingBishopsSearchGo]
    split_ifs with hc
    · simp
    · have h' : ∃ pair ∈ rest ++
          (s.quietSuccessors.filter (fun p => !decide (p.2 ∈ visited))).map
            fun p => (p.2, path ++ [p.1]),
          pair.1.toPosition.inCheckmate = true := by
        obtain ⟨pair, hmem, hmate⟩ := h
        simp only [List.mem_cons] at hmem
        rcases hmem with hpair | hmem
        · subst hpair
          exact (Bool.eq_false_iff.mp (by simpa using hc) hmate).elim
        · exact ⟨pair, List.mem_append.mpr (Or.inl hmem), hmate⟩
      exact kingBishopsSearchGo_isSome_of_mate_in_queue _ _ h'
termination_by (kingBishopsStateBound - visited.card, queue.length)
decreasing_by
  simp_wf
  by_cases hnil :
      List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors = []
  · simp only [hnil, List.map_nil, List.length_nil, List.toFinset_nil,
      Finset.union_empty]
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    set nxt' := List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors
    have ⟨p, hp⟩ : ∃ p : Move × KingBishopsState, p ∈ nxt' := by
      cases hnxt : nxt' with
      | nil => exact (hnil hnxt).elim
      | cons p _ => exact ⟨p, by simp⟩
    have hp2 : p.2 ∈ (nxt'.map (·.2)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hss : visited ⊂ visited ∪ (nxt'.map (·.2)).toFinset := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · exact Finset.subset_union_left
      · intro heq
        have hin : p.2 ∈ visited := by
          rw [heq]
          exact Finset.mem_union.mpr (Or.inr hp2)
        have hnot : p.2 ∉ visited := by
          have hdec := (List.mem_filter.mp hp).2
          simpa using hdec
        exact hnot hin
    have hlt := Finset.card_lt_card hss
    have hle := KingBishopsState.card_le (visited ∪ (nxt'.map (·.2)).toFinset)
    have hle0 := KingBishopsState.card_le visited
    simp only [kingBishopsStateBound]
    omega

theorem succ_mem_visited_union {s u : KingBishopsState}
    {visited : Finset KingBishopsState} (hsucc : KingBishopsState.Succ s u) :
    u ∈ visited ∪
      ((s.quietSuccessors.filter (fun p => !decide (p.2 ∈ visited))).map
        (·.2)).toFinset := by
  by_cases hu : u ∈ visited
  · exact Finset.mem_union.mpr (Or.inl hu)
  · obtain ⟨m, hm⟩ := hsucc
    have hfilt :
        (m, u) ∈ s.quietSuccessors.filter
          (fun p => !decide (p.2 ∈ visited)) :=
      List.mem_filter.mpr ⟨hm, by simp [hu]⟩
    refine Finset.mem_union.mpr (Or.inr ?_)
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨(m, u), hfilt, rfl⟩

/-- If the search returns `none`, every quiet-reachable state has already
been expanded without being checkmate. The invariant is that every
visited state is still queued or closed under quiet successors. -/
theorem kingBishopsSearchGo_eq_none_not_mate
    (origin : KingBishopsState)
    (visited : Finset KingBishopsState)
    (queue : List (KingBishopsState × List Move))
    (horigin : origin ∈ visited)
    (hvis : ∀ s ∈ visited, QuietReachable origin s)
    (hque : ∀ pair ∈ queue, pair.1 ∈ visited)
    (hclosed : ∀ s ∈ visited,
      (∃ path, (s, path) ∈ queue) ∨
        (s.toPosition.inCheckmate = false ∧
          ∀ u, KingBishopsState.Succ s u → u ∈ visited))
    (hres : kingBishopsSearchGo visited queue = none) :
    ∀ t, QuietReachable origin t → t.toPosition.inCheckmate = false := by
  match queue with
  | [] =>
    intro t ht
    have htvis : t ∈ visited := by
      induction ht with
      | refl => exact horigin
      | tail _hreach hsucc ih =>
        have hcl := hclosed _ ih
        rcases hcl with ⟨_, hmem⟩ | ⟨_, hsuccs⟩
        · simp at hmem
        · exact hsuccs _ hsucc
    have hcl := hclosed t htvis
    rcases hcl with ⟨_, hmem⟩ | ⟨hnomate, _⟩
    · simp at hmem
    · exact hnomate
  | (s, path) :: rest =>
    cases hc : s.toPosition.inCheckmate
    · have hres' : kingBishopsSearchGo
          (visited ∪
            ((s.quietSuccessors.filter (fun p => !decide (p.2 ∈ visited))).map
              (·.2)).toFinset)
          (rest ++
            (s.quietSuccessors.filter (fun p => !decide (p.2 ∈ visited))).map
              fun p => (p.2, path ++ [p.1])) = none := by
        simpa [kingBishopsSearchGo, hc] using hres
      apply kingBishopsSearchGo_eq_none_not_mate origin _ _ ?_ ?_ ?_ ?_ hres'
      · exact Finset.mem_union.mpr (Or.inl horigin)
      · intro u hu
        rcases Finset.mem_union.mp hu with hvin | hnxt
        · exact hvis _ hvin
        · simp only [List.mem_toFinset, List.mem_map] at hnxt
          obtain ⟨p, hp, rfl⟩ := hnxt
          have hsucc : KingBishopsState.Succ s p.2 :=
            ⟨p.1, (List.mem_filter.mp hp).1⟩
          have hsvis : s ∈ visited := hque (s, path) (by simp)
          exact (hvis s hsvis).tail hsucc
      · intro pair hp
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact Finset.mem_union.mpr (Or.inl (hque pair (by simp [hp])))
        · simp only [List.mem_map] at hp
          obtain ⟨p, hp, hpair⟩ := hp
          cases hpair
          refine Finset.mem_union.mpr (Or.inr ?_)
          simp only [List.mem_toFinset, List.mem_map]
          exact ⟨p, hp, rfl⟩
      · intro u hu
        rcases Finset.mem_union.mp hu with hvin | hnxt
        · rcases hclosed u hvin with ⟨path', hmemq⟩ | hproc
          · simp only [List.mem_cons] at hmemq
            rcases hmemq with hhead | hrest
            · cases hhead
              by_cases hsin : s ∈ rest.map (fun p => p.1)
              · simp only [List.mem_map] at hsin
                obtain ⟨pair, hpair, hs⟩ := hsin
                cases pair
                simp only at hs
                subst hs
                exact Or.inl ⟨_, List.mem_append.mpr (Or.inl hpair)⟩
              · refine Or.inr ⟨hc, fun v hsucc => succ_mem_visited_union hsucc⟩
            · exact Or.inl ⟨path', List.mem_append.mpr (Or.inl hrest)⟩
          · exact Or.inr ⟨hproc.1, fun v hsucc =>
              Finset.mem_union.mpr (Or.inl (hproc.2 v hsucc))⟩
        · simp only [List.mem_toFinset, List.mem_map] at hnxt
          obtain ⟨p, hp, rfl⟩ := hnxt
          refine Or.inl ⟨path ++ [p.1], List.mem_append.mpr (Or.inr ?_)⟩
          simp only [List.mem_map]
          exact ⟨p, hp, rfl⟩
    · have hsome : kingBishopsSearchGo visited ((s, path) :: rest) = some path := by
        simp [kingBishopsSearchGo, hc]
      nomatch (hsome.symm.trans hres)
termination_by (kingBishopsStateBound - visited.card, queue.length)
decreasing_by
  simp_wf
  by_cases hnil :
      List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors = []
  · simp only [hnil, List.map_nil, List.length_nil, List.toFinset_nil,
      Finset.union_empty]
    apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    set nxt' := List.filter (fun p => !decide (p.2 ∈ visited)) s.quietSuccessors
    have ⟨p, hp⟩ : ∃ p : Move × KingBishopsState, p ∈ nxt' := by
      cases hnxt : nxt' with
      | nil => exact (hnil hnxt).elim
      | cons p _ => exact ⟨p, by simp⟩
    have hp2 : p.2 ∈ (nxt'.map (·.2)).toFinset := by
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have hss : visited ⊂ visited ∪ (nxt'.map (·.2)).toFinset := by
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · exact Finset.subset_union_left
      · intro heq
        have hin : p.2 ∈ visited := by
          rw [heq]
          exact Finset.mem_union.mpr (Or.inr hp2)
        have hnot : p.2 ∉ visited := by
          have hdec := (List.mem_filter.mp hp).2
          simpa using hdec
        exact hnot hin
    have hlt := Finset.card_lt_card hss
    have hle := KingBishopsState.card_le (visited ∪ (nxt'.map (·.2)).toFinset)
    have hle0 := KingBishopsState.card_le visited
    simp only [kingBishopsStateBound]
    omega

theorem kingBishopsSearch_eq_none_not_CheckmateReachable
    {p : Position} (hp : IsKingBishops p)
    (hn : kingBishopsSearch p = none) :
    ¬ CheckmateReachable p := by
  intro ⟨q, hr, hm⟩
  have hq : IsKingBishops q :=
    IsKingBishops.of_reachable_of_InCheckmate hp hr hm
  obtain ⟨s, hs, _hseq⟩ := ofPosition?_of_isKingBishops hp
  obtain ⟨t, ht, hteq⟩ := ofPosition?_of_isKingBishops hq
  have hquiet : QuietReachable s t :=
    quietReachable_of_reachable hp hq hr hs ht
  unfold kingBishopsSearch at hn
  rw [hs] at hn
  have hmate : t.toPosition.inCheckmate = true := by
    rw [hteq]
    exact (inCheckmate_eq_true_iff _).mpr hm
  have hnm : t.toPosition.inCheckmate = false :=
    kingBishopsSearchGo_eq_none_not_mate s {s} [(s, [])]
      (by simp)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst hu
        exact Relation.ReflTransGen.refl)
      (by
        intro pair hpair
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
        cases hpair
        simp)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst hu
        exact Or.inl ⟨[], by simp⟩)
      hn t hquiet
  exact Bool.false_ne_true (hnm.symm.trans hmate)

def oppositeColorBishopPairs (b : Board) : Finset (Square × Square) :=
  (b.bishopSquares .white ×ˢ b.bishopSquares .black).filter
    fun pair => pair.1.color != pair.2.color

theorem oppositeColorBishopPairs_nonempty_of_isOpposite {p : Position}
    (h : IsOppositeColorBishops p) :
    (oppositeColorBishopPairs p.board).Nonempty := by
  obtain ⟨wk, bk, wb, bb, _hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    _hna, hcol, hboard, _, _⟩ := h
  refine ⟨⟨wb, bb⟩, ?_⟩
  simp only [oppositeColorBishopPairs, Finset.mem_filter, Finset.mem_product,
    Board.mem_bishopSquares]
  constructor
  · constructor
    · rw [hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
    · rw [hboard, Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb
        hwb_bb]
  · simpa [bne_iff_ne] using hcol

theorem isSameColorBishops_of_not_oppositeColorBishopPairs {p : Position}
    (h : IsKingBishops p)
    (hne : ¬ (oppositeColorBishopPairs p.board).Nonempty) :
    IsSameColorBishops p := by
  rcases h.same_or_opposite with hsame | hopp
  · exact hsame
  · exact (hne (oppositeColorBishopPairs_nonempty_of_isOpposite hopp)).elim

/-- From same-color bishops, checkmate is not reachable. -/
theorem IsSameColorBishops.not_CheckmateReachable {p : Position}
    (h : IsSameColorBishops p) : ¬ CheckmateReachable p := by
  intro ⟨q, hr, hm⟩
  exact not_InCheckmate_of_scb_or_kb_or_tk (IsSameColorBishops.of_reachable h hr) hm

/-- A same-color king-and-bishop versus king-and-bishop position is dead. -/
theorem deadPosition_of_isSameColorBishops {p : Position}
    (h : IsSameColorBishops p) : DeadPosition p :=
  (DeadPosition_iff_not_CheckmateReachable p).mpr h.not_CheckmateReachable

/-- Decide whether any legally reachable position is checkmate, when `p`
is king-and-bishop versus king and bishop.

Same-color bishops never mate. Opposite-color bishops are searched by
a quiet-move BFS on the four-piece encoding; the search stops at the
first mate and does not enumerate `Finset.univ` of all states. -/
def kingBishopsCheckmateReachable (p : Position) (h : IsKingBishops p) :
    Decidable (CheckmateReachable p) :=
  if hc : p.inCheckmate then
    isTrue (checkmateReachable_of_inCheckmate ((inCheckmate_eq_true_iff p).mp hc))
  else if hopp : (oppositeColorBishopPairs p.board).Nonempty then
    match hs : kingBishopsSearch p with
    | some _ms => isTrue (kingBishopsSearch_checkmateReachable h hs)
    | none => isFalse (kingBishopsSearch_eq_none_not_CheckmateReachable h hs)
  else
    isFalse
      (isSameColorBishops_of_not_oppositeColorBishopPairs h hopp).not_CheckmateReachable

/-- Same-color bishops: checkmate is not reachable. -/
theorem kingBishops_sameColor_not_checkmateReachable {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color) :
    ¬ CheckmateReachable p :=
  (isSameColorBishops_of_valid hv hocc hwb hbb hsame).not_CheckmateReachable

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

theorem oppositeColorBishopsMate_isKingBishops :
    IsKingBishops oppositeColorBishopsMate :=
  isKingBishops_of_valid
    ((isValid_eq_true_iff oppositeColorBishopsMate).mp
      oppositeColorBishopsMate_isValid)
    oppositeColorBishopsMate_occupied_card
    oppositeColorBishopsMate_has_whiteBishop
    oppositeColorBishopsMate_has_blackBishop

/-- The mating position can reach checkmate (it already is checkmate). -/
theorem oppositeColorBishopsMate_CheckmateReachable :
    CheckmateReachable oppositeColorBishopsMate :=
  checkmateReachable_of_inCheckmate oppositeColorBishopsMate_InCheckmate

/-- The four-piece checker reports checkmate is reachable: the position
is already checkmate. -/
theorem oppositeColorBishopsMate_decide_CheckmateReachable :
    @decide (CheckmateReachable oppositeColorBishopsMate)
      (kingBishopsCheckmateReachable oppositeColorBishopsMate
        oppositeColorBishopsMate_isKingBishops) = true := by
  native_decide

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

theorem oppositeColorBishopsBeforeMate_isKingBishops :
    IsKingBishops oppositeColorBishopsBeforeMate :=
  isKingBishops_of_valid
    ((isValid_eq_true_iff oppositeColorBishopsBeforeMate).mp
      oppositeColorBishopsBeforeMate_isValid)
    oppositeColorBishopsBeforeMate_occupied_card
    oppositeColorBishopsBeforeMate_has_whiteBishop
    oppositeColorBishopsBeforeMate_has_blackBishop

/-- The four-piece checker finds the one-move helpmate `Ba4–c6#`. -/
theorem oppositeColorBishopsBeforeMate_decide_CheckmateReachable :
    @decide (CheckmateReachable oppositeColorBishopsBeforeMate)
      (kingBishopsCheckmateReachable oppositeColorBishopsBeforeMate
        oppositeColorBishopsBeforeMate_isKingBishops) = true := by
  native_decide

theorem oppositeColorBishopsBeforeMate_not_deadPosition :
    ¬ DeadPosition oppositeColorBishopsBeforeMate :=
  not_deadPosition_of_checkmateReachable
    oppositeColorBishopsBeforeMate_CheckmateReachable

theorem sameColorBishops_isKingBishops : IsKingBishops sameColorBishops :=
  isKingBishops_of_valid
    ((isValid_eq_true_iff sameColorBishops).mp sameColorBishops_isValid)
    sameColorBishops_occupied_card
    sameColorBishops_has_whiteBishop
    sameColorBishops_has_blackBishop

theorem sameColorBishops_not_CheckmateReachable :
    ¬ CheckmateReachable sameColorBishops :=
  kingBishops_sameColor_not_checkmateReachable
    ((isValid_eq_true_iff sameColorBishops).mp sameColorBishops_isValid)
    sameColorBishops_occupied_card
    sameColorBishops_has_whiteBishop
    sameColorBishops_has_blackBishop
    sameColorBishops_same_square_color

/-- Same-color bishops: the checker reports that checkmate is not
reachable. -/
theorem sameColorBishops_decide_not_CheckmateReachable :
    @decide (CheckmateReachable sameColorBishops)
      (kingBishopsCheckmateReachable sameColorBishops
        sameColorBishops_isKingBishops) = false := by
  native_decide

/-- Two kings alone are not king-and-bishop versus king-and-bishop. -/
theorem kingsOnly_not_IsKingBishops : ¬ IsKingBishops kingsOnly := by
  intro h
  have h4 := h.occupied_card
  have h2 := kingsOnly_occupied_card
  omega

/-- The starting position has 32 pieces, so it is not this material. -/
theorem starting_not_IsKingBishops : ¬ IsKingBishops starting := by
  intro h
  have h4 := h.occupied_card
  have h32 : starting.board.occupied.card = 32 := by
    simp [Board.starting_occupied_card]
  omega

end Position

end Chess
