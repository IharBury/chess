import Chess.KingBishop

/-!
# King and bishop versus king and bishop (same square-color)

A valid position whose board holds only two kings and two bishops, with
both bishops on squares of the same color, is never checkmate. If the
player to move is in check, the check is from the enemy bishop, so the
king stands on that square-color. An orthogonal neighbor has the
opposite color, so neither bishop can occupy or cover it. The other
king is not adjacent (otherwise the opponent would be in check) and
therefore cannot cover both the horizontal and the vertical neighbor,
so one of those squares is a legal flight.

A legal move either keeps both bishops (still on the same color, since
bishops stay on one square-color) or captures a bishop, leaving king
and bishop versus king. In the latter case `IsKingAndBishop` applies.
Hence no sequence of legal moves produces checkmate.
-/

namespace Chess

namespace Board

/-- White king on `wk`, black king on `bk`, white bishop on `wb`, and
black bishop on `bb`. -/
def kingsBishopsBoard (wk bk wb bb : Square) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = wb then some { color := .white, kind := .bishop }
  else if s = bb then some { color := .black, kind := .bishop }
  else none

theorem kingsBishopsBoard_whiteKing (wk bk wb bb : Square) :
    kingsBishopsBoard wk bk wb bb wk = some { color := .white, kind := .king } := by
  simp [kingsBishopsBoard]

theorem kingsBishopsBoard_blackKing (wk bk wb bb : Square) (h : wk ≠ bk) :
    kingsBishopsBoard wk bk wb bb bk = some { color := .black, kind := .king } := by
  simp [kingsBishopsBoard, h.symm]

theorem kingsBishopsBoard_whiteBishop (wk bk wb bb : Square)
    (hw : wk ≠ wb) (hb : bk ≠ wb) :
    kingsBishopsBoard wk bk wb bb wb = some { color := .white, kind := .bishop } := by
  simp [kingsBishopsBoard, hw.symm, hb.symm]

theorem kingsBishopsBoard_blackBishop (wk bk wb bb : Square)
    (hw : wk ≠ bb) (hb : bk ≠ bb) (hbb : wb ≠ bb) :
    kingsBishopsBoard wk bk wb bb bb = some { color := .black, kind := .bishop } := by
  simp [kingsBishopsBoard, hw.symm, hb.symm, hbb.symm]

theorem kingsBishopsBoard_other (wk bk wb bb s : Square)
    (hw : s ≠ wk) (hb : s ≠ bk) (hwb : s ≠ wb) (hbb : s ≠ bb) :
    kingsBishopsBoard wk bk wb bb s = none := by
  simp [kingsBishopsBoard, hw, hb, hwb, hbb]

theorem kingsBishopsBoard_eq_white_king {wk bk wb bb s : Square}
    (h : kingsBishopsBoard wk bk wb bb s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_eq_black_king {wk bk wb bb s : Square}
    (h : kingsBishopsBoard wk bk wb bb s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_eq_white_bishop {wk bk wb bb s : Square}
    (h : kingsBishopsBoard wk bk wb bb s = some { color := .white, kind := .bishop }) :
    s = wb := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_eq_black_bishop {wk bk wb bb s : Square}
    (h : kingsBishopsBoard wk bk wb bb s = some { color := .black, kind := .bishop }) :
    s = bb := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_isSome (wk bk wb bb s : Square) :
    ((kingsBishopsBoard wk bk wb bb) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = wb ∨ s = bb := by
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_whiteBishop_blocked {wk bk wb bb t : Square} :
    (∃ u : Square, Between wb t u ∧
        ((kingsBishopsBoard wk bk wb bb) u).isSome = true) ↔
      Between wb t wk ∨ Between wb t bk ∨ Between wb t bb := by
  constructor
  · intro ⟨u, hB, hocc⟩
    have hu : u = wk ∨ u = bk ∨ u = wb ∨ u = bb :=
      (kingsBishopsBoard_isSome wk bk wb bb u).mp hocc
    rcases hu with hu | hu | hu | hu
    · subst u; exact Or.inl hB
    · subst u; exact Or.inr (Or.inl hB)
    · subst u
      exact (hB.1 rfl).elim
    · subst u; exact Or.inr (Or.inr hB)
  · intro h
    rcases h with hB | hB | hB
    · exact ⟨wk, hB, (kingsBishopsBoard_isSome wk bk wb bb wk).mpr (Or.inl rfl)⟩
    · exact ⟨bk, hB, (kingsBishopsBoard_isSome wk bk wb bb bk).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨bb, hB,
        (kingsBishopsBoard_isSome wk bk wb bb bb).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩

theorem kingsBishopsBoard_blackBishop_blocked {wk bk wb bb t : Square} :
    (∃ u : Square, Between bb t u ∧
        ((kingsBishopsBoard wk bk wb bb) u).isSome = true) ↔
      Between bb t wk ∨ Between bb t bk ∨ Between bb t wb := by
  constructor
  · intro ⟨u, hB, hocc⟩
    have hu : u = wk ∨ u = bk ∨ u = wb ∨ u = bb :=
      (kingsBishopsBoard_isSome wk bk wb bb u).mp hocc
    rcases hu with hu | hu | hu | hu
    · subst u; exact Or.inl hB
    · subst u; exact Or.inr (Or.inl hB)
    · subst u; exact Or.inr (Or.inr hB)
    · subst u
      exact (hB.1 rfl).elim
  · intro h
    rcases h with hB | hB | hB
    · exact ⟨wk, hB, (kingsBishopsBoard_isSome wk bk wb bb wk).mpr (Or.inl rfl)⟩
    · exact ⟨bk, hB, (kingsBishopsBoard_isSome wk bk wb bb bk).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨wb, hB,
        (kingsBishopsBoard_isSome wk bk wb bb wb).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem kingsBishopsBoard_attacks_whiteBishop_iff {wk bk wb bb t : Square}
    (hw : wk ≠ wb) (hb : bk ≠ wb) :
    (kingsBishopsBoard wk bk wb bb).attacks wb t = true ↔
      BishopAttacks wb t ∧ ¬ Between wb t wk ∧ ¬ Between wb t bk ∧
        ¬ Between wb t bb := by
  rw [attacks_bishop_iff (kingsBishopsBoard_whiteBishop wk bk wb bb hw hb),
    kingsBishopsBoard_whiteBishop_blocked]
  tauto

theorem kingsBishopsBoard_attacks_blackBishop_iff {wk bk wb bb t : Square}
    (hw : wk ≠ bb) (hb : bk ≠ bb) (hbb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).attacks bb t = true ↔
      BishopAttacks bb t ∧ ¬ Between bb t wk ∧ ¬ Between bb t bk ∧
        ¬ Between bb t wb := by
  rw [attacks_bishop_iff (kingsBishopsBoard_blackBishop wk bk wb bb hw hb hbb),
    kingsBishopsBoard_blackBishop_blocked]
  tauto

theorem kingsBishopsBoard_occupiedBy_white (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).occupiedBy .white = {wk, wb} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_occupiedBy_black (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).occupiedBy .black = {bk, bb} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_kingSquares_white (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_kingSquares_black (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_occupied (wk bk wb bb : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wb : wk ≠ wb) (_hwk_bb : wk ≠ bb)
    (_hbk_wb : bk ≠ wb) (_hbk_bb : bk ≠ bb) (_hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).occupied = {wk, bk, wb, bb} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsBishopsBoard
  split_ifs <;> simp_all

theorem kingsBishopsBoard_black_piece {wk bk wb bb s : Square}
    (h : (kingsBishopsBoard wk bk wb bb s).map (·.color) = some .black) :
    s = bk ∨ s = bb := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_white_piece {wk bk wb bb s : Square}
    (h : (kingsBishopsBoard wk bk wb bb s).map (·.color) = some .white) :
    s = wk ∨ s = wb := by
  unfold kingsBishopsBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopsBoard_kingIsAttacked_white (wk bk wb bb : Square)
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨
        (BishopAttacks bb wk ∧ ¬ Between bb wk bk ∧ ¬ Between bb wk wb) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBishopsBoard_kingSquares_white wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsBishopsBoard_black_piece hcol
    rcases hpiece with hseq | hseq
    · rw [hseq] at hatt
      rw [attacks_king (kingsBishopsBoard_blackKing wk bk wb bb hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq] at hatt
      rw [kingsBishopsBoard_attacks_blackBishop_iff (t := wk)
        hwk_bb hbk_bb hwb_bb] at hatt
      exact Or.inr ⟨hatt.1, hatt.2.2.1, hatt.2.2.2⟩
  · intro h
    rcases h with hk | ⟨hB, hnbk, hnwb⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopsBoard_blackKing wk bk wb bb hwk_bk]
      · rw [attacks_king (kingsBishopsBoard_blackKing wk bk wb bb hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨bb, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb]
      · rw [kingsBishopsBoard_attacks_blackBishop_iff (t := wk)
          hwk_bb hbk_bb hwb_bb]
        exact ⟨hB, fun hBet => (hBet.2.1 rfl).elim, hnbk, hnwb⟩

theorem kingsBishopsBoard_kingIsAttacked_black (wk bk wb bb : Square)
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨
        (BishopAttacks wb bk ∧ ¬ Between wb bk wk ∧ ¬ Between wb bk bb) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBishopsBoard_kingSquares_black wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsBishopsBoard_white_piece hcol
    rcases hpiece with hseq | hseq
    · rw [hseq] at hatt
      rw [attacks_king (kingsBishopsBoard_whiteKing wk bk wb bb)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq] at hatt
      rw [kingsBishopsBoard_attacks_whiteBishop_iff (t := bk) hwk_wb hbk_wb] at hatt
      exact Or.inr ⟨hatt.1, hatt.2.1, hatt.2.2.2⟩
  · intro h
    rcases h with hk | ⟨hB, hnwk, hnbb⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopsBoard_whiteKing]
      · rw [attacks_king (kingsBishopsBoard_whiteKing wk bk wb bb)]
        exact decide_eq_true hk
    · refine ⟨wb, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
      · rw [kingsBishopsBoard_attacks_whiteBishop_iff (t := bk) hwk_wb hbk_wb]
        exact ⟨hB, hnwk, fun hBet => (hBet.2.1 rfl).elim, hnbb⟩

theorem relocate_kingsBishopsBoard_whiteKing (wk bk wb bb dst : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwb : dst ≠ wb) (_hdbb : dst ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate wk dst { color := .white, kind := .king } =
      kingsBishopsBoard dst bk wb bb := by
  funext s
  unfold relocate kingsBishopsBoard
  split_ifs <;> simp_all

theorem relocate_kingsBishopsBoard_blackKing (wk bk wb bb dst : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwb : dst ≠ wb) (_hdbb : dst ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate bk dst { color := .black, kind := .king } =
      kingsBishopsBoard wk dst wb bb := by
  funext s
  unfold relocate kingsBishopsBoard
  split_ifs <;> simp_all

theorem relocate_kingsBishopsBoard_whiteBishop (wk bk wb bb dst : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwb : dst ≠ wb) (_hdbb : dst ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate wb dst { color := .white, kind := .bishop } =
      kingsBishopsBoard wk bk dst bb := by
  funext s
  unfold relocate kingsBishopsBoard
  split_ifs <;> simp_all

theorem relocate_kingsBishopsBoard_blackBishop (wk bk wb bb dst : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwb : dst ≠ wb) (_hdbb : dst ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate bb dst { color := .black, kind := .bishop } =
      kingsBishopsBoard wk bk wb dst := by
  funext s
  unfold relocate kingsBishopsBoard
  split_ifs <;> simp_all

theorem relocate_capture_blackBishop_whiteKing (wk bk wb bb : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate wk bb { color := .white, kind := .king } =
      kingsBishopBoard bb bk wb .white := by
  funext s
  unfold relocate kingsBishopsBoard kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_capture_whiteBishop_blackKing (wk bk wb bb : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate bk wb { color := .black, kind := .king } =
      kingsBishopBoard wk wb bb .black := by
  funext s
  unfold relocate kingsBishopsBoard kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_capture_blackBishop_whiteBishop (wk bk wb bb : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate wb bb { color := .white, kind := .bishop } =
      kingsBishopBoard wk bk bb .white := by
  funext s
  unfold relocate kingsBishopsBoard kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_capture_whiteBishop_blackBishop (wk bk wb bb : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ wb) (_hbb : wk ≠ bb)
    (_bwb : bk ≠ wb) (_bbb : bk ≠ bb) (_wbbb : wb ≠ bb) :
    (kingsBishopsBoard wk bk wb bb).relocate bb wb { color := .black, kind := .bishop } =
      kingsBishopBoard wk bk wb .black := by
  funext s
  unfold relocate kingsBishopsBoard kingsBishopBoard
  split_ifs <;> simp_all

end Board

namespace Position

/-- King of the player `c`. -/
def scbKing (wk bk : Square) : Color → Square
  | .white => wk
  | .black => bk

/-- King of the opponent of `c`. -/
def scbOtherKing (wk bk : Square) : Color → Square
  | .white => bk
  | .black => wk

/-- Bishop owned by `c`. -/
def scbBishop (wb bb : Square) : Color → Square
  | .white => wb
  | .black => bb

/-- Bishop owned by the opponent of `c`. -/
def scbOppBishop (wb bb : Square) : Color → Square
  | .white => bb
  | .black => wb

/-- Orthogonal flight square for the king of `c`. -/
def scbEscape (wk bk : Square) (c : Color) : Square :=
  kingOrthoEscape (scbKing wk bk c) (scbOtherKing wk bk c)

/-- `p` contains only two kings and two bishops on the same square-color,
with the kings not adjacent, no remaining castling rights, and no en
passant target. -/
def IsSameColorBishops (p : Position) : Prop :=
  ∃ wk bk wb bb : Square,
    wk ≠ bk ∧
      wk ≠ wb ∧
      wk ≠ bb ∧
      bk ≠ wb ∧
      bk ≠ bb ∧
      wb ≠ bb ∧
      ¬ KingAttacks wk bk ∧
      wb.color = bb.color ∧
      p.board = Board.kingsBishopsBoard wk bk wb bb ∧
      p.castling = ∅ ∧
      p.enPassant = none

theorem scbEscape_ortho (wk bk : Square) (c : Color) :
    OrthogonalAdjacent (scbKing wk bk c) (scbEscape wk bk c) :=
  kingOrthoEscape_ortho _ _

theorem scbEscape_not_kingAttacks (wk bk : Square) (c : Color)
    (hne : wk ≠ bk) (hna : ¬ KingAttacks wk bk) :
    ¬ KingAttacks (scbOtherKing wk bk c) (scbEscape wk bk c) := by
  cases c with
  | white =>
    exact kingOrthoEscape_not_kingAttacks wk bk hne.symm
      (mt kingAttacks_symmetric.mp hna)
  | black =>
    exact kingOrthoEscape_not_kingAttacks bk wk hne hna

theorem scbEscape_ne_king (wk bk : Square) (c : Color) :
    scbEscape wk bk c ≠ scbKing wk bk c :=
  kingOrthoEscape_ne_self _ _

theorem scbEscape_ne_otherKing (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    scbEscape wk bk c ≠ scbOtherKing wk bk c := by
  cases c with
  | white =>
    exact kingOrthoEscape_ne_other wk bk (mt kingAttacks_symmetric.mp hna)
  | black =>
    exact kingOrthoEscape_ne_other bk wk hna

theorem scbEscape_ne_wk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    scbEscape wk bk c ≠ wk := by
  cases c with
  | white => exact scbEscape_ne_king wk bk .white
  | black => exact scbEscape_ne_otherKing wk bk .black hna

theorem scbEscape_ne_bk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    scbEscape wk bk c ≠ bk := by
  cases c with
  | white => exact scbEscape_ne_otherKing wk bk .white hna
  | black => exact scbEscape_ne_king wk bk .black

theorem scbBishop_color (wb bb : Square) (c : Color) (hsame : wb.color = bb.color) :
    (scbBishop wb bb c).color = (scbOppBishop wb bb c).color := by
  cases c <;> simp [scbBishop, scbOppBishop, hsame]

theorem scbEscape_ne_oppBishop {wk bk wb bb : Square} {c : Color}
    (hatt : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c)) :
    scbEscape wk bk c ≠ scbOppBishop wb bb c := by
  intro heq
  have hcol : (scbEscape wk bk c).color = (scbKing wk bk c).color.other :=
    orthoAdj_color (scbEscape_ortho wk bk c)
  rw [heq] at hcol
  have hsame : (scbOppBishop wb bb c).color = (scbKing wk bk c).color :=
    bishopAttacks_same_color hatt
  rw [hsame] at hcol
  exact Color.other_ne _ hcol.symm

theorem scbEscape_ne_ownBishop {wk bk wb bb : Square} {c : Color}
    (hsame : wb.color = bb.color)
    (hatt : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c)) :
    scbEscape wk bk c ≠ scbBishop wb bb c := by
  intro heq
  have hcol : (scbEscape wk bk c).color = (scbKing wk bk c).color.other :=
    orthoAdj_color (scbEscape_ortho wk bk c)
  rw [heq] at hcol
  have hopp : (scbOppBishop wb bb c).color = (scbKing wk bk c).color :=
    bishopAttacks_same_color hatt
  have hown : (scbBishop wb bb c).color = (scbOppBishop wb bb c).color :=
    scbBishop_color wb bb c hsame
  rw [hown, hopp] at hcol
  exact Color.other_ne _ hcol.symm

theorem scbEscape_ne_wb {wk bk wb bb : Square} {c : Color}
    (hsame : wb.color = bb.color)
    (hatt : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c)) :
    scbEscape wk bk c ≠ wb := by
  cases c with
  | white => exact scbEscape_ne_ownBishop (c := Color.white) hsame hatt
  | black => exact scbEscape_ne_oppBishop (c := Color.black) hatt

theorem scbEscape_ne_bb {wk bk wb bb : Square} {c : Color}
    (hsame : wb.color = bb.color)
    (hatt : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c)) :
    scbEscape wk bk c ≠ bb := by
  cases c with
  | white => exact scbEscape_ne_oppBishop (c := Color.white) hatt
  | black => exact scbEscape_ne_ownBishop (c := Color.black) hsame hatt

theorem IsSameColorBishops.inCheck_bishopAttacks {p : Position}
    {wk bk wb bb : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = c)
    (hchk : p.inCheck = true) :
    BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c) := by
  unfold inCheck at hchk
  rw [hboard, ht] at hchk
  cases c with
  | white =>
    have hiff := Board.kingsBishopsBoard_kingIsAttacked_white wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna (kingAttacks_symmetric.mp hk)).elim
    · exact h.1
  | black =>
    have hiff := Board.kingsBishopsBoard_kingIsAttacked_black wk bk wb bb
      hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna hk).elim
    · exact h.1

theorem sameColorBishops_escape_src {p : Position} {wk bk wb bb : Square}
    {c : Color}
    (hwk_bk : wk ≠ bk)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = c) :
    p.board (scbKing wk bk c) = some { color := p.toMove, kind := .king } := by
  rw [hboard, ht]
  cases c with
  | white =>
    simpa [scbKing] using Board.kingsBishopsBoard_whiteKing wk bk wb bb
  | black =>
    simpa [scbKing] using Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk

theorem sameColorBishops_escape_dst {p : Position} {wk bk wb bb : Square}
    {c : Color}
    (hna : ¬ KingAttacks wk bk)
    (hsame : wb.color = bb.color)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (hatt : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c)) :
    p.board (scbEscape wk bk c) = none := by
  rw [hboard]
  exact Board.kingsBishopsBoard_other wk bk wb bb (scbEscape wk bk c)
    (scbEscape_ne_wk wk bk c hna)
    (scbEscape_ne_bk wk bk c hna)
    (scbEscape_ne_wb hsame hatt)
    (scbEscape_ne_bb hsame hatt)

theorem sameColorBishops_play_escape_board_white {p : Position}
    {wk bk wb bb : Square} {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hna : ¬ KingAttacks wk bk)
    (hsame : wb.color = bb.color)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = .white)
    (hattB : BishopAttacks bb wk)
    (hsrc : m.src = wk)
    (hdst : m.dst = scbEscape wk bk .white)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .white = none)
    (hsrcP : p.board m.src = some { color := .white, kind := .king }) :
    (p.play m).board =
      Board.kingsBishopsBoard (scbEscape wk bk .white) bk wb bb := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .white) hside hpromo
  have htne_wk := scbEscape_ne_wk wk bk .white hna
  have htne_bk := scbEscape_ne_bk wk bk .white hna
  have hatt : BishopAttacks (scbOppBishop wb bb Color.white) (scbKing wk bk Color.white) :=
    hattB
  have htne_wb := scbEscape_ne_wb (c := Color.white) hsame hatt
  have htne_bb := scbEscape_ne_bb (c := Color.white) hsame hatt
  have hrel := Board.relocate_kingsBishopsBoard_whiteKing wk bk wb bb
    (scbEscape wk bk .white) hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
    htne_wk htne_bk htne_wb htne_bb
  calc (p.play m).board
      = p.boardAfter m { color := .white, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
    _ = (Board.kingsBishopsBoard wk bk wb bb).relocate
          wk (scbEscape wk bk .white) { color := .white, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsBishopsBoard (scbEscape wk bk .white) bk wb bb := hrel

theorem sameColorBishops_play_escape_board_black {p : Position}
    {wk bk wb bb : Square} {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hna : ¬ KingAttacks wk bk)
    (hsame : wb.color = bb.color)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = .black)
    (hattB : BishopAttacks wb bk)
    (hsrc : m.src = bk)
    (hdst : m.dst = scbEscape wk bk .black)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .black = none)
    (hsrcP : p.board m.src = some { color := .black, kind := .king }) :
    (p.play m).board =
      Board.kingsBishopsBoard wk (scbEscape wk bk .black) wb bb := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .black) hside hpromo
  have htne_wk := scbEscape_ne_wk wk bk .black hna
  have htne_bk := scbEscape_ne_bk wk bk .black hna
  have hatt : BishopAttacks (scbOppBishop wb bb Color.black) (scbKing wk bk Color.black) :=
    hattB
  have htne_wb := scbEscape_ne_wb (c := Color.black) hsame hatt
  have htne_bb := scbEscape_ne_bb (c := Color.black) hsame hatt
  have hrel := Board.relocate_kingsBishopsBoard_blackKing wk bk wb bb
    (scbEscape wk bk .black) hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
    htne_wk htne_bk htne_wb htne_bb
  calc (p.play m).board
      = p.boardAfter m { color := .black, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
    _ = (Board.kingsBishopsBoard wk bk wb bb).relocate
          bk (scbEscape wk bk .black) { color := .black, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsBishopsBoard wk (scbEscape wk bk .black) wb bb := hrel

theorem sameColorBishops_escape_safe {p : Position} {wk bk wb bb : Square}
    {c : Color} {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hna : ¬ KingAttacks wk bk)
    (hsame : wb.color = bb.color)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = c)
    (hattB : BishopAttacks (scbOppBishop wb bb c) (scbKing wk bk c))
    (hsrc : m.src = scbKing wk bk c)
    (hdst : m.dst = scbEscape wk bk c)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? p.toMove = none)
    (hsrcP : p.board m.src = some { color := p.toMove, kind := .king }) :
    (p.play m).board.kingIsAttacked p.toMove = false := by
  have ho := scbEscape_ortho wk bk c
  have hnk := scbEscape_not_kingAttacks wk bk c hwk_bk hna
  have hnbish : ¬ BishopAttacks (scbOppBishop wb bb c) (scbEscape wk bk c) :=
    orthoAdj_not_bishopAttacks ho hattB
  cases c with
  | white =>
    have hnb := sameColorBishops_play_escape_board_white hwk_bk hwk_wb hwk_bb
      hbk_wb hbk_bb hwb_bb hna hsame hboard ht hattB hsrc hdst hpromo
      (by simpa [ht] using hside) (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_bk := scbEscape_ne_bk wk bk .white hna
    have htne_wb := scbEscape_ne_wb (c := Color.white) hsame hattB
    have htne_bb := scbEscape_ne_bb (c := Color.white) hsame hattB
    have hiff := Board.kingsBishopsBoard_kingIsAttacked_white
      (scbEscape wk bk .white) bk wb bb
      htne_bk htne_wb htne_bb hbk_wb hbk_bb hwb_bb
    cases hAtt :
      (Board.kingsBishopsBoard (scbEscape wk bk .white) bk wb bb).kingIsAttacked
        .white
    · rfl
    · rcases hiff.mp hAtt with hk | ⟨hB, _, _⟩
      · exact (hnk hk).elim
      · exact (hnbish hB).elim
  | black =>
    have hnb := sameColorBishops_play_escape_board_black hwk_bk hwk_wb hwk_bb
      hbk_wb hbk_bb hwb_bb hna hsame hboard ht hattB hsrc hdst hpromo
      (by simpa [ht] using hside) (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_wk := scbEscape_ne_wk wk bk .black hna
    have htne_wb := scbEscape_ne_wb (c := Color.black) hsame hattB
    have htne_bb := scbEscape_ne_bb (c := Color.black) hsame hattB
    have hiff := Board.kingsBishopsBoard_kingIsAttacked_black wk
      (scbEscape wk bk .black) wb bb
      htne_wk.symm hwk_wb hwk_bb htne_wb htne_bb hwb_bb
    cases hAtt :
      (Board.kingsBishopsBoard wk (scbEscape wk bk .black) wb bb).kingIsAttacked
        .black
    · rfl
    · rcases hiff.mp hAtt with hk | ⟨hB, _, _⟩
      · exact (hnk hk).elim
      · exact (hnbish hB).elim

theorem sameColorBishops_escape_isLegalMove {p : Position}
    {wk bk wb bb : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_wb : wk ≠ wb) (hwk_bb : wk ≠ bb)
    (hbk_wb : bk ≠ wb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hna : ¬ KingAttacks wk bk)
    (hsame : wb.color = bb.color)
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (ht : p.toMove = c)
    (hchk : p.inCheck = true) :
    isLegalMove p (Move.std (scbKing wk bk c) (scbEscape wk bk c)) = true := by
  let m := Move.std (scbKing wk bk c) (scbEscape wk bk c)
  have hattB := IsSameColorBishops.inCheck_bishopAttacks
    hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb hna hboard ht hchk
  have hsrcP : p.board (scbKing wk bk c) =
      some { color := p.toMove, kind := .king } :=
    sameColorBishops_escape_src hwk_bk hboard ht
  have hdstNone := sameColorBishops_escape_dst hna hsame hboard hattB
  have ho := scbEscape_ortho wk bk c
  have hside := castlingSide_none_of_ortho p.toMove ho
  have hgeo : p.board.attacks (scbKing wk bk c) (scbEscape wk bk c) = true := by
    have hsk : Board.kingsBishopsBoard wk bk wb bb (scbKing wk bk c) =
        some { color := p.toMove, kind := .king } := by
      simpa [hboard] using hsrcP
    rw [hboard, Board.attacks_king hsk]
    exact decide_eq_true (orthoAdj_kingAttacks ho)
  have hsrcP' : p.board m.src = some { color := p.toMove, kind := .king } := hsrcP
  have hsafe := sameColorBishops_escape_safe hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb
    hwb_bb hna hsame hboard ht hattB
    (rfl : m.src = scbKing wk bk c) (rfl : m.dst = scbEscape wk bk c) rfl hside hsrcP'
  unfold isLegalMove
  rw [hsrcP']
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := m) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std (scbKing wk bk c) (scbEscape wk bk c)).castlingSide?
      p.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool
    (p.board.attacks (scbKing wk bk c) (scbEscape wk bk c))
    ((Move.std (scbKing wk bk c) (scbEscape wk bk c)).promotion == none)
    ((p.play m).board.kingIsAttacked p.toMove)
    hgeo rfl hsafe

set_option linter.constructorNameAsVariable false

theorem IsSameColorBishops.not_inCheckmate {p : Position}
    (h : IsSameColorBishops p) : p.inCheckmate = false := by
  set_option maxRecDepth 1024 in
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hsame, hboard, _, _⟩ := h
  have hsplit := bool_eq_false_or_true p.inCheck
  cases hsplit with
  | inl hIn => exact not_inCheck_not_inCheckmate hIn
  | inr hIn =>
    have hleg := sameColorBishops_escape_isLegalMove hwk_bk hwk_wb hwk_bb
      hbk_wb hbk_bb hwb_bb hna hsame hboard rfl hIn
    have hmem :
        Move.std (scbKing wk bk p.toMove) (scbEscape wk bk p.toMove) ∈ p.legalMoves :=
      (mem_legalMoves p _).mpr hleg
    have hne : p.legalMoves.card ≠ 0 :=
      mt Finset.card_eq_zero.mp (Finset.ne_empty_of_mem hmem)
    unfold inCheckmate
    rw [hIn]
    simp only [Bool.true_and]
    exact beq_eq_false_iff_ne.mpr hne

theorem IsSameColorBishops.not_InCheckmate {p : Position}
    (h : IsSameColorBishops p) : ¬ InCheckmate p :=
  mt (inCheckmate_eq_true_iff p).mpr
    (Eq.trans_ne h.not_inCheckmate Bool.false_ne_true)

theorem destOk_kingsBishopsBoard {p : Position} {m : Move}
    {wk bk wb bb : Square}
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = wb ∨ m.dst = bb := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsBishopsBoard wk bk wb bb m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsBishopsBoard at hdst
    split_ifs at hdst with h1 h2 h3 h4
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)

theorem sameColorBishops_legalMove_core {p : Position} {m : Move}
    {wk bk wb bb : Square}
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = wb ∨ m.dst = bb) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      p.board.attacks m.src m.dst = true ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .bishop) ∧
        (piece.kind = .king → m.castlingSide? p.toMove = none) := by
  have hm' : isLegalMove p m = true := hm
  unfold isLegalMove at hm'
  cases hsrcB : p.board m.src with
  | none => simp [hsrcB] at hm'
  | some piece =>
    simp only [hsrcB, Bool.and_eq_true] at hm'
    obtain ⟨⟨hcolDest, hifs⟩, hsafeB⟩ := hm'
    have hcol' : piece.color = p.toMove := beq_iff_eq.mp hcolDest.1
    have hdestOk : p.destOk m = true := hcolDest.2
    have hdstOr := destOk_kingsBishopsBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsBishopsBoard wk bk wb bb m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .bishop := by
      have hsrc' := hsrc
      unfold Board.kingsBishopsBoard at hsrc'
      split_ifs at hsrc' with _h1 _h2 _h3 _h4
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inr rfl
      · cases hsrc'; exact Or.inr rfl
    have hpawn : (piece.kind == PieceKind.pawn) = false := by
      cases hkind with
      | inl hk => simp [hk]
      | inr hb => simp [hb]
    have hside : piece.kind = .king → m.castlingSide? p.toMove = none := by
      intro hk
      cases hopt : m.castlingSide? p.toMove with
      | none => rfl
      | some _ =>
        have hs : (m.castlingSide? p.toMove).isSome = true := by simp [hopt]
        have hcastle := castleMoveOk_of_empty (m := m) hcstl
        have hifs' := hifs
        simp [hk, hs, hcastle] at hifs'
    have hgeo : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
      cases hkind with
      | inl hk =>
        have hsnone := hside hk
        simpa [hpawn, hk, hsnone, Bool.and_eq_true, beq_iff_eq] using hifs
      | inr hb =>
        simpa [hpawn, hb, Bool.and_eq_true, beq_iff_eq] using hifs
    exact ⟨hgeo.2, hdestOk, hdstOr, hsafe, hgeo.1, piece, rfl, hcol', hkind, hside⟩

theorem destOk_toMove_of_dst_whiteBishop {p : Position} {m : Move}
    {wk bk wb bb : Square}
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (hwk_wb : wk ≠ wb) (hbk_wb : bk ≠ wb)
    (hdst : m.dst = wb) (hok : p.destOk m = true) :
    p.toMove = Color.black := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb hwk_wb hbk_wb]
    at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem destOk_toMove_of_dst_blackBishop {p : Position} {m : Move}
    {wk bk wb bb : Square}
    (hboard : p.board = Board.kingsBishopsBoard wk bk wb bb)
    (hwk_bb : wk ≠ bb) (hbk_bb : bk ≠ bb) (hwb_bb : wb ≠ bb)
    (hdst : m.dst = bb) (hok : p.destOk m = true) :
    p.toMove = Color.white := by
  unfold destOk at hok
  rw [hdst, hboard,
    Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem IsSameColorBishops.of_play {p : Position} {m : Move}
    (h : IsSameColorBishops p) (hm : LegalMove p m) :
    IsSameColorBishops (p.play m) ∨ IsKingAndBishop (p.play m) := by
  obtain ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb,
    hna, hsame, hboard, hcstl, _hep⟩ := h
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
    · -- White king moves.
      have hpiece : piece = { color := .white, kind := .king } :=
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
        hna', hsame, hboard', hcast', hep'⟩
    · -- Black king moves.
      have hpiece : piece = { color := .black, kind := .king } :=
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
        hdstBB, hwb_bb, hna', hsame, hboard', hcast', hep'⟩
    · -- White bishop moves.
      have hpiece : piece = { color := .white, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcWB, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb
            hwk_wb hbk_wb])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
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
      have hsame' : m.dst.color = bb.color :=
        (bishopAttacks_same_color hAtt).symm.trans hsame
      exact Or.inl ⟨wk, bk, m.dst, bb, hwk_bk, hdstW.symm, hwk_bb, hdstB.symm,
        hbk_bb, hdstBB, hna, hsame', hboard', hcast', hep'⟩
    · -- Black bishop moves.
      have hpiece : piece = { color := .black, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcBB, hboard,
            Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
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
      have hsame' : wb.color = m.dst.color :=
        hsame.trans (bishopAttacks_same_color hAtt)
      exact Or.inl ⟨wk, bk, wb, m.dst, hwk_bk, hwk_wb, hdstW.symm, hbk_wb,
        hdstB.symm, hdstWB.symm, hna, hsame', hboard', hcast', hep'⟩
  · -- Capture on the white bishop's square.
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
    · -- White king cannot capture its own bishop.
      have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcW, hboard, Board.kingsBishopsBoard_whiteKing])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      exact nomatch ht.symm.trans htW
    · -- Black king captures the white bishop.
      have hpiece : piece = { color := .black, kind := .king } :=
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
    · -- Black bishop captures the white bishop.
      have hpiece : piece = { color := .black, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcBB, hboard,
            Board.kingsBishopsBoard_blackBishop wk bk wb bb hwk_bb hbk_bb hwb_bb])
      have hba := boardAfter_bishop p m (c := .black) hpromo
      have hrel := Board.relocate_capture_whiteBishop_blackBishop wk bk wb bb
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
      have hboard' : (p.play m).board = Board.kingsBishopBoard wk bk wb .black := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .bishop } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .bishop } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate bb wb
                { color := .black, kind := .bishop } := by
              rw [hboard, hsrcBB, hdstWb]
          _ = Board.kingsBishopBoard wk bk wb .black := hrel
      exact Or.inr ⟨wk, bk, wb, Color.black, hwk_bk, hwk_wb, hbk_wb, hna,
        hboard', hcast', hep'⟩
  · -- Capture on the black bishop's square.
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
    · -- White king captures the black bishop.
      have hpiece : piece = { color := .white, kind := .king } :=
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
    · -- Black king cannot capture its own bishop.
      have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopsBoard_blackKing wk bk wb bb hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      exact nomatch ht.symm.trans htB
    · -- White bishop captures the black bishop.
      have hpiece : piece = { color := .white, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcWB, hboard, Board.kingsBishopsBoard_whiteBishop wk bk wb bb
            hwk_wb hbk_wb])
      have hba := boardAfter_bishop p m (c := .white) hpromo
      have hrel := Board.relocate_capture_blackBishop_whiteBishop wk bk wb bb
        hwk_bk hwk_wb hwk_bb hbk_wb hbk_bb hwb_bb
      have hboard' : (p.play m).board = Board.kingsBishopBoard wk bk bb .white := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .bishop } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .bishop } := hba
          _ = (Board.kingsBishopsBoard wk bk wb bb).relocate wb bb
                { color := .white, kind := .bishop } := by
              rw [hboard, hsrcWB, hdstBb]
          _ = Board.kingsBishopBoard wk bk bb .white := hrel
      exact Or.inr ⟨wk, bk, bb, Color.white, hwk_bk, hwk_bb, hbk_bb, hna,
        hboard', hcast', hep'⟩
    · exact (hsrcNeBb hsrcBB).elim

theorem IsSameColorBishops.of_reachable {p q : Position}
    (h : IsSameColorBishops p) (hr : Reachable p q) :
    IsSameColorBishops q ∨ IsKingAndBishop q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    rcases ih with hscb | hkb | htk
    · rcases hscb.of_play hleg with hscb' | hkb'
      · exact Or.inl hscb'
      · exact Or.inr (Or.inl hkb')
    · rcases hkb.of_play hleg with hkb' | htk'
      · exact Or.inr (Or.inl hkb')
      · exact Or.inr (Or.inr htk')
    · exact Or.inr (Or.inr (htk.of_play hleg))

/-- A valid position with exactly four occupied squares, a white bishop
and a black bishop on squares of the same color, holds only the two
kings and those bishops, with the kings not adjacent. -/
theorem isSameColorBishops_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color) :
    IsSameColorBishops p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨wb, hwb'⟩ := hwb
  obtain ⟨bb, hbb'⟩ := hbb
  have hcol : wb.color = bb.color := hsame hwb' hbb'
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
  exact ⟨wk, bk, wb, bb, hwk_bk, hwk_wb, hwk_bb, hbk_wb, hbk_bb, hwb_bb, hna, hcol,
    hboard, hc, he⟩

theorem not_inCheckmate_of_scb_or_kb_or_tk {q : Position}
    (h : IsSameColorBishops q ∨ IsKingAndBishop q ∨ IsTwoKings q) :
    q.inCheckmate = false := by
  rcases h with hscb | hkb | htk
  · exact hscb.not_inCheckmate
  · exact hkb.not_inCheckmate
  · exact htk.not_inCheckmate

theorem not_InCheckmate_of_scb_or_kb_or_tk {q : Position}
    (h : IsSameColorBishops q ∨ IsKingAndBishop q ∨ IsTwoKings q) :
    ¬ InCheckmate q := by
  rcases h with hscb | hkb | htk
  · exact hscb.not_InCheckmate
  · exact hkb.not_InCheckmate
  · exact htk.not_InCheckmate

/-- A valid king-and-bishop versus king-and-bishop position with both
bishops on the same square-color is never checkmate. -/
theorem sameColorBishops_not_inCheckmate {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color) :
    p.inCheckmate = false :=
  (isSameColorBishops_of_valid hv hocc hwb hbb hsame).not_inCheckmate

/-- From a valid position with two kings and two same-color bishops,
every legally reachable position is still not checkmate. -/
theorem sameColorBishops_reachable_not_inCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color)
    (hr : Reachable p q) : q.inCheckmate = false :=
  not_inCheckmate_of_scb_or_kb_or_tk
    (IsSameColorBishops.of_reachable
      (isSameColorBishops_of_valid hv hocc hwb hbb hsame) hr)

/-- From a valid position with two kings and two same-color bishops, no
sequence of legal moves produces checkmate. -/
theorem sameColorBishops_legalSeq_not_inCheckmate {p : Position} {ms : List Move}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color)
    (hms : LegalSeq p ms) :
    (playSeq p ms).inCheckmate = false :=
  sameColorBishops_reachable_not_inCheckmate hv hocc hwb hbb hsame
    (legalSeq_reachable hms)

theorem sameColorBishops_reachable_not_InCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 4)
    (hwb : ∃ s, p.board s = some { color := .white, kind := .bishop })
    (hbb : ∃ s, p.board s = some { color := .black, kind := .bishop })
    (hsame : ∀ {s t : Square},
      p.board s = some { color := .white, kind := .bishop } →
      p.board t = some { color := .black, kind := .bishop } →
      s.color = t.color)
    (hr : Reachable p q) : ¬ InCheckmate q :=
  not_InCheckmate_of_scb_or_kb_or_tk
    (IsSameColorBishops.of_reachable
      (isSameColorBishops_of_valid hv hocc hwb hbb hsame) hr)

/-! ### Example: kings on `e1` and `e8`, bishops on `a3` and `c3` -/

/-- White king on `e1`, black king on `e8`, white bishop on `a3`, black
bishop on `c3` (both dark squares), White to move. -/
def sameColorBishops : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.a3 then some { color := .white, kind := .bishop }
    else if s = Square.c3 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem sameColorBishops_isValid : isValid sameColorBishops = true := by
  native_decide

theorem sameColorBishops_occupied_card :
    sameColorBishops.board.occupied.card = 4 := by
  native_decide

theorem sameColorBishops_has_whiteBishop :
    ∃ s, sameColorBishops.board s = some { color := .white, kind := .bishop } :=
  ⟨Square.a3, by native_decide⟩

theorem sameColorBishops_has_blackBishop :
    ∃ s, sameColorBishops.board s = some { color := .black, kind := .bishop } :=
  ⟨Square.c3, by native_decide⟩

def sameColorBishopsIsWhiteBishop (s : Square) : Bool :=
  decide (sameColorBishops.board s = some { color := .white, kind := .bishop })

def sameColorBishopsIsBlackBishop (s : Square) : Bool :=
  decide (sameColorBishops.board s = some { color := .black, kind := .bishop })

theorem sameColorBishops_whiteBishop_eq {s : Square}
    (h : sameColorBishops.board s = some { color := .white, kind := .bishop }) :
    s = Square.a3 := by
  have hb : sameColorBishopsIsWhiteBishop s = true := by
    unfold sameColorBishopsIsWhiteBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter (fun t => sameColorBishopsIsWhiteBishop t = true) =
        {Square.a3} := by
    native_decide
  have : s ∈ ({Square.a3} : Finset Square) := by
    have : s ∈ Finset.univ.filter (fun t => sameColorBishopsIsWhiteBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem sameColorBishops_blackBishop_eq {s : Square}
    (h : sameColorBishops.board s = some { color := .black, kind := .bishop }) :
    s = Square.c3 := by
  have hb : sameColorBishopsIsBlackBishop s = true := by
    unfold sameColorBishopsIsBlackBishop
    exact decide_eq_true h
  have hset :
      Finset.univ.filter (fun t => sameColorBishopsIsBlackBishop t = true) =
        {Square.c3} := by
    native_decide
  have : s ∈ ({Square.c3} : Finset Square) := by
    have : s ∈ Finset.univ.filter (fun t => sameColorBishopsIsBlackBishop t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

theorem sameColorBishops_same_square_color {s t : Square}
    (hs : sameColorBishops.board s = some { color := .white, kind := .bishop })
    (ht : sameColorBishops.board t = some { color := .black, kind := .bishop }) :
    s.color = t.color := by
  rw [sameColorBishops_whiteBishop_eq hs, sameColorBishops_blackBishop_eq ht]
  decide

theorem sameColorBishops_not_inCheckmate_ex : sameColorBishops.inCheckmate = false :=
  sameColorBishops_not_inCheckmate
    ((isValid_eq_true_iff sameColorBishops).mp sameColorBishops_isValid)
    sameColorBishops_occupied_card
    sameColorBishops_has_whiteBishop
    sameColorBishops_has_blackBishop
    sameColorBishops_same_square_color

/-- White's `e1–e2` is a legal flight from the bishop check. -/
theorem sameColorBishops_e1e2_legal :
    isLegalMove sameColorBishops (Move.std Square.e1 Square.e2) = true := by
  native_decide

/-- After `e1–e2`, the position is still not checkmate. -/
theorem sameColorBishops_play_e1e2_not_inCheckmate :
    (sameColorBishops.play (Move.std Square.e1 Square.e2)).inCheckmate = false := by
  native_decide

end Position

end Chess

