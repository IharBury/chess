import Chess.KingKnight
import Chess.EndsGame
import Mathlib.Data.Fintype.Prod

/-!
# King and knight versus king and knight

A valid position whose board holds only two kings and two knights is
king-and-knight versus king-and-knight. Unlike king-and-knight versus
king, checkmate is possible: the two sides cooperate (a helpmate, not a
forced win) and steer into one known mating picture.

## The engineered mating line

The target picture is Black checkmated in the `h8` corner:

* black king on `h8`, black knight on `g8` (occupying the last flight),
* white king on `g6` (covering `g7` and `h7`),
* white knight on `f7` (checking `h8`).

Pieces first assemble on a nearby staging net — white king `g6`, white
knight `e5` or `c4`, black king `f8`, black knight `h6` — by greedy king
steps (least remaining king-metric among strictly reducing dests) and
knight hops toward those squares. The `e5↔c4` / `h6↔f5` shuttle is
skipped while the king is off target, so the king can step instead of
looping. Quiet hops never check, and Black never quietly occupies the
mate square `f7`. A short movie then walks Black into the corner: the
white king wobbles `g6–f6–g6` (or `g6–f6–g5–g6` when White is to move at
the net) so that White has the move for `Ne5–f7` mate.

A potential measures distance to the staging net (plus a check bonus and
a tempo term). Each legal state is either checkmate or has an explicit
next move — never a search over legal moves — after which a few plies of
the same policy strictly lower the potential. Strong induction on the
potential gives `CheckmateReachable`.

Most legal states are covered by a one-ply strictly reducing king or
knight move. The rest follow the scripted policy for a short window.
That every legal state is covered is a Boolean nested loop
(`KNState.checkSlice`), split by white-king files across
`Chess.KingKnightsW0`–`W3` and glued in `Chess.KingKnightsTheorems`. The
loop skips illegal occupancy and adjacent kings; it does not search the
legal-move tree.
-/

namespace Chess

namespace Board

/-- White king on `wk`, black king on `bk`, white knight on `wn`, black
knight on `bn`. -/
def kingsKnightsBoard (wk bk wn bn : Square) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = wn then some { color := .white, kind := .knight }
  else if s = bn then some { color := .black, kind := .knight }
  else none

theorem kingsKnightsBoard_whiteKing (wk bk wn bn : Square) :
    kingsKnightsBoard wk bk wn bn wk = some { color := .white, kind := .king } := by
  simp [kingsKnightsBoard]

theorem kingsKnightsBoard_blackKing (wk bk wn bn : Square) (h : wk ≠ bk) :
    kingsKnightsBoard wk bk wn bn bk = some { color := .black, kind := .king } := by
  simp [kingsKnightsBoard, h.symm]

theorem kingsKnightsBoard_whiteKnight (wk bk wn bn : Square)
    (hw : wk ≠ wn) (hb : bk ≠ wn) :
    kingsKnightsBoard wk bk wn bn wn = some { color := .white, kind := .knight } := by
  simp [kingsKnightsBoard, hw.symm, hb.symm]

theorem kingsKnightsBoard_blackKnight (wk bk wn bn : Square)
    (hw : wk ≠ bn) (hb : bk ≠ bn) (hn : wn ≠ bn) :
    kingsKnightsBoard wk bk wn bn bn = some { color := .black, kind := .knight } := by
  simp [kingsKnightsBoard, hw.symm, hb.symm, hn.symm]

theorem kingsKnightsBoard_other (wk bk wn bn s : Square)
    (hw : s ≠ wk) (hb : s ≠ bk) (hwn : s ≠ wn) (hbn : s ≠ bn) :
    kingsKnightsBoard wk bk wn bn s = none := by
  simp [kingsKnightsBoard, hw, hb, hwn, hbn]

theorem kingsKnightsBoard_eq_white_king {wk bk wn bn s : Square}
    (h : kingsKnightsBoard wk bk wn bn s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_eq_black_king {wk bk wn bn s : Square}
    (h : kingsKnightsBoard wk bk wn bn s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_eq_white_knight {wk bk wn bn s : Square}
    (h : kingsKnightsBoard wk bk wn bn s = some { color := .white, kind := .knight }) :
    s = wn := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_eq_black_knight {wk bk wn bn s : Square}
    (h : kingsKnightsBoard wk bk wn bn s = some { color := .black, kind := .knight }) :
    s = bn := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_isSome (wk bk wn bn s : Square) :
    ((kingsKnightsBoard wk bk wn bn) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = wn ∨ s = bn := by
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_occupiedBy_white (wk bk wn bn : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wn : wk ≠ wn) (_hwk_bn : wk ≠ bn)
    (_hbk_wn : bk ≠ wn) (_hbk_bn : bk ≠ bn) (_hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).occupiedBy .white = {wk, wn} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_occupiedBy_black (wk bk wn bn : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wn : wk ≠ wn) (_hwk_bn : wk ≠ bn)
    (_hbk_wn : bk ≠ wn) (_hbk_bn : bk ≠ bn) (_hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).occupiedBy .black = {bk, bn} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_kingSquares_white (wk bk wn bn : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wn : wk ≠ wn) (_hwk_bn : wk ≠ bn)
    (_hbk_wn : bk ≠ wn) (_hbk_bn : bk ≠ bn) (_hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_kingSquares_black (wk bk wn bn : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wn : wk ≠ wn) (_hwk_bn : wk ≠ bn)
    (_hbk_wn : bk ≠ wn) (_hbk_bn : bk ≠ bn) (_hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_occupied (wk bk wn bn : Square)
    (_hwk_bk : wk ≠ bk) (_hwk_wn : wk ≠ wn) (_hwk_bn : wk ≠ bn)
    (_hbk_wn : bk ≠ wn) (_hbk_bn : bk ≠ bn) (_hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).occupied = {wk, bk, wn, bn} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsKnightsBoard
  split_ifs <;> simp_all

theorem kingsKnightsBoard_black_piece {wk bk wn bn s : Square}
    (h : (kingsKnightsBoard wk bk wn bn s).map (·.color) = some .black) :
    s = bk ∨ s = bn := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_white_piece {wk bk wn bn s : Square}
    (h : (kingsKnightsBoard wk bk wn bn s).map (·.color) = some .white) :
    s = wk ∨ s = wn := by
  unfold kingsKnightsBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightsBoard_kingIsAttacked_white (wk bk wn bn : Square)
    (hwk_bk : wk ≠ bk) (hwk_wn : wk ≠ wn) (hwk_bn : wk ≠ bn)
    (hbk_wn : bk ≠ wn) (hbk_bn : bk ≠ bn) (hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨ KnightAttacks bn wk := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsKnightsBoard_kingSquares_white wk bk wn bn
      hwk_bk hwk_wn hwk_bn hbk_wn hbk_bn hwn_bn,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsKnightsBoard_black_piece hcol
    rcases hpiece with hseq | hseq
    · rw [hseq] at hatt
      rw [attacks_king (kingsKnightsBoard_blackKing wk bk wn bn hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq] at hatt
      rw [attacks_knight (kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn)] at hatt
      exact Or.inr (of_decide_eq_true hatt)
  · intro h
    rcases h with hk | hn
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightsBoard_blackKing wk bk wn bn hwk_bk]
      · rw [attacks_king (kingsKnightsBoard_blackKing wk bk wn bn hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨bn, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn]
      · rw [attacks_knight (kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn)]
        exact decide_eq_true hn

theorem kingsKnightsBoard_kingIsAttacked_black (wk bk wn bn : Square)
    (hwk_bk : wk ≠ bk) (hwk_wn : wk ≠ wn) (hwk_bn : wk ≠ bn)
    (hbk_wn : bk ≠ wn) (hbk_bn : bk ≠ bn) (hwn_bn : wn ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨ KnightAttacks wn bk := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsKnightsBoard_kingSquares_black wk bk wn bn
      hwk_bk hwk_wn hwk_bn hbk_wn hbk_bn hwn_bn,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsKnightsBoard_white_piece hcol
    rcases hpiece with hseq | hseq
    · rw [hseq] at hatt
      rw [attacks_king (kingsKnightsBoard_whiteKing wk bk wn bn)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq] at hatt
      rw [attacks_knight (kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn)] at hatt
      exact Or.inr (of_decide_eq_true hatt)
  · intro h
    rcases h with hk | hn
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightsBoard_whiteKing]
      · rw [attacks_king (kingsKnightsBoard_whiteKing wk bk wn bn)]
        exact decide_eq_true hk
    · refine ⟨wn, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn]
      · rw [attacks_knight (kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn)]
        exact decide_eq_true hn

theorem relocate_kingsKnightsBoard_whiteKing (wk bk wn bn dst : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ wn) (_hbn : wk ≠ bn)
    (_bwn : bk ≠ wn) (_bbn : bk ≠ bn) (_wnbn : wn ≠ bn)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwn : dst ≠ wn) (_hdbn : dst ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).relocate wk dst { color := .white, kind := .king } =
      kingsKnightsBoard dst bk wn bn := by
  funext s
  unfold relocate kingsKnightsBoard
  split_ifs <;> simp_all

theorem relocate_kingsKnightsBoard_blackKing (wk bk wn bn dst : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ wn) (_hbn : wk ≠ bn)
    (_bwn : bk ≠ wn) (_bbn : bk ≠ bn) (_wnbn : wn ≠ bn)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwn : dst ≠ wn) (_hdbn : dst ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).relocate bk dst { color := .black, kind := .king } =
      kingsKnightsBoard wk dst wn bn := by
  funext s
  unfold relocate kingsKnightsBoard
  split_ifs <;> simp_all

theorem relocate_kingsKnightsBoard_whiteKnight (wk bk wn bn dst : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ wn) (_hbn : wk ≠ bn)
    (_bwn : bk ≠ wn) (_bbn : bk ≠ bn) (_wnbn : wn ≠ bn)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwn : dst ≠ wn) (_hdbn : dst ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).relocate wn dst { color := .white, kind := .knight } =
      kingsKnightsBoard wk bk dst bn := by
  funext s
  unfold relocate kingsKnightsBoard
  split_ifs <;> simp_all

theorem relocate_kingsKnightsBoard_blackKnight (wk bk wn bn dst : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ wn) (_hbn : wk ≠ bn)
    (_bwn : bk ≠ wn) (_bbn : bk ≠ bn) (_wnbn : wn ≠ bn)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdwn : dst ≠ wn) (_hdbn : dst ≠ bn) :
    (kingsKnightsBoard wk bk wn bn).relocate bn dst { color := .black, kind := .knight } =
      kingsKnightsBoard wk bk wn dst := by
  funext s
  unfold relocate kingsKnightsBoard
  split_ifs <;> simp_all

end Board

namespace Position

/-- `p` contains only two kings and two knights, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingKnights (p : Position) : Prop :=
  ∃ wk bk wn bn : Square,
    wk ≠ bk ∧
      wk ≠ wn ∧
      wk ≠ bn ∧
      bk ≠ wn ∧
      bk ≠ bn ∧
      wn ≠ bn ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsKnightsBoard wk bk wn bn ∧
      p.castling = ∅ ∧
      p.enPassant = none

/-- A valid position with exactly four occupied squares, a white knight,
and a black knight holds only the two kings and those knights, with the
kings not adjacent. -/
theorem isKingKnights_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 4)
    (hwn : ∃ s, p.board s = some { color := .white, kind := .knight })
    (hbn : ∃ s, p.board s = some { color := .black, kind := .knight }) :
    IsKingKnights p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨wn, hwn'⟩ := hwn
  obtain ⟨bn, hbn'⟩ := hbn
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_wn : wk ≠ wn := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hwn')
  have hwk_bn : wk ≠ bn := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hbn')
  have hbk_wn : bk ≠ wn := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hwn')
  have hbk_bn : bk ≠ bn := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hbn')
  have hwn_bn : wn ≠ bn := by
    intro heq
    rw [heq] at hwn'
    cases hwn'.symm.trans hbn'
  have hoccEq : p.board.occupied = {wk, bk, wn, bn} := by
    have hsub : ({wk, bk, wn, bn} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hwn']
      · simp [Board.mem_occupied, h, hbn']
    have hcard : ({wk, bk, wn, bn} : Finset Square).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hwn_bn]
      · simp [hbk_wn, hbk_bn]
      · simp [hwk_bk, hwk_wn, hwk_bn]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsKnightsBoard wk bk wn bn := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsKnightsBoard_whiteKing]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsKnightsBoard_blackKing wk bk wn bn hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = wn
        · rw [hs, Board.kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn]
          exact hwn'
        · by_cases hs' : s = bn
          · rw [hs', Board.kingsKnightsBoard_blackKnight wk bk wn bn
              hwk_bn hbk_bn hwn_bn]
            exact hbn'
          · have hsocc : s ∉ p.board.occupied := by
              rw [hoccEq]
              simp [hw, hb, hs, hs']
            rw [eq_none_of_not_mem_occupied hsocc,
              Board.kingsKnightsBoard_other wk bk wn bn s hw hb hs hs']
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsKnightsBoard_kingIsAttacked_black wk bk wn bn
          hwk_bk hwk_wn hwk_bn hbk_wn hbk_bn hwn_bn).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsKnightsBoard_kingIsAttacked_white wk bk wn bn
          hwk_bk hwk_wn hwk_bn hbk_wn hbk_bn hwn_bn).mpr
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
    · rw [hsq, hboard, Board.kingsKnightsBoard_whiteKing] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsKnightsBoard_blackKing wk bk wn bn hwk_bk] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn]
        at hrook
      exact some_knight_ne_rook hrook
    · rw [hsq, hboard,
        Board.kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn]
        at hrook
      exact some_knight_ne_rook hrook
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
      · rw [hsq, hboard, Board.kingsKnightsBoard_whiteKing] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsKnightsBoard_blackKing wk bk wn bn hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn]
          at hpawn
        cases some_knight_ne_pawn hpawn
      · rw [hsq, hboard,
          Board.kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn]
          at hpawn
        cases some_knight_ne_pawn hpawn
  exact ⟨wk, bk, wn, bn, hwk_bk, hwk_wn, hwk_bn, hbk_wn, hbk_bn, hwn_bn, hna,
    hboard, hc, he⟩

end Position

/-! ## Four-piece states -/

/-- A king-and-knight versus king-and-knight position by the squares of
its four pieces and the side to move. -/
structure KNState where
  /-- The side to move. -/
  toMove : Color
  /-- White king. -/
  wk : Square
  /-- Black king. -/
  bk : Square
  /-- White knight. -/
  wn : Square
  /-- Black knight. -/
  bn : Square
deriving DecidableEq, Repr

instance : Fintype KNState :=
  Fintype.ofEquiv (Color × Square × Square × Square × Square)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
      invFun := fun s => (s.toMove, s.wk, s.bk, s.wn, s.bn)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A move of the side to move: its king or its knight goes to `dst`. -/
inductive KNMove where
  | king (dst : Square)
  | knight (dst : Square)
deriving DecidableEq, Repr

namespace KNState

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

/-- The eight knight leaps. -/
def knightOffsets : List (Int × Int) :=
  [(1, 2), (1, -2), (-1, 2), (-1, -2), (2, 1), (2, -1), (-2, 1), (-2, -1)]

/-- Squares a king on `k` can step to, by computation. -/
def kingNeighborsOf (k : Square) : List Square :=
  kingOffsets.filterMap fun p => shift k p.1 p.2

/-- Squares a knight on `n` can leap to, by computation. -/
def knightDestsOf (n : Square) : List Square :=
  knightOffsets.filterMap fun p => shift n p.1 p.2

/-- King steps of every square, indexed by `idx`. -/
def kingNeighborsTable : Array (List Square) := (allSquares.map kingNeighborsOf).toArray

/-- Knight destinations of every square, indexed by `idx`. -/
def knightDestsTable : Array (List Square) := (allSquares.map knightDestsOf).toArray

/-- Squares a king on `k` can step to. -/
def kingNeighbors (k : Square) : List Square := kingNeighborsTable.getD (idx k) []

/-- Squares a knight on `n` can leap to. -/
def knightDests (n : Square) : List Square := knightDestsTable.getD (idx n) []

/-- Empty-board knight distance, indexed by `idx s * 64 + idx t`. -/
def knightDistTable : Array Nat := #[
    0, 3, 2, 3, 2, 3, 4, 5, 3, 4, 1, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4,
    2, 3, 2, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 4, 3, 4, 3, 4, 5, 4, 5, 5, 4, 5, 4, 5, 4, 5, 6,
    3, 0, 3, 2, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3,
    3, 2, 3, 2, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 4, 5, 4, 5, 4, 5, 4, 5,
    2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4,
    2, 3, 2, 3, 2, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 5, 5, 4, 5, 4, 5, 4, 5, 4,
    3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 3, 2, 3, 2, 3, 2, 3,
    3, 2, 3, 2, 3, 2, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 5, 4, 5, 4, 5, 4, 5,
    2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 3, 2, 3, 2, 3, 2,
    4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 5, 4, 5, 4, 5, 4, 5, 4,
    3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 3, 2, 3, 2, 3,
    3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 4, 3, 4, 4, 5, 4, 5, 4, 5, 4, 5,
    4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 3, 2, 3, 2,
    4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 4, 3, 4, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 5, 4, 5, 4, 5, 4,
    5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 4, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 3, 2, 3,
    5, 4, 3, 4, 3, 2, 3, 2, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 5, 4, 3, 4, 3, 4, 6, 5, 4, 5, 4, 5, 4, 5,
    3, 2, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5,
    3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 4, 3, 4, 3, 4, 5, 4, 5,
    4, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4,
    2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4,
    1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3,
    3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 5,
    2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2,
    2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4,
    3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4, 3,
    3, 2, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3,
    4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4, 1, 2, 1, 4,
    4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 4, 3, 4,
    3, 4, 3, 2, 1, 2, 3, 4, 4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1,
    3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 4, 3, 4, 4, 5, 4, 3, 4, 3, 4, 3,
    4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2,
    4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 2, 3, 2, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 5, 4, 3, 4, 3, 4,
    2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4,
    2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4,
    1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3,
    1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 5,
    4, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4,
    4, 1, 2, 1, 4, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4,
    3, 4, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3,
    3, 4, 1, 2, 1, 4, 3, 2, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3,
    2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2,
    2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 4, 3, 4, 3, 4,
    3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1,
    3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 4, 3, 4, 3,
    4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 2,
    4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 4, 3, 4,
    5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 2, 3,
    5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 2, 3, 2, 4, 5, 4, 3, 4, 3, 4, 3,
    3, 2, 3, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5,
    3, 2, 1, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 4, 3, 4, 5,
    2, 3, 2, 3, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4,
    2, 3, 2, 1, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 4, 3, 4,
    3, 2, 3, 2, 3, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3,
    1, 2, 3, 2, 1, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3,
    2, 3, 2, 3, 2, 3, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2,
    2, 1, 2, 3, 2, 1, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4,
    3, 2, 3, 2, 3, 2, 3, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3,
    3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3,
    4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2,
    4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2,
    3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 2, 3, 0, 3,
    3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3,
    4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 2, 3, 0,
    4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 4, 3, 2, 3, 2,
    2, 3, 2, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4,
    0, 3, 2, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4,
    3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3,
    3, 0, 3, 2, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3,
    2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4,
    2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 4,
    3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3,
    3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 3, 2, 3, 2, 3, 2, 3,
    4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3, 2, 1, 2,
    2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 3, 2, 3, 2, 3, 2,
    3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 1, 2, 3, 2, 1,
    3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 3, 2, 3, 2, 3,
    4, 3, 4, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 2,
    4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 3, 2, 3, 2,
    5, 4, 3, 4, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 1, 2, 3,
    5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 3, 2, 3,
    3, 4, 3, 4, 3, 4, 5, 4, 2, 3, 2, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5,
    3, 2, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5,
    4, 3, 4, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4,
    2, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4,
    3, 4, 3, 4, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3,
    1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3,
    4, 3, 4, 3, 4, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2,
    2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2,
    3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 2, 3, 4, 1, 2, 1, 4, 3,
    3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4, 1, 2, 1, 4, 3,
    4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 4, 1, 2, 1, 4,
    4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 4, 1, 2, 1, 4,
    5, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1,
    3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1,
    4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2,
    4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2,
    4, 3, 4, 3, 4, 5, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 2, 3, 2, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4,
    2, 1, 4, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5, 3, 2, 1, 2, 3, 4, 3, 4,
    3, 4, 3, 4, 3, 4, 5, 4, 4, 3, 4, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3,
    1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4, 4, 3, 2, 1, 2, 3, 4, 3,
    4, 3, 4, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4,
    4, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4,
    3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4, 2, 3, 2, 3, 2, 3, 2, 3,
    3, 4, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3,
    4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2,
    2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3, 3, 2, 1, 2, 3, 2, 1, 2,
    5, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 2, 3, 2, 3,
    3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2, 4, 3, 2, 1, 2, 3, 2, 1,
    4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 2, 3, 2, 3, 3, 4, 3, 2, 3, 2, 3, 2,
    4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 2, 3, 0, 3, 3, 4, 3, 2, 1, 2, 3, 4,
    5, 4, 5, 4, 3, 4, 3, 4, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 2, 3, 2, 4, 3, 4, 3, 2, 3, 2, 3,
    5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 1, 2, 3, 5, 4, 3, 2, 3, 2, 3, 0, 4, 3, 4, 3, 2, 1, 2, 3,
    5, 4, 5, 4, 5, 4, 5, 6, 4, 3, 4, 3, 4, 5, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 2, 3, 2, 3, 4, 3, 4, 5,
    3, 2, 3, 2, 3, 4, 3, 4, 2, 1, 4, 3, 2, 3, 4, 5, 3, 4, 1, 2, 3, 4, 3, 4, 0, 3, 2, 3, 2, 3, 4, 5,
    4, 5, 4, 5, 4, 5, 4, 5, 3, 4, 3, 4, 3, 4, 5, 4, 4, 3, 4, 3, 4, 3, 4, 5, 3, 2, 3, 2, 3, 4, 3, 4,
    2, 3, 2, 3, 2, 3, 4, 3, 1, 2, 1, 4, 3, 2, 3, 4, 2, 3, 2, 1, 2, 3, 4, 3, 3, 0, 3, 2, 3, 2, 3, 4,
    5, 4, 5, 4, 5, 4, 5, 4, 4, 3, 4, 3, 4, 3, 4, 5, 3, 4, 3, 4, 3, 4, 3, 4, 2, 3, 2, 3, 2, 3, 4, 3,
    3, 2, 3, 2, 3, 2, 3, 4, 4, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3, 4, 2, 3, 0, 3, 2, 3, 2, 3,
    4, 5, 4, 5, 4, 5, 4, 5, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 2, 3, 2, 3, 2, 3, 4,
    2, 3, 2, 3, 2, 3, 2, 3, 3, 4, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3, 2, 3, 0, 3, 2, 3, 2,
    5, 4, 5, 4, 5, 4, 5, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 4, 3, 4, 3, 4, 4, 3, 2, 3, 2, 3, 2, 3,
    3, 2, 3, 2, 3, 2, 3, 2, 2, 3, 4, 1, 2, 1, 4, 3, 3, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3, 0, 3, 2, 3,
    4, 5, 4, 5, 4, 5, 4, 5, 5, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 4, 3, 4, 3, 3, 4, 3, 2, 3, 2, 3, 2,
    4, 3, 2, 3, 2, 3, 2, 3, 3, 2, 3, 4, 1, 2, 1, 4, 4, 3, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3, 0, 3, 2,
    5, 4, 5, 4, 5, 4, 5, 4, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 4, 3, 4, 4, 3, 4, 3, 2, 3, 2, 3,
    3, 4, 3, 2, 3, 2, 3, 2, 4, 3, 2, 3, 4, 1, 2, 1, 3, 4, 3, 2, 1, 2, 3, 2, 4, 3, 2, 3, 2, 3, 0, 3,
    6, 5, 4, 5, 4, 5, 4, 5, 5, 4, 5, 4, 3, 4, 3, 4, 4, 5, 4, 3, 4, 3, 4, 3, 5, 4, 3, 4, 3, 2, 3, 2,
    4, 3, 4, 3, 2, 3, 2, 3, 5, 4, 3, 2, 3, 4, 1, 2, 4, 3, 4, 3, 2, 1, 4, 3, 5, 4, 3, 2, 3, 2, 3, 0
]

/-- Empty-board knight distance from `s` to `t`. -/
def knightDist (s t : Square) : Nat :=
  knightDistTable.getD (idx s * 64 + idx t) 0

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Chebyshev distance. -/
def cheb (s t : Square) : Nat := max (dist s.file.val t.file.val) (dist s.rank.val t.rank.val)

/-- King-walk metric toward `t`: Chebyshev distance, then file, then rank. -/
def kingMetric (k t : Square) : Nat :=
  32 * cheb k t + 4 * dist k.file.val t.file.val + dist k.rank.val t.rank.val

/-- Square `d` is attacked by the enemy king `ek` or enemy knight `en`. -/
def kingAttackedAt (d ek en : Square) : Bool :=
  decide (KingAttacks ek d) || decide (KnightAttacks en d)

/-- Geometric legality of the king step `k → d` against enemy king `ek`,
enemy knight `en`, and own knight `on`. Captures are excluded. -/
def fastKingStep (k d ek en on : Square) : Bool :=
  decide (KingAttacks k d) && d != ek && d != en && d != on && !kingAttackedAt d ek en

/-- Geometric legality of the knight leap `n → d` with own king `k`, enemy
king `ek`, and enemy knight `en`. Captures are excluded. The leap is
legal only when the own king is not already in check (a knight leap onto
an empty square cannot resolve a knight check). -/
def fastKnightMove (n d k ek en : Square) : Bool :=
  decide (KnightAttacks n d) && d != k && d != ek && d != en && !kingAttackedAt k ek en

/-- King of `c`. -/
def king (s : KNState) : Color → Square
  | .white => s.wk
  | .black => s.bk

/-- Knight of `c`. -/
def knight (s : KNState) : Color → Square
  | .white => s.wn
  | .black => s.bn

/-- The king of `c` is attacked. -/
def inCheckB (s : KNState) (c : Color) : Bool :=
  kingAttackedAt (s.king c) (s.king c.other) (s.knight c.other)

/-- The state describes a legal four-piece position: distinct squares,
kings not adjacent, and the side not to move not in check. -/
def okB (s : KNState) : Bool :=
  s.wk != s.bk && s.wk != s.wn && s.wk != s.bn && s.bk != s.wn && s.bk != s.bn &&
    s.wn != s.bn && !decide (KingAttacks s.wk s.bk) && !s.inCheckB s.toMove.other

/-- Geometric legality of a move in an `okB` state. -/
def fastLegal (s : KNState) : KNMove → Bool
  | .king d =>
    fastKingStep (s.king s.toMove) d (s.king s.toMove.other) (s.knight s.toMove.other)
      (s.knight s.toMove)
  | .knight d =>
    fastKnightMove (s.knight s.toMove) d (s.king s.toMove) (s.king s.toMove.other)
      (s.knight s.toMove.other)

/-- The state after a move. -/
def apply (s : KNState) : KNMove → KNState
  | .king d =>
    match s.toMove with
    | .white => { s with toMove := .black, wk := d }
    | .black => { s with toMove := .white, bk := d }
  | .knight d =>
    match s.toMove with
    | .white => { s with toMove := .black, wn := d }
    | .black => { s with toMove := .white, bn := d }

/-- The side to move is checkmated: in check, and every king step is onto
the own knight or onto an attacked square. -/
def mateB (s : KNState) : Bool :=
  let c := s.toMove
  let k := s.king c
  let on := s.knight c
  let ek := s.king c.other
  let en := s.knight c.other
  kingAttackedAt k ek en && (kingNeighbors k).all fun d => d == on || kingAttackedAt d ek en

/-- The chess position of the state. -/
def toPosition (s : KNState) : Position where
  board := Board.kingsKnightsBoard s.wk s.bk s.wn s.bn
  toMove := s.toMove
  castling := ∅
  enPassant := none

/-- The chess move of a state move. -/
def move (s : KNState) : KNMove → Move
  | .king d => Move.std (s.king s.toMove) d
  | .knight d => Move.std (s.knight s.toMove) d

/-! ### Staging net and potential -/

/-- White king target: `g6`. -/
def tgtWK : Square := Square.g6
/-- White knight staging square: `e5`. -/
def tgtWN : Square := Square.e5
/-- White knight waiting square: `c4`, a knight leap from `e5`. -/
def waitWN : Square := Square.c4
/-- Black king staging square: `f8`. -/
def tgtBK : Square := Square.f8
/-- Black knight staging square: `h6`. -/
def tgtBN : Square := ⟨7, 5⟩
/-- Black knight waiting square: `f5`, a knight leap from `h6`. -/
def waitBN : Square := Square.f5
/-- Mating black king: `h8`. -/
def mateBK : Square := Square.h8
/-- Mating black knight: `g8`. -/
def mateBN : Square := Square.g8
/-- Mating white knight: `f7`. -/
def mateWN : Square := Square.f7
/-- White-king tempo square on the finale: `f6`. -/
def tempoWK : Square := Square.f6
/-- Second white-king tempo square on the white-to-move finale: `g5`. -/
def tempoWK2 : Square := ⟨6, 4⟩

/-- White knight work: zero on `e5` and `c4`. -/
def nworkW (wn : Square) : Nat :=
  if wn == tgtWN || wn == waitWN then 0 else min (knightDist wn tgtWN) (knightDist wn waitWN)

/-- Black knight work: zero on `h6` and `f5`. -/
def nworkB (bn : Square) : Nat :=
  if bn == tgtBN || bn == waitBN then 0 else min (knightDist bn tgtBN) (knightDist bn waitBN)

/-- White's share of the staging work. -/
def whiteWork (wk wn : Square) : Nat :=
  if wk == tgtWK && (wn == tgtWN || wn == waitWN) then 0
  else kingMetric wk tgtWK + 8 * nworkW wn

/-- Black's share of the staging work. -/
def blackWork (bk bn : Square) : Nat :=
  if bk == tgtBK && (bn == tgtBN || bn == waitBN) then 0
  else kingMetric bk tgtBK + 8 * nworkB bn

/-- Strict staging: white king `g6`, white knight `e5`, black king `f8`,
black knight `h6`. -/
def assembledStrict (s : KNState) : Bool :=
  s.wk == tgtWK && s.wn == tgtWN && s.bk == tgtBK && s.bn == tgtBN

/-- Remaining plies of the engineered finale, if the state is on that
movie; `none` otherwise. The movie uses a white-king wobble (`g6–f6–g6`
or `g6–f6–g5–g6`) rather than a knight shuttle, so that White has the
move for `Ne5–f7`. -/
def finaleMu (s : KNState) : Option Nat :=
  if s.mateB && s.wk == tgtWK && s.bk == mateBK && s.wn == mateWN && s.bn == mateBN then
    some 0
  else if s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == mateBN &&
      s.toMove == .white then
    some 1
  else if s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some 2
  -- White-to-move assembly: `g6–f6–g5–g6`
  else if s.wk == tempoWK2 && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some 3
  else if s.wk == tempoWK2 && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some 4
  else if s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some 5
  else if s.wk == tempoWK && s.bk == tgtBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some 6
  else if s.assembledStrict && s.toMove == .white then
    some 7
  -- Black-to-move assembly: `g6–f6–g6`
  else if s.wk == tempoWK && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some 3
  else if s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some 4
  else if s.wk == tgtWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some 5
  else if s.assembledStrict && s.toMove == .black then
    some 6
  else if s.wk == tgtWK && s.bk == tgtBK && s.bn == tgtBN && s.wn == waitWN &&
      s.toMove == .white then
    some 8
  else none

/-- Tempo term: a finished side has no progress move of its own. -/
def tempo (s : KNState) : Nat :=
  match s.toMove with
  | .white => if whiteWork s.wk s.wn == 0 then 1 else 0
  | .black => if blackWork s.bk s.bn == 0 then 1 else 0

/-! ### The engineered next move -/

/-- Orthogonal neighbors, files first. -/
def orthos (k : Square) : List Square :=
  [shift k 1 0, shift k (-1) 0, shift k 0 1, shift k 0 (-1)].filterMap id

/-- First legal orthogonal king flight. -/
def escapeMove (s : KNState) : Option KNMove :=
  let k := s.king s.toMove
  let ek := s.king s.toMove.other
  let en := s.knight s.toMove.other
  let on := s.knight s.toMove
  match (orthos k).find? fun d => fastKingStep k d ek en on with
  | some d => some (.king d)
  | none =>
    match (kingNeighbors k).find? fun d => fastKingStep k d ek en on with
    | some d => some (.king d)
    | none => none

/-- Scripted finale move, if the state is on the movie. -/
def finaleMove (s : KNState) : Option KNMove :=
  if s.mateB then none
  else if s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == mateBN &&
      s.toMove == .white then
    some (.knight mateWN)
  else if s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some (.knight mateBN)
  else if s.wk == tempoWK2 && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some (.king tgtWK)
  else if s.wk == tempoWK2 && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some (.king mateBK)
  else if s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some (.king tempoWK2)
  else if s.wk == tempoWK && s.bk == tgtBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some (.king Square.g8)
  else if s.assembledStrict && s.toMove == .white then
    some (.king tempoWK)
  else if s.wk == tempoWK && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some (.king tgtWK)
  else if s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .black then
    some (.king mateBK)
  else if s.wk == tgtWK && s.bk == Square.g8 && s.wn == tgtWN && s.bn == tgtBN &&
      s.toMove == .white then
    some (.king tempoWK)
  else if s.assembledStrict && s.toMove == .black then
    some (.king Square.g8)
  else if s.wk == tgtWK && s.bk == tgtBK && s.bn == tgtBN && s.wn == waitWN &&
      s.toMove == .white then
    some (.knight tgtWN)
  else none

/-- A quiet knight leap: legal, and not a check. The mating hop `Ne5–f7`
is quiet only for White against Black on `h8`. Black never quietly
occupies `f7` (that squares the knight on the mate cell). -/
def quietKnight (s : KNState) (d : Square) : Bool :=
  s.fastLegal (.knight d) &&
    if d == mateWN then
      (s.toMove == .white && s.bk == mateBK)
    else
      !decide (KnightAttacks d (s.king s.toMove.other))

/-- Strictly reducing legal king step of least `kingMetric`, if any. -/
def reducingKing (s : KNState) : Option Square :=
  let k := s.king s.toMove
  let tgt := if s.toMove == .white then tgtWK else tgtBK
  let cur := kingMetric k tgt
  if cur == 0 then none
  else
    let ek := s.king s.toMove.other
    let en := s.knight s.toMove.other
    let on := s.knight s.toMove
    (kingNeighbors k).foldl (fun acc d =>
      if fastKingStep k d ek en on && kingMetric d tgt < cur then
        match acc with
        | none => some d
        | some best =>
          if kingMetric d tgt < kingMetric best tgt then some d else acc
      else acc) none

/-- First quiet knight leap that strictly lowers knight-work. -/
def reducingKnight (s : KNState) : Option Square :=
  let n := s.knight s.toMove
  let cur := if s.toMove == .white then nworkW n else nworkB n
  if cur == 0 then none
  else
    (knightDests n).find? fun d =>
      s.quietKnight d &&
        (if s.toMove == .white then nworkW d else nworkB d) < cur

/-- Waiting knight leap: the `e5`/`c4` or `h6`/`f5` shuttle when that is
quiet, otherwise a quiet leap that does not raise knight-work. -/
def waitKnight (s : KNState) : Option Square :=
  let n := s.knight s.toMove
  let dests := (knightDests n).filter (s.quietKnight ·)
  let shuttle :=
    if s.toMove == .white then
      if n == tgtWN && dests.contains waitWN then some waitWN
      else if n == waitWN && dests.contains tgtWN then some tgtWN
      else none
    else
      if n == tgtBN && dests.contains waitBN then some waitBN
      else if n == waitBN && dests.contains tgtBN then some tgtBN
      else none
  match shuttle with
  | some d => some d
  | none =>
    let cur := if s.toMove == .white then nworkW n else nworkB n
    dests.find? fun d =>
      (if s.toMove == .white then nworkW d else nworkB d) ≤ cur

/-- Quiet legal knight hop of least remaining knight-work, then least
square index. Preferring lower work breaks idle cycles such as
`h8↔g6`. -/
def anyQuietKnight (s : KNState) : Option Square :=
  (knightDests (s.knight s.toMove)).foldl (fun acc d =>
    if s.quietKnight d then
      let nw := if s.toMove == .white then nworkW d else nworkB d
      match acc with
      | none => some d
      | some best =>
        let nwBest := if s.toMove == .white then nworkW best else nworkB best
        if nw < nwBest || (nw == nwBest && idx d < idx best) then some d else acc
    else acc) none

/-- First geometrically legal knight hop, including checks. -/
def anyLegalKnight (s : KNState) : Option Square :=
  (knightDests (s.knight s.toMove)).find? fun d => s.fastLegal (.knight d)

/-- First geometrically legal king step. -/
def anyLegalKing (s : KNState) : Option Square :=
  let k := s.king s.toMove
  (kingNeighbors k).find? fun d =>
    fastKingStep k d (s.king s.toMove.other) (s.knight s.toMove.other) (s.knight s.toMove)

/-- Legal king step of least `kingMetric` toward the staging target.
Used when the king is boxed off a strictly reducing step. -/
def relaxingKing (s : KNState) : Option Square :=
  let k := s.king s.toMove
  let tgt := if s.toMove == .white then tgtWK else tgtBK
  let ek := s.king s.toMove.other
  let en := s.knight s.toMove.other
  let on := s.knight s.toMove
  (kingNeighbors k).foldl (fun acc d =>
    if fastKingStep k d ek en on then
      let m := kingMetric d tgt
      match acc with
      | none => some d
      | some d0 => if m < kingMetric d0 tgt then some d else acc
    else acc) none

/-- The potential: finale counter on the movie, otherwise twice the
staging work plus tempo and a check bonus. -/
def mu (s : KNState) : Nat :=
  if s.mateB then 0
  else
    match s.finaleMu with
    | some n => n
    | none =>
      2 * (whiteWork s.wk s.wn + blackWork s.bk s.bn) + s.tempo +
        (if s.inCheckB s.toMove then 256 else 0) + 16

/-- The king of the side to move is not yet on its staging square. -/
def kingOffTarget (s : KNState) : Bool :=
  let tgt := if s.toMove == .white then tgtWK else tgtBK
  kingMetric (s.king s.toMove) tgt != 0

/-- The destination is the `e5↔c4` or `h6↔f5` waiting shuttle. -/
def shuttleDest (s : KNState) (d : Square) : Bool :=
  if s.toMove == .white then
    (s.wn == tgtWN && d == waitWN) || (s.wn == waitWN && d == tgtWN)
  else
    (s.bn == tgtBN && d == waitBN) || (s.bn == waitBN && d == tgtBN)

/-- The engineered next move: finale, else escape check, else a reducing
king step, else a reducing knight hop, else a waiting knight hop
(skipped for the shuttle while the king is off target, so the king can
step), else any quiet or legal knight hop, else any legal king step. -/
def nextMove (s : KNState) : Option KNMove :=
  if s.mateB then none
  else
    match s.finaleMove with
    | some m => some m
    | none =>
      if s.inCheckB s.toMove then s.escapeMove
      else
        match s.reducingKing with
        | some d => some (.king d)
        | none =>
          match s.reducingKnight with
          | some d => some (.knight d)
          | none =>
            match s.waitKnight with
            | some d =>
              if s.kingOffTarget && s.shuttleDest d then
                match s.relaxingKing with
                | some r => some (.king r)
                | none => some (.knight d)
              else
                some (.knight d)
            | none =>
              match s.anyQuietKnight with
              | some d => some (.knight d)
              | none =>
                match s.anyLegalKnight with
                | some d => some (.knight d)
                | none =>
                  match s.anyLegalKing with
                  | some d => some (.king d)
                  | none => none

/-- The move is legal and leads to a legal state. -/
def oneOk (s : KNState) (m : KNMove) : Bool :=
  s.fastLegal m && (s.apply m).okB

/-- Within `n` plies of the engineered policy from `s`, the potential
falls below that of `s0`, or checkmate is reached. -/
def chain (s0 : KNState) : KNState → Nat → Bool
  | _, 0 => false
  | s, n + 1 =>
    match s.nextMove with
    | none => false
    | some m =>
      s.oneOk m &&
        let s1 := s.apply m
        s1.mateB || s1.mu < s0.mu || chain s0 s1 n

/-- Plies of scripted play allowed to lower the potential. -/
def window : Nat := 12

/-- Whether the side to move has a geometrically legal king step that
strictly lowers `kingMetric`. Cheap to evaluate: no successor state. -/
def hasReducingKing (s : KNState) : Bool :=
  let k := s.king s.toMove
  let tgt := if s.toMove == .white then tgtWK else tgtBK
  let cur := kingMetric k tgt
  let ek := s.king s.toMove.other
  let en := s.knight s.toMove.other
  let on := s.knight s.toMove
  decide (cur ≠ 0) && (kingNeighbors k).any fun d =>
    fastKingStep k d ek en on && decide (kingMetric d tgt < cur)

/-- Whether the side to move has a geometrically legal knight hop that
strictly lowers knight-work and does not check. -/
def hasReducingKnight (s : KNState) : Bool :=
  let n := s.knight s.toMove
  let cur := if s.toMove == .white then nworkW n else nworkB n
  decide (cur ≠ 0) && (knightDests n).any fun d =>
    s.fastLegal (.knight d) &&
      !decide (KnightAttacks d (s.king s.toMove.other)) &&
      decide ((if s.toMove == .white then nworkW d else nworkB d) < cur)

/-- Off the finale, a reducing king step covers the state. The cheap
geometric test is first so `native_decide` skips `finaleMu` on the
common failure path. -/
def reducingKingProgress (s : KNState) : Bool :=
  s.hasReducingKing && s.finaleMu.isNone

/-- Off the finale, a reducing knight hop covers the state. -/
def reducingKnightProgress (s : KNState) : Bool :=
  s.hasReducingKnight && s.finaleMu.isNone

/-- A legal state is covered: it is checkmate, or a one-ply reducing
move exists off the finale, or the engineered policy lowers the potential
in `window` plies. -/
def checkState (s : KNState) : Bool :=
  s.mateB || s.reducingKingProgress || s.reducingKnightProgress || chain s s window

/-- `s` is covered: illegal, or `checkState`. -/
def stateCovered (s : KNState) : Bool :=
  !s.okB || s.checkState

/-- Both colors with these four squares are covered. -/
def pairCovered (wk bk wn bn : Square) : Bool :=
  stateCovered ⟨.white, wk, bk, wn, bn⟩ && stateCovered ⟨.black, wk, bk, wn, bn⟩

/-- Occupancy skip or `pairCovered` for a black-knight square. -/
def bnCovered (wk bk wn bn : Square) : Bool :=
  wk == bn || bk == bn || wn == bn || pairCovered wk bk wn bn

/-- Occupancy skip or every black-knight square, for a white-knight square. -/
def wnCovered (wk bk wn : Square) : Bool :=
  wk == wn || bk == wn || allSquares.all (bnCovered wk bk wn)

/-- Every knight placement with kings `wk`, `bk` is covered. -/
def knightsCovered (wk bk : Square) : Bool :=
  allSquares.all (wnCovered wk bk)

/-- Legal states with white king `wk` and black king `bk` are covered. -/
def kingsCovered (wk bk : Square) : Bool :=
  wk == bk || decide (KingAttacks wk bk) || knightsCovered wk bk

/-- White kings outside `[lo, hi)` are skipped; others go to `kingsCovered`. -/
def wkCovered (lo hi : Nat) (wk : Square) : Bool :=
  decide (wk.file.val < lo) || decide (hi ≤ wk.file.val) ||
    allSquares.all (kingsCovered wk)

/-- Exhaustive Boolean covering of legal states whose white king file
lies in `[lo, hi)`. -/
def checkSlice (lo hi : Nat) : Bool :=
  allSquares.all (wkCovered lo hi)

/-! ### The mating line -/

/-- The moves of a successful `chain` from `s` relative to `s0`, if any. -/
def chainPath (s0 : KNState) : KNState → Nat → Option (List KNMove)
  | _, 0 => none
  | s, n + 1 =>
    match s.nextMove with
    | none => none
    | some m =>
      if s.oneOk m then
        let s1 := s.apply m
        if s1.mateB || s1.mu < s0.mu then some [m]
        else (chainPath s0 s1 n).map (m :: ·)
      else none

/-- The state after a sequence of moves. -/
def applyAll (s : KNState) (ms : List KNMove) : KNState :=
  ms.foldl apply s

/-- The mating line in state moves. Every round lowers the potential or
mates, so `2 * s.mu + 2` rounds suffice. -/
def matingLineAux : KNState → Nat → List KNMove
  | _, 0 => []
  | s, fuel + 1 =>
    if s.mateB then []
    else
      match s.nextMove with
      | some m =>
        if s.oneOk m then
          let s1 := s.apply m
          if s1.mateB || s1.mu < s.mu then
            m :: matingLineAux s1 fuel
          else
            match chainPath s s window with
            | some ms => ms ++ matingLineAux (s.applyAll ms) fuel
            | none => []
        else []
      | none => []

/-- The chess moves of a sequence of state moves. -/
def toMoves : KNState → List KNMove → List Move
  | _, [] => []
  | s, m :: ms => s.move m :: toMoves (s.apply m) ms

/-- The engineered mating line from `s`, as chess moves. -/
def matingLine (s : KNState) : List Move :=
  s.toMoves (matingLineAux s (2 * s.mu + 2))

/-- The four-piece state of a position whose board holds exactly two kings
and two knights in a legal arrangement, with no castling rights and no en
passant target. -/
def ofPosition? (p : Position) : Option KNState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .white, kind := .knight }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .knight }) with
  | some wk, some bk, some wn, some bn =>
    let s : KNState := ⟨p.toMove, wk, bk, wn, bn⟩
    if s.okB && (allSquares.all fun q => p.board q == Board.kingsKnightsBoard wk bk wn bn q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some s
    else none
  | _, _, _, _ => none

/-! ## Soundness -/

open Position

theorem kingAttacks_ne {s t : Square} (h : KingAttacks s t) : s ≠ t := h.1

theorem knightAttacks_ne {s t : Square} (h : KnightAttacks s t) : s ≠ t := by
  intro heq
  subst heq
  simp [KnightAttacks] at h

theorem mem_kingNeighbors {k d : Square} (h : KingAttacks k d) : d ∈ kingNeighbors k := by
  revert k d
  native_decide

theorem mem_knightDests {n d : Square} (h : KnightAttacks n d) : d ∈ knightDests n := by
  revert n d
  native_decide

theorem castlingSide_none_of_kingAttacks (c : Color) {s t : Square} (h : KingAttacks s t) :
    (Move.std s t).castlingSide? c = none := by
  revert c s t
  native_decide

theorem castlingSide_none_of_knightAttacks (c : Color) {s t : Square} (h : KnightAttacks s t) :
    (Move.std s t).castlingSide? c = none := by
  revert c s t
  native_decide

theorem kingAttackedAt_iff (d ek en : Square) :
    kingAttackedAt d ek en = true ↔ KingAttacks ek d ∨ KnightAttacks en d := by
  simp [kingAttackedAt]

theorem kingAttackedAt_eq_false (d ek en : Square) :
    kingAttackedAt d ek en = false ↔ ¬ KingAttacks ek d ∧ ¬ KnightAttacks en d := by
  simp [kingAttackedAt, Bool.or_eq_false_iff, decide_eq_false_iff_not]

theorem okB_iff (s : KNState) :
    s.okB = true ↔
      s.wk ≠ s.bk ∧ s.wk ≠ s.wn ∧ s.wk ≠ s.bn ∧ s.bk ≠ s.wn ∧ s.bk ≠ s.bn ∧ s.wn ≠ s.bn ∧
        ¬ KingAttacks s.wk s.bk ∧ s.inCheckB s.toMove.other = false := by
  simp [okB, and_assoc]

theorem kingIsAttacked_white_eq (wk bk wn bn : Square)
    (hwk_bk : wk ≠ bk) (hwk_wn : wk ≠ wn) (hwk_bn : wk ≠ bn)
    (hbk_wn : bk ≠ wn) (hbk_bn : bk ≠ bn) (hwn_bn : wn ≠ bn) :
    (Board.kingsKnightsBoard wk bk wn bn).kingIsAttacked .white =
      kingAttackedAt wk bk bn := by
  rw [Bool.eq_iff_iff, Board.kingsKnightsBoard_kingIsAttacked_white wk bk wn bn hwk_bk hwk_wn
    hwk_bn hbk_wn hbk_bn hwn_bn, kingAttackedAt_iff]

theorem kingIsAttacked_black_eq (wk bk wn bn : Square)
    (hwk_bk : wk ≠ bk) (hwk_wn : wk ≠ wn) (hwk_bn : wk ≠ bn)
    (hbk_wn : bk ≠ wn) (hbk_bn : bk ≠ bn) (hwn_bn : wn ≠ bn) :
    (Board.kingsKnightsBoard wk bk wn bn).kingIsAttacked .black =
      kingAttackedAt bk wk wn := by
  rw [Bool.eq_iff_iff, Board.kingsKnightsBoard_kingIsAttacked_black wk bk wn bn hwk_bk hwk_wn
    hwk_bn hbk_wn hbk_bn hwn_bn, kingAttackedAt_iff]

theorem kingIsAttacked_eq (s : KNState) (hok : s.okB = true) (c : Color) :
    s.toPosition.board.kingIsAttacked c = s.inCheckB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
  cases c with
  | white => exact kingIsAttacked_white_eq _ _ _ _ h1 h2 h3 h4 h5 h6
  | black => exact kingIsAttacked_black_eq _ _ _ _ h1 h2 h3 h4 h5 h6

theorem fastKingStep_iff (k d ek en on : Square) :
    fastKingStep k d ek en on = true ↔
      KingAttacks k d ∧ d ≠ ek ∧ d ≠ en ∧ d ≠ on ∧ kingAttackedAt d ek en = false := by
  simp [fastKingStep, and_assoc]

theorem fastKnightMove_iff (n d k ek en : Square) :
    fastKnightMove n d k ek en = true ↔
      KnightAttacks n d ∧ d ≠ k ∧ d ≠ ek ∧ d ≠ en ∧ kingAttackedAt k ek en = false := by
  simp [fastKnightMove, and_assoc]

theorem legal_step_bool {unused₁ unused₂ : Bool} (att promoNone attacked : Bool)
    (hatt : att = true) (hpromo : promoNone = true) (hsafe : attacked = false) :
    ((if false = true then unused₁
      else if false = true then unused₂
      else att && promoNone) && !attacked) = true := by
  simp [hatt, hpromo, hsafe]

theorem destOk_of_empty {p : Position} {m : Move}
    (h : p.board m.dst = none) : p.destOk m = true := by
  unfold destOk
  rw [h]

/-- A white king step of an `okB` state is legal and leads to the applied state. -/
theorem play_whiteKing {s : KNState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : fastKingStep s.wk d s.bk s.bn s.wn = true) :
    isLegalMove s.toPosition (Move.std s.wk d) = true ∧
      s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdbk, hdbn, hdwn, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hm
  have hdwk : d ≠ s.wk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.wk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsKnightsBoard s.wk s.bk s.wn s.bn s.wk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsKnightsBoard_whiteKing _ _ _ _
  have hdstNone : s.toPosition.board (Move.std s.wk d).dst = none :=
    Board.kingsKnightsBoard_other _ _ _ _ d hdwk hdbk hdwn hdbn
  have hside : (Move.std s.wk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.wk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.wk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsKnightsBoard d s.bk s.wn s.bn := by
    rw [hba]
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.wk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsKnightsBoard_whiteKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwn hdbn
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
    change (Board.kingsKnightsBoard d s.bk s.wn s.bn).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq d s.bk s.wn s.bn hdbk hdwn hdbn h4 h5 h6]
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
  exact legal_step_bool _ _ _ hgeo rfl hsafe'

theorem play_blackKing {s : KNState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .black)
    (hm : fastKingStep s.bk d s.wk s.wn s.bn = true) :
    isLegalMove s.toPosition (Move.std s.bk d) = true ∧
      s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdwk, hdwn, hdbn, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hm
  have hdbk : d ≠ s.bk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.bk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsKnightsBoard s.wk s.bk s.wn s.bn s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsKnightsBoard_blackKing _ _ _ _ h1
  have hdstNone : s.toPosition.board (Move.std s.bk d).dst = none :=
    Board.kingsKnightsBoard_other _ _ _ _ d hdwk hdbk hdwn hdbn
  have hside : (Move.std s.bk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsKnightsBoard s.wk d s.wn s.bn := by
    rw [hba]
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.bk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsKnightsBoard_blackKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwn hdbn
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
    change (Board.kingsKnightsBoard s.wk d s.wn s.bn).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk d s.wn s.bn hdwk.symm h2 h3 hdwn hdbn h6]
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
  exact legal_step_bool _ _ _ hgeo rfl hsafe'

theorem play_whiteKnight {s : KNState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : fastKnightMove s.wn d s.wk s.bk s.bn = true) :
    isLegalMove s.toPosition (Move.std s.wn d) = true ∧
      s.toPosition.play (Move.std s.wn d) = (s.apply (.knight d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hna, hdwk, hdbk, hdbn, hsafe⟩ := (fastKnightMove_iff _ _ _ _ _).mp hm
  have hdwn : d ≠ s.wn := knightAttacks_ne hna |>.symm
  have hsrcP : s.toPosition.board (Move.std s.wn d).src =
      some { color := s.toPosition.toMove, kind := .knight } := by
    change Board.kingsKnightsBoard s.wk s.bk s.wn s.bn s.wn =
      some { color := s.toMove, kind := .knight }
    rw [ht]
    exact Board.kingsKnightsBoard_whiteKnight _ _ _ _ h2 h4
  have hdstNone : s.toPosition.board (Move.std s.wn d).dst = none :=
    Board.kingsKnightsBoard_other _ _ _ _ d hdwk hdbk hdwn hdbn
  have hside : (Move.std s.wn d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_knightAttacks _ hna
  have hplay := play_of_some s.toPosition (Move.std s.wn d) hsrcP
  have hba := boardAfter_knight s.toPosition (Move.std s.wn d) (c := s.toPosition.toMove) rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wn d)
      { color := s.toPosition.toMove, kind := .knight } =
      Board.kingsKnightsBoard s.wk s.bk d s.bn := by
    rw [hba]
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.wn d
      { color := s.toMove, kind := .knight } = _
    rw [ht]
    exact Board.relocate_kingsKnightsBoard_whiteKnight _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwn
      hdbn
  have hplay' : s.toPosition.play (Move.std s.wn d) = (s.apply (.knight d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_knight]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.wn d).src (Move.std s.wn d).dst = true := by
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks s.wn d = true
    rw [Board.attacks_knight (Board.kingsKnightsBoard_whiteKnight _ _ _ _ h2 h4)]
    exact decide_eq_true hna
  have hsafe' : (s.toPosition.play (Move.std s.wn d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.knight d) = { s with toMove := .black, wn := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsKnightsBoard s.wk s.bk d s.bn).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq s.wk s.bk d s.bn h1 hdwk.symm h3 hdbk.symm h5 hdbn]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.wn d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.knight == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.knight == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_step_bool _ _ _ hgeo rfl hsafe'

theorem play_blackKnight {s : KNState} {d : Square} (hok : s.okB = true) (ht : s.toMove = .black)
    (hm : fastKnightMove s.bn d s.bk s.wk s.wn = true) :
    isLegalMove s.toPosition (Move.std s.bn d) = true ∧
      s.toPosition.play (Move.std s.bn d) = (s.apply (.knight d)).toPosition := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hna, hdbk, hdwk, hdwn, hsafe⟩ := (fastKnightMove_iff _ _ _ _ _).mp hm
  have hdbn : d ≠ s.bn := knightAttacks_ne hna |>.symm
  have hsrcP : s.toPosition.board (Move.std s.bn d).src =
      some { color := s.toPosition.toMove, kind := .knight } := by
    change Board.kingsKnightsBoard s.wk s.bk s.wn s.bn s.bn =
      some { color := s.toMove, kind := .knight }
    rw [ht]
    exact Board.kingsKnightsBoard_blackKnight _ _ _ _ h3 h5 h6
  have hdstNone : s.toPosition.board (Move.std s.bn d).dst = none :=
    Board.kingsKnightsBoard_other _ _ _ _ d hdwk hdbk hdwn hdbn
  have hside : (Move.std s.bn d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_knightAttacks _ hna
  have hplay := play_of_some s.toPosition (Move.std s.bn d) hsrcP
  have hba := boardAfter_knight s.toPosition (Move.std s.bn d) (c := s.toPosition.toMove) rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bn d)
      { color := s.toPosition.toMove, kind := .knight } =
      Board.kingsKnightsBoard s.wk s.bk s.wn d := by
    rw [hba]
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.bn d
      { color := s.toMove, kind := .knight } = _
    rw [ht]
    exact Board.relocate_kingsKnightsBoard_blackKnight _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk hdwn
      hdbn
  have hplay' : s.toPosition.play (Move.std s.bn d) = (s.apply (.knight d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_knight]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.bn d).src (Move.std s.bn d).dst = true := by
    change (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks s.bn d = true
    rw [Board.attacks_knight (Board.kingsKnightsBoard_blackKnight _ _ _ _ h3 h5 h6)]
    exact decide_eq_true hna
  have hsafe' : (s.toPosition.play (Move.std s.bn d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.knight d) = { s with toMove := .white, bn := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsKnightsBoard s.wk s.bk s.wn d).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk s.bk s.wn d h1 h2 hdwk.symm h4 hdbk.symm hdwn.symm]
    exact hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.bn d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.knight == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.knight == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_step_bool _ _ _ hgeo rfl hsafe'

theorem fastLegal_sound {s : KNState} {m : KNMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    isLegalMove s.toPosition (s.move m) = true ∧
      s.toPosition.play (s.move m) = (s.apply m).toPosition := by
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht, king, knight, Color.other] at hm
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.wk d) ▸
        play_whiteKing hok ht hm
    | black =>
      simp only [fastLegal, ht, king, knight, Color.other] at hm
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.bk d) ▸
        play_blackKing hok ht hm
  | knight d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht, king, knight, Color.other] at hm
      exact (by simp [move, ht, knight] : s.move (.knight d) = Move.std s.wn d) ▸
        play_whiteKnight hok ht hm
    | black =>
      simp only [fastLegal, ht, king, knight, Color.other] at hm
      exact (by simp [move, ht, knight] : s.move (.knight d) = Move.std s.bn d) ▸
        play_blackKnight hok ht hm

theorem legalMove_of_fastLegal {s : KNState} {m : KNMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) : LegalMove s.toPosition (s.move m) :=
  (fastLegal_sound hok hm).1

theorem play_move_eq {s : KNState} {m : KNMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    s.toPosition.play (s.move m) = (s.apply m).toPosition :=
  (fastLegal_sound hok hm).2

theorem mateB_iff (s : KNState) :
    s.mateB = true ↔
      kingAttackedAt (s.king s.toMove) (s.king s.toMove.other) (s.knight s.toMove.other) = true ∧
        ∀ d ∈ kingNeighbors (s.king s.toMove),
          d = s.knight s.toMove ∨
            kingAttackedAt d (s.king s.toMove.other) (s.knight s.toMove.other) = true := by
  simp [mateB, List.all_eq_true, beq_iff_eq, Bool.or_eq_true]

/-! ### Progress from the exhaustive check -/

/-- `s` makes progress to `s1`: `s1` is legal and reachable, and is
checkmate or has strictly smaller potential. -/
def Progress (s s1 : KNState) : Prop :=
  s1.okB = true ∧ Reachable s.toPosition s1.toPosition ∧
    (s1.mateB = true ∨ s1.mu < s.mu)

theorem reachable_apply {s : KNState} {m : KNMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    Reachable s.toPosition (s.apply m).toPosition := by
  have := Reachable.step (s.move m) Reachable.refl (legalMove_of_fastLegal hok hm)
  rwa [play_move_eq hok hm] at this

theorem oneOk_iff (s : KNState) (m : KNMove) :
    s.oneOk m = true ↔ s.fastLegal m = true ∧ (s.apply m).okB = true := by
  simp [oneOk]

theorem kingMetric_self (k : Square) : kingMetric k k = 0 := by
  simp [kingMetric, cheb, dist]

theorem kingMetric_eq_zero (k t : Square) : (kingMetric k t == 0) = decide (k = t) := by
  revert k t
  native_decide

theorem whiteWork_lt_of_kingMetric {wks wns ds : Square}
    (h0 : kingMetric wks tgtWK ≠ 0)
    (hlt : kingMetric ds tgtWK < kingMetric wks tgtWK) :
    whiteWork ds wns < whiteWork wks wns := by
  have hne : wks ≠ tgtWK := by
    intro heq
    subst heq
    exact h0 (kingMetric_self tgtWK)
  have hw : whiteWork wks wns = kingMetric wks tgtWK + 8 * nworkW wns := by
    unfold whiteWork
    split_ifs with h
    · simp only [beq_iff_eq, Bool.and_eq_true] at h
      exact (hne h.1).elim
    · rfl
  rw [hw]
  unfold whiteWork
  split_ifs <;> omega

theorem blackWork_lt_of_kingMetric {bks bns ds : Square}
    (h0 : kingMetric bks tgtBK ≠ 0)
    (hlt : kingMetric ds tgtBK < kingMetric bks tgtBK) :
    blackWork ds bns < blackWork bks bns := by
  have hne : bks ≠ tgtBK := by
    intro heq
    subst heq
    exact h0 (kingMetric_self tgtBK)
  have hw : blackWork bks bns = kingMetric bks tgtBK + 8 * nworkB bns := by
    unfold blackWork
    split_ifs with h
    · simp only [beq_iff_eq, Bool.and_eq_true] at h
      exact (hne h.1).elim
    · rfl
  rw [hw]
  unfold blackWork
  split_ifs <;> omega

theorem nworkW_eq_zero_of_staging {wns : Square} (h : wns = tgtWN ∨ wns = waitWN) :
    nworkW wns = 0 := by
  unfold nworkW
  rcases h with rfl | rfl
  · simp only [beq_self_eq_true, Bool.true_or, ite_true]
  · simp only [beq_self_eq_true, Bool.or_true, ite_true]

theorem nworkB_eq_zero_of_staging {bns : Square} (h : bns = tgtBN ∨ bns = waitBN) :
    nworkB bns = 0 := by
  unfold nworkB
  rcases h with rfl | rfl
  · simp only [beq_self_eq_true, Bool.true_or, ite_true]
  · simp only [beq_self_eq_true, Bool.or_true, ite_true]

theorem whiteWork_lt_of_nwork {wks wns ns : Square}
    (h0 : nworkW wns ≠ 0)
    (hlt : nworkW ns < nworkW wns) :
    whiteWork wks ns < whiteWork wks wns := by
  have hw : whiteWork wks wns = kingMetric wks tgtWK + 8 * nworkW wns := by
    unfold whiteWork
    split_ifs with h
    · simp only [beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true] at h
      exact (h0 (nworkW_eq_zero_of_staging h.2)).elim
    · rfl
  have : 0 < nworkW wns := Nat.pos_of_ne_zero h0
  rw [hw]
  unfold whiteWork
  split_ifs <;> omega

theorem blackWork_lt_of_nwork {bks bns ns : Square}
    (h0 : nworkB bns ≠ 0)
    (hlt : nworkB ns < nworkB bns) :
    blackWork bks ns < blackWork bks bns := by
  have hw : blackWork bks bns = kingMetric bks tgtBK + 8 * nworkB bns := by
    unfold blackWork
    split_ifs with h
    · simp only [beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true] at h
      exact (h0 (nworkB_eq_zero_of_staging h.2)).elim
    · rfl
  have : 0 < nworkB bns := Nat.pos_of_ne_zero h0
  rw [hw]
  unfold blackWork
  split_ifs <;> omega

theorem tempo_le (s : KNState) : s.tempo ≤ 1 := by
  cases htm : s.toMove
  · simp only [tempo, htm]; split_ifs <;> omega
  · simp only [tempo, htm]; split_ifs <;> omega

theorem finaleMu_le {s : KNState} {n : Nat} (h : s.finaleMu = some n) : n ≤ 8 := by
  unfold finaleMu at h
  cases h0 : (s.mateB && s.wk == tgtWK && s.bk == mateBK && s.wn == mateWN && s.bn == mateBN)
  · rw [h0, if_neg Bool.false_ne_true] at h
    cases h1 : (s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == mateBN &&
        s.toMove == .white)
    · rw [h1, if_neg Bool.false_ne_true] at h
      cases h2 : (s.wk == tgtWK && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
          s.toMove == .black)
      · rw [h2, if_neg Bool.false_ne_true] at h
        cases h3 : (s.wk == tempoWK2 && s.bk == mateBK && s.wn == tgtWN && s.bn == tgtBN &&
            s.toMove == .white)
        · rw [h3, if_neg Bool.false_ne_true] at h
          cases h4 : (s.wk == tempoWK2 && s.bk == Square.g8 && s.wn == tgtWN &&
              s.bn == tgtBN && s.toMove == .black)
          · rw [h4, if_neg Bool.false_ne_true] at h
            cases h5 : (s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN &&
                s.bn == tgtBN && s.toMove == .white)
            · rw [h5, if_neg Bool.false_ne_true] at h
              cases h6 : (s.wk == tempoWK && s.bk == tgtBK && s.wn == tgtWN &&
                  s.bn == tgtBN && s.toMove == .black)
              · rw [h6, if_neg Bool.false_ne_true] at h
                cases h7 : (s.assembledStrict && s.toMove == .white)
                · rw [h7, if_neg Bool.false_ne_true] at h
                  cases h8 : (s.wk == tempoWK && s.bk == mateBK && s.wn == tgtWN &&
                      s.bn == tgtBN && s.toMove == .white)
                  · rw [h8, if_neg Bool.false_ne_true] at h
                    cases h9 : (s.wk == tempoWK && s.bk == Square.g8 && s.wn == tgtWN &&
                        s.bn == tgtBN && s.toMove == .black)
                    · rw [h9, if_neg Bool.false_ne_true] at h
                      cases h10 : (s.wk == tgtWK && s.bk == Square.g8 && s.wn == tgtWN &&
                          s.bn == tgtBN && s.toMove == .white)
                      · rw [h10, if_neg Bool.false_ne_true] at h
                        cases h11 : (s.assembledStrict && s.toMove == .black)
                        · rw [h11, if_neg Bool.false_ne_true] at h
                          cases h12 : (s.wk == tgtWK && s.bk == tgtBK && s.bn == tgtBN &&
                              s.wn == waitWN && s.toMove == .white)
                          · rw [h12, if_neg Bool.false_ne_true] at h
                            nomatch h
                          · rw [h12] at h; injection h with hn; omega
                        · rw [h11] at h; injection h with hn; omega
                      · rw [h10] at h; injection h with hn; omega
                    · rw [h9] at h; injection h with hn; omega
                  · rw [h8] at h; injection h with hn; omega
                · rw [h7] at h; injection h with hn; omega
              · rw [h6] at h; injection h with hn; omega
            · rw [h5] at h; injection h with hn; omega
          · rw [h4] at h; injection h with hn; omega
        · rw [h3] at h; injection h with hn; omega
      · rw [h2] at h; injection h with hn; omega
    · rw [h1] at h; injection h with hn; omega
  · rw [h0] at h; injection h with hn; omega

theorem mu_staging {s : KNState} (hm : s.mateB = false) (hf : s.finaleMu = none) :
    s.mu = 2 * (whiteWork s.wk s.wn + blackWork s.bk s.bn) + s.tempo +
      (if s.inCheckB s.toMove then 256 else 0) + 16 := by
  unfold mu
  rw [if_neg (Bool.eq_false_iff.mp hm), hf]

theorem staging_mu_ge {s : KNState} (hm : s.mateB = false) (hf : s.finaleMu = none) :
    16 ≤ s.mu := by
  rw [mu_staging hm hf]
  omega

theorem fastKingStep_apply_okB {s : KNState} {d : Square}
    (hok : s.okB = true)
    (hs : fastKingStep (s.king s.toMove) d (s.king s.toMove.other)
      (s.knight s.toMove.other) (s.knight s.toMove) = true) :
    (s.apply (.king d)).okB = true := by
  cases ht : s.toMove with
  | white =>
    obtain ⟨_, _, _, h4, h5, h6, _, _⟩ := (okB_iff s).mp hok
    obtain ⟨_, hdek, hden, hdon, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hs
    simp only [king, knight, Color.other, ht] at hdek hden hdon hsafe
    have hnk : ¬ KingAttacks s.bk d := ((kingAttackedAt_eq_false _ _ _).mp hsafe).1
    rw [okB_iff]
    simp only [apply, ht, inCheckB, king, knight, Color.other]
    exact ⟨hdek, hdon, hden, h4, h5, h6,
      fun hk => hnk (kingAttacks_symmetric.mp hk), hsafe⟩
  | black =>
    obtain ⟨_, h2, h3, _, _, h6, _, _⟩ := (okB_iff s).mp hok
    obtain ⟨_, hdek, hden, hdon, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hs
    simp only [king, knight, Color.other, ht] at hdek hden hdon hsafe
    have hnk : ¬ KingAttacks s.wk d := ((kingAttackedAt_eq_false _ _ _).mp hsafe).1
    rw [okB_iff]
    simp only [apply, ht, inCheckB, king, knight, Color.other]
    exact ⟨fun h => hdek h.symm, h2, h3, hden, hdon, h6, hnk, hsafe⟩

theorem fastKnightMove_apply_okB {s : KNState} {d : Square}
    (hok : s.okB = true)
    (hs : s.fastLegal (.knight d) = true) :
    (s.apply (.knight d)).okB = true := by
  cases ht : s.toMove with
  | white =>
    obtain ⟨h1, _, h3, _, h5, _, hka, _⟩ := (okB_iff s).mp hok
    simp only [fastLegal, king, knight, Color.other, ht] at hs
    obtain ⟨_, hdk, hdek, hden, hsafe⟩ := (fastKnightMove_iff _ _ _ _ _).mp hs
    rw [okB_iff]
    simp only [apply, ht, inCheckB, king, knight, Color.other]
    exact ⟨h1, fun h => hdk h.symm, h3, fun h => hdek h.symm, h5, hden, hka, hsafe⟩
  | black =>
    obtain ⟨h1, h2, _, h4, _, _, hka, _⟩ := (okB_iff s).mp hok
    simp only [fastLegal, king, knight, Color.other, ht] at hs
    obtain ⟨_, hdk, hdek, hden, hsafe⟩ := (fastKnightMove_iff _ _ _ _ _).mp hs
    rw [okB_iff]
    simp only [apply, ht, inCheckB, king, knight, Color.other]
    exact ⟨h1, h2, fun h => hdek h.symm, h4, fun h => hdk h.symm, fun h => hden h.symm,
      hka, hsafe⟩

theorem oneOk_king_of_fastKingStep {s : KNState} {d : Square}
    (hok : s.okB = true)
    (hs : fastKingStep (s.king s.toMove) d (s.king s.toMove.other)
      (s.knight s.toMove.other) (s.knight s.toMove) = true) :
    s.oneOk (.king d) = true := by
  rw [oneOk_iff, fastLegal]
  exact ⟨hs, fastKingStep_apply_okB hok hs⟩

theorem oneOk_knight_of_fastLegal {s : KNState} {d : Square}
    (hok : s.okB = true) (hs : s.fastLegal (.knight d) = true) :
    s.oneOk (.knight d) = true :=
  (oneOk_iff s (.knight d)).mpr ⟨hs, fastKnightMove_apply_okB hok hs⟩

theorem chain_sound {s0 s : KNState} (hok : s.okB = true) :
    ∀ n, chain s0 s n = true → ∃ s1 : KNState, s1.okB = true ∧
      Reachable s.toPosition s1.toPosition ∧ (s1.mateB = true ∨ s1.mu < s0.mu) := by
  intro n
  induction n generalizing s with
  | zero =>
    intro h
    simp [chain] at h
  | succ n ih =>
    intro h
    simp only [chain] at h
    cases hmv : s.nextMove with
    | none => simp [hmv] at h
    | some m =>
      simp only [hmv, Bool.and_eq_true] at h
      obtain ⟨hokm, hrest⟩ := h
      obtain ⟨hfl, hok1⟩ := (oneOk_iff s m).mp hokm
      have hr := reachable_apply hok hfl
      simp only [Bool.or_eq_true, decide_eq_true_iff] at hrest
      rcases hrest with h1 | hch
      · rcases h1 with hm1 | hlt
        · exact ⟨s.apply m, hok1, hr, Or.inl hm1⟩
        · exact ⟨s.apply m, hok1, hr, Or.inr hlt⟩
      · obtain ⟨s1, hok1', hr1, hp⟩ := ih hok1 hch
        exact ⟨s1, hok1', hr.trans hr1, hp⟩

theorem oneOk_progress {s : KNState} {m : KNMove} (hok : s.okB = true)
    (hokm : s.oneOk m = true)
    (hp : (s.apply m).mateB = true ∨ (s.apply m).mu < s.mu) :
    ∃ s1, Progress s s1 := by
  obtain ⟨hfl, hok1⟩ := (oneOk_iff s m).mp hokm
  exact ⟨s.apply m, hok1, reachable_apply hok hfl, hp⟩

theorem tempo_eq_zero_of_whiteWork_pos {s : KNState} (ht : s.toMove = .white)
    (hp : 0 < whiteWork s.wk s.wn) : s.tempo = 0 := by
  unfold tempo
  rw [ht]
  refine if_neg ?_
  simpa only [beq_iff_eq] using Nat.ne_of_gt hp

theorem tempo_eq_zero_of_blackWork_pos {s : KNState} (ht : s.toMove = .black)
    (hp : 0 < blackWork s.bk s.bn) : s.tempo = 0 := by
  unfold tempo
  rw [ht]
  refine if_neg ?_
  simpa only [beq_iff_eq] using Nat.ne_of_gt hp

theorem inCheckB_black_after_whiteKing {s : KNState} {d : Square}
    (ht : s.toMove = .white) (hok : s.okB = true)
    (hs : fastKingStep s.wk d s.bk s.bn s.wn = true) :
    ({ s with toMove := .black, wk := d } : KNState).inCheckB .black = false := by
  obtain ⟨_, _, _, _, _, _, _, hnc⟩ := (okB_iff s).mp hok
  obtain ⟨_, _, _, _, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hs
  simp only [inCheckB, king, knight, Color.other, ht] at hnc
  rw [kingAttackedAt_eq_false] at hnc
  have hnk := ((kingAttackedAt_eq_false d s.bk s.bn).mp hsafe).1
  simp only [inCheckB, king, knight, Color.other]
  rw [kingAttackedAt_eq_false]
  exact ⟨fun hk => hnk (kingAttacks_symmetric.mp hk), hnc.2⟩

theorem inCheckB_white_after_blackKing {s : KNState} {d : Square}
    (ht : s.toMove = .black) (hok : s.okB = true)
    (hs : fastKingStep s.bk d s.wk s.wn s.bn = true) :
    ({ s with toMove := .white, bk := d } : KNState).inCheckB .white = false := by
  obtain ⟨_, _, _, _, _, _, _, hnc⟩ := (okB_iff s).mp hok
  obtain ⟨_, _, _, _, hsafe⟩ := (fastKingStep_iff _ _ _ _ _).mp hs
  simp only [inCheckB, king, knight, Color.other, ht] at hnc
  rw [kingAttackedAt_eq_false] at hnc
  have hnk := ((kingAttackedAt_eq_false d s.wk s.wn).mp hsafe).1
  simp only [inCheckB, king, knight, Color.other]
  rw [kingAttackedAt_eq_false]
  exact ⟨fun hk => hnk (kingAttacks_symmetric.mp hk), hnc.2⟩

theorem inCheckB_black_after_whiteKnight {s : KNState} {d : Square}
    (hok : s.okB = true) (hna : ¬ KnightAttacks d s.bk) :
    ({ s with toMove := .black, wn := d } : KNState).inCheckB .black = false := by
  obtain ⟨_, _, _, _, _, _, hka, _⟩ := (okB_iff s).mp hok
  simp only [inCheckB, king, knight, Color.other]
  rw [kingAttackedAt_eq_false]
  exact ⟨hka, hna⟩

theorem inCheckB_white_after_blackKnight {s : KNState} {d : Square}
    (hok : s.okB = true) (hna : ¬ KnightAttacks d s.wk) :
    ({ s with toMove := .white, bn := d } : KNState).inCheckB .white = false := by
  obtain ⟨_, _, _, _, _, _, hka, _⟩ := (okB_iff s).mp hok
  simp only [inCheckB, king, knight, Color.other]
  rw [kingAttackedAt_eq_false]
  exact ⟨fun hk => hka (kingAttacks_symmetric.mp hk), hna⟩

theorem mu_drop_of_whiteKing {s : KNState} {d : Square}
    (hm : s.mateB = false) (hf : s.finaleMu = none) (ht : s.toMove = .white)
    (hok : s.okB = true)
    (hstep : fastKingStep s.wk d s.bk s.bn s.wn = true)
    (h0 : kingMetric s.wk tgtWK ≠ 0)
    (hlt : kingMetric d tgtWK < kingMetric s.wk tgtWK) :
    (s.apply (.king d)).mateB = true ∨ (s.apply (.king d)).mu < s.mu := by
  set s1 := s.apply (.king d)
  have hw : whiteWork d s.wn < whiteWork s.wk s.wn := whiteWork_lt_of_kingMetric h0 hlt
  have hpos : 0 < whiteWork s.wk s.wn := Nat.lt_of_le_of_lt (Nat.zero_le _) hw
  have ht0 : s.tempo = 0 := tempo_eq_zero_of_whiteWork_pos ht hpos
  have hge : 16 ≤ s.mu := staging_mu_ge hm hf
  by_cases hm1 : s1.mateB = true
  · exact Or.inl hm1
  have hm1f : s1.mateB = false := eq_false_of_ne_true hm1
  match hf1 : s1.finaleMu with
  | some n =>
    have hmu1 : s1.mu = n := by
      unfold mu
      rw [if_neg (Bool.eq_false_iff.mp hm1f), hf1]
    have hn : n ≤ 8 := finaleMu_le hf1
    right
    omega
  | none =>
    have hchk1 : s1.inCheckB .black = false := by
      simpa only [s1, apply, ht] using inCheckB_black_after_whiteKing ht hok hstep
    have hs := mu_staging hm hf
    have hs1 := mu_staging hm1f hf1
    have hwk : s1.wk = d := by simp only [s1, apply, ht]
    have hbk : s1.bk = s.bk := by simp only [s1, apply, ht]
    have hwn : s1.wn = s.wn := by simp only [s1, apply, ht]
    have hbn : s1.bn = s.bn := by simp only [s1, apply, ht]
    have ht1c : s1.toMove = .black := by simp only [s1, apply, ht]
    rw [hwk, hbk, hwn, hbn, ht1c] at hs1
    have ht1 : s1.tempo ≤ 1 := tempo_le s1
    have hbonus : (if s1.inCheckB .black then 256 else 0) = 0 :=
      if_neg (Bool.eq_false_iff.mp hchk1)
    right
    omega

theorem mu_drop_of_blackKing {s : KNState} {d : Square}
    (hm : s.mateB = false) (hf : s.finaleMu = none) (ht : s.toMove = .black)
    (hok : s.okB = true)
    (hstep : fastKingStep s.bk d s.wk s.wn s.bn = true)
    (h0 : kingMetric s.bk tgtBK ≠ 0)
    (hlt : kingMetric d tgtBK < kingMetric s.bk tgtBK) :
    (s.apply (.king d)).mateB = true ∨ (s.apply (.king d)).mu < s.mu := by
  set s1 := s.apply (.king d)
  have hw : blackWork d s.bn < blackWork s.bk s.bn := blackWork_lt_of_kingMetric h0 hlt
  have hpos : 0 < blackWork s.bk s.bn := Nat.lt_of_le_of_lt (Nat.zero_le _) hw
  have ht0 : s.tempo = 0 := tempo_eq_zero_of_blackWork_pos ht hpos
  have hge : 16 ≤ s.mu := staging_mu_ge hm hf
  by_cases hm1 : s1.mateB = true
  · exact Or.inl hm1
  have hm1f : s1.mateB = false := eq_false_of_ne_true hm1
  match hf1 : s1.finaleMu with
  | some n =>
    have hmu1 : s1.mu = n := by
      unfold mu
      rw [if_neg (Bool.eq_false_iff.mp hm1f), hf1]
    have hn : n ≤ 8 := finaleMu_le hf1
    right
    omega
  | none =>
    have hchk1 : s1.inCheckB .white = false := by
      simpa only [s1, apply, ht] using inCheckB_white_after_blackKing ht hok hstep
    have hs := mu_staging hm hf
    have hs1 := mu_staging hm1f hf1
    have hwk : s1.wk = s.wk := by simp only [s1, apply, ht]
    have hbk : s1.bk = d := by simp only [s1, apply, ht]
    have hwn : s1.wn = s.wn := by simp only [s1, apply, ht]
    have hbn : s1.bn = s.bn := by simp only [s1, apply, ht]
    have ht1c : s1.toMove = .white := by simp only [s1, apply, ht]
    rw [hwk, hbk, hwn, hbn, ht1c] at hs1
    have ht1 : s1.tempo ≤ 1 := tempo_le s1
    have hbonus : (if s1.inCheckB .white then 256 else 0) = 0 :=
      if_neg (Bool.eq_false_iff.mp hchk1)
    right
    omega

theorem mu_drop_of_whiteKnight {s : KNState} {d : Square}
    (hm : s.mateB = false) (hf : s.finaleMu = none) (ht : s.toMove = .white)
    (hok : s.okB = true) (hna : ¬ KnightAttacks d s.bk)
    (h0 : nworkW s.wn ≠ 0) (hlt : nworkW d < nworkW s.wn) :
    (s.apply (.knight d)).mateB = true ∨ (s.apply (.knight d)).mu < s.mu := by
  set s1 := s.apply (.knight d)
  have hw : whiteWork s.wk d < whiteWork s.wk s.wn := whiteWork_lt_of_nwork h0 hlt
  have hpos : 0 < whiteWork s.wk s.wn := Nat.lt_of_le_of_lt (Nat.zero_le _) hw
  have ht0 : s.tempo = 0 := tempo_eq_zero_of_whiteWork_pos ht hpos
  have hge : 16 ≤ s.mu := staging_mu_ge hm hf
  by_cases hm1 : s1.mateB = true
  · exact Or.inl hm1
  have hm1f : s1.mateB = false := eq_false_of_ne_true hm1
  match hf1 : s1.finaleMu with
  | some n =>
    have hmu1 : s1.mu = n := by
      unfold mu
      rw [if_neg (Bool.eq_false_iff.mp hm1f), hf1]
    have hn : n ≤ 8 := finaleMu_le hf1
    right
    omega
  | none =>
    have hchk1 : s1.inCheckB .black = false := by
      simpa only [s1, apply, ht] using inCheckB_black_after_whiteKnight hok hna
    have hs := mu_staging hm hf
    have hs1 := mu_staging hm1f hf1
    have hwk : s1.wk = s.wk := by simp only [s1, apply, ht]
    have hbk : s1.bk = s.bk := by simp only [s1, apply, ht]
    have hwn : s1.wn = d := by simp only [s1, apply, ht]
    have hbn : s1.bn = s.bn := by simp only [s1, apply, ht]
    have ht1c : s1.toMove = .black := by simp only [s1, apply, ht]
    rw [hwk, hbk, hwn, hbn, ht1c] at hs1
    have ht1 : s1.tempo ≤ 1 := tempo_le s1
    have hbonus : (if s1.inCheckB .black then 256 else 0) = 0 :=
      if_neg (Bool.eq_false_iff.mp hchk1)
    right
    omega

theorem mu_drop_of_blackKnight {s : KNState} {d : Square}
    (hm : s.mateB = false) (hf : s.finaleMu = none) (ht : s.toMove = .black)
    (hok : s.okB = true) (hna : ¬ KnightAttacks d s.wk)
    (h0 : nworkB s.bn ≠ 0) (hlt : nworkB d < nworkB s.bn) :
    (s.apply (.knight d)).mateB = true ∨ (s.apply (.knight d)).mu < s.mu := by
  set s1 := s.apply (.knight d)
  have hw : blackWork s.bk d < blackWork s.bk s.bn := blackWork_lt_of_nwork h0 hlt
  have hpos : 0 < blackWork s.bk s.bn := Nat.lt_of_le_of_lt (Nat.zero_le _) hw
  have ht0 : s.tempo = 0 := tempo_eq_zero_of_blackWork_pos ht hpos
  have hge : 16 ≤ s.mu := staging_mu_ge hm hf
  by_cases hm1 : s1.mateB = true
  · exact Or.inl hm1
  have hm1f : s1.mateB = false := eq_false_of_ne_true hm1
  match hf1 : s1.finaleMu with
  | some n =>
    have hmu1 : s1.mu = n := by
      unfold mu
      rw [if_neg (Bool.eq_false_iff.mp hm1f), hf1]
    have hn : n ≤ 8 := finaleMu_le hf1
    right
    omega
  | none =>
    have hchk1 : s1.inCheckB .white = false := by
      simpa only [s1, apply, ht] using inCheckB_white_after_blackKnight hok hna
    have hs := mu_staging hm hf
    have hs1 := mu_staging hm1f hf1
    have hwk : s1.wk = s.wk := by simp only [s1, apply, ht]
    have hbk : s1.bk = s.bk := by simp only [s1, apply, ht]
    have hwn : s1.wn = s.wn := by simp only [s1, apply, ht]
    have hbn : s1.bn = d := by simp only [s1, apply, ht]
    have ht1c : s1.toMove = .white := by simp only [s1, apply, ht]
    rw [hwk, hbk, hwn, hbn, ht1c] at hs1
    have ht1 : s1.tempo ≤ 1 := tempo_le s1
    have hbonus : (if s1.inCheckB .white then 256 else 0) = 0 :=
      if_neg (Bool.eq_false_iff.mp hchk1)
    right
    omega

theorem reducingKingProgress_sound {s : KNState} (hok : s.okB = true)
    (h : s.reducingKingProgress = true) : ∃ s1, Progress s s1 := by
  by_cases hm : s.mateB = true
  · exact ⟨s, hok, Reachable.refl, Or.inl hm⟩
  have hm' : s.mateB = false := eq_false_of_ne_true hm
  simp only [reducingKingProgress, Bool.and_eq_true] at h
  obtain ⟨hhas, hfin⟩ := h
  have hf : s.finaleMu = none := by
    cases hfm : s.finaleMu <;> simp [hfm, Option.isNone] at hfin ⊢
  simp only [hasReducingKing, Bool.and_eq_true] at hhas
  obtain ⟨hcur, hany⟩ := hhas
  obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true] at hd
  obtain ⟨hstep, hlt⟩ := hd
  have hokm := oneOk_king_of_fastKingStep hok hstep
  have hp : (s.apply (.king d)).mateB = true ∨ (s.apply (.king d)).mu < s.mu := by
    cases ht : s.toMove with
    | white =>
      simp only [ht, king, knight, Color.other, beq_iff_eq, decide_eq_true_iff] at hcur hstep hlt
      exact mu_drop_of_whiteKing hm' hf ht hok hstep hcur hlt
    | black =>
      simp only [ht, king, knight, Color.other, beq_iff_eq, decide_eq_true_iff] at hcur hstep hlt
      exact mu_drop_of_blackKing hm' hf ht hok hstep hcur hlt
  exact oneOk_progress hok hokm hp

theorem reducingKnightProgress_sound {s : KNState} (hok : s.okB = true)
    (h : s.reducingKnightProgress = true) : ∃ s1, Progress s s1 := by
  by_cases hm : s.mateB = true
  · exact ⟨s, hok, Reachable.refl, Or.inl hm⟩
  have hm' : s.mateB = false := eq_false_of_ne_true hm
  simp only [reducingKnightProgress, Bool.and_eq_true] at h
  obtain ⟨hhas, hfin⟩ := h
  have hf : s.finaleMu = none := by
    cases hfm : s.finaleMu <;> simp [hfm, Option.isNone] at hfin ⊢
  simp only [hasReducingKnight, Bool.and_eq_true] at hhas
  obtain ⟨hcur, hany⟩ := hhas
  obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨hfl, hna⟩, hlt⟩ := hd
  have hokm := oneOk_knight_of_fastLegal hok hfl
  have hnaF : decide (KnightAttacks d (s.king s.toMove.other)) = false := by
    cases hdec : decide (KnightAttacks d (s.king s.toMove.other)) with
    | false => rfl
    | true =>
      simp only [hdec, Bool.not_true] at hna
      nomatch hna
  have hna' : ¬ KnightAttacks d (s.king s.toMove.other) :=
    decide_eq_false_iff_not.mp hnaF
  have hp : (s.apply (.knight d)).mateB = true ∨ (s.apply (.knight d)).mu < s.mu := by
    cases ht : s.toMove with
    | white =>
      simp only [ht, king, knight, Color.other, beq_iff_eq, decide_eq_true_iff] at hcur hlt hna'
      exact mu_drop_of_whiteKnight hm' hf ht hok hna' hcur hlt
    | black =>
      simp only [ht, king, knight, Color.other, beq_iff_eq, decide_eq_true_iff] at hcur hlt hna'
      exact mu_drop_of_blackKnight hm' hf ht hok hna' hcur hlt
  exact oneOk_progress hok hokm hp

theorem checkState_sound {s : KNState} (hok : s.okB = true) (h : s.checkState = true) :
    ∃ s1, Progress s s1 := by
  simp only [checkState, Bool.or_eq_true] at h
  rcases h with h3 | hch
  · rcases h3 with h2 | hn
    · rcases h2 with hm | hk
      · exact ⟨s, hok, Reachable.refl, Or.inl hm⟩
      · exact reducingKingProgress_sound hok hk
    · exact reducingKnightProgress_sound hok hn
  · obtain ⟨s1, hok1, hr, hp⟩ := chain_sound hok window hch
    exact ⟨s1, hok1, hr, hp⟩

theorem of_allSquares_all {p : Square → Bool} (h : allSquares.all p = true) (x : Square) :
    p x = true :=
  List.all_eq_true.mp h x (mem_allSquares x)

theorem stateCovered_of_not_okB {s : KNState} (h : s.okB = false) :
    stateCovered s = true := by
  simp [stateCovered, h]

theorem okB_false_of_wk_eq_bk {s : KNState} (h : s.wk = s.bk) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_kingAttacks {s : KNState} (h : KingAttacks s.wk s.bk) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_wk_eq_wn {s : KNState} (h : s.wk = s.wn) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_bk_eq_wn {s : KNState} (h : s.bk = s.wn) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_wk_eq_bn {s : KNState} (h : s.wk = s.bn) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_bk_eq_bn {s : KNState} (h : s.bk = s.bn) : s.okB = false := by
  simp [okB, h]

theorem okB_false_of_wn_eq_bn {s : KNState} (h : s.wn = s.bn) : s.okB = false := by
  simp [okB, h]

theorem pairCovered_sound {s : KNState} (h : pairCovered s.wk s.bk s.wn s.bn = true) :
    stateCovered s = true := by
  rcases s with ⟨c, wk, bk, wn, bn⟩
  have h' := Bool.and_eq_true_iff.mp h
  cases c with
  | white => exact h'.1
  | black => exact h'.2

theorem bool_or3 {a b c : Bool} (h : (a || b || c) = true) :
    (a = true ∨ b = true) ∨ c = true := by
  simpa only [Bool.or_eq_true] using h

theorem bool_or4 {a b c d : Bool} (h : (a || b || c || d) = true) :
    ((a = true ∨ b = true) ∨ c = true) ∨ d = true := by
  simpa only [Bool.or_eq_true] using h

/-- A true `checkSlice lo hi` covers every state whose white king file
lies in `[lo, hi)`. -/
theorem checkSlice_sound (lo hi : Nat) (hall : checkSlice lo hi = true) (s : KNState)
    (hlo : lo ≤ s.wk.file.val) (hhi : s.wk.file.val < hi) :
    stateCovered s = true := by
  have hwk : wkCovered lo hi s.wk = true := of_allSquares_all (p := wkCovered lo hi) hall s.wk
  have hlt : decide (s.wk.file.val < lo) = false :=
    decide_eq_false (Nat.not_lt.mpr hlo)
  have hge : decide (hi ≤ s.wk.file.val) = false :=
    decide_eq_false (Nat.not_le.mpr hhi)
  rw [wkCovered] at hwk
  simp only [hlt, hge, Bool.false_or] at hwk
  have hbk : kingsCovered s.wk s.bk = true :=
    of_allSquares_all (p := kingsCovered s.wk) hwk s.bk
  rw [kingsCovered] at hbk
  match bool_or3 hbk with
  | Or.inl (Or.inl heq) =>
    exact stateCovered_of_not_okB (okB_false_of_wk_eq_bk (beq_iff_eq.mp heq))
  | Or.inl (Or.inr hatt) =>
    exact stateCovered_of_not_okB (okB_false_of_kingAttacks (decide_eq_true_iff.mp hatt))
  | Or.inr hwns =>
    rw [knightsCovered] at hwns
    have hwn : wnCovered s.wk s.bk s.wn = true :=
      of_allSquares_all (p := wnCovered s.wk s.bk) hwns s.wn
    rw [wnCovered] at hwn
    match bool_or3 hwn with
    | Or.inl (Or.inl heq) =>
      exact stateCovered_of_not_okB (okB_false_of_wk_eq_wn (beq_iff_eq.mp heq))
    | Or.inl (Or.inr heq) =>
      exact stateCovered_of_not_okB (okB_false_of_bk_eq_wn (beq_iff_eq.mp heq))
    | Or.inr hbns =>
      have hbn : bnCovered s.wk s.bk s.wn s.bn = true :=
        of_allSquares_all (p := bnCovered s.wk s.bk s.wn) hbns s.bn
      rw [bnCovered] at hbn
      match bool_or4 hbn with
      | Or.inl (Or.inl (Or.inl heq)) =>
        exact stateCovered_of_not_okB (okB_false_of_wk_eq_bn (beq_iff_eq.mp heq))
      | Or.inl (Or.inl (Or.inr heq)) =>
        exact stateCovered_of_not_okB (okB_false_of_bk_eq_bn (beq_iff_eq.mp heq))
      | Or.inl (Or.inr heq) =>
        exact stateCovered_of_not_okB (okB_false_of_wn_eq_bn (beq_iff_eq.mp heq))
      | Or.inr hp =>
        exact pairCovered_sound hp

/-- The known mating picture is legal, mate, and covered. -/
theorem checkState_matePicture :
    let s : KNState := ⟨.black, Square.g6, Square.h8, Square.f7, Square.g8⟩
    (s.okB && s.mateB && s.checkState) = true := by
  native_decide

/-- The black-to-move staging net is legal and covered. -/
theorem checkState_assembledBlack :
    let s : KNState := ⟨.black, Square.g6, Square.f8, Square.e5, ⟨7, 5⟩⟩
    (s.okB && s.checkState) = true := by
  native_decide

end KNState

namespace Position

theorem exists_knState_of_kingKnights {p : Position} (hv : Valid p)
    (h : IsKingKnights p) : ∃ s : KNState, s.okB = true ∧ s.toPosition = p := by
  obtain ⟨wk, bk, wn, bn, h1, h2, h3, h4, h5, h6, hna, hboard, hc, he⟩ := h
  refine ⟨⟨p.toMove, wk, bk, wn, bn⟩, ?_, ?_⟩
  · rw [KNState.okB_iff]
    refine ⟨h1, h2, h3, h4, h5, h6, hna, ?_⟩
    have hnc := hv.2.1
    rw [hboard] at hnc
    have key : ∀ c : Color,
        (Board.kingsKnightsBoard wk bk wn bn).kingIsAttacked c.other = false →
          KNState.inCheckB ⟨c, wk, bk, wn, bn⟩ c.other = false := by
      intro c hc'
      cases c
      · rw [Color.other_white, KNState.kingIsAttacked_black_eq wk bk wn bn h1 h2 h3 h4 h5 h6]
          at hc'
        exact hc'
      · rw [Color.other_black, KNState.kingIsAttacked_white_eq wk bk wn bn h1 h2 h3 h4 h5 h6]
          at hc'
        exact hc'
    exact key p.toMove hnc
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

/-- The engineered mating line of a king-and-knight versus king-and-knight
position; `[]` for other positions. -/
def kingKnightsMatingLine (p : Position) : List Move :=
  match KNState.ofPosition? p with
  | some s => s.matingLine
  | none => []

/-! ### Example: kings on `e1` and `e8`, knights on `b1` and `b8` -/

/-- White king on `e1`, black king on `e8`, white knight on `b1`, black
knight on `b8`, White to move. -/
def kingKnightsStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.b1 then some { color := .white, kind := .knight }
    else if s = Square.b8 then some { color := .black, kind := .knight }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingKnightsStart_isValid : isValid kingKnightsStart = true := by
  native_decide

theorem kingKnightsStart_valid : Valid kingKnightsStart :=
  (isValid_eq_true_iff _).mp kingKnightsStart_isValid

theorem kingKnightsStart_isKingKnights : IsKingKnights kingKnightsStart :=
  isKingKnights_of_valid kingKnightsStart_valid (by native_decide)
    ⟨Square.b1, by native_decide⟩ ⟨Square.b8, by native_decide⟩

/-! ### Example: the known mating picture -/

/-- Black to move is checkmated: king `h8`, knight `g8`, white king `g6`,
white knight `f7`. -/
def kingKnightsMate : Position where
  board := fun s =>
    if s = Square.g6 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.f7 then some { color := .white, kind := .knight }
    else if s = Square.g8 then some { color := .black, kind := .knight }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem kingKnightsMate_isValid : isValid kingKnightsMate = true := by
  native_decide

theorem kingKnightsMate_inCheckmate : kingKnightsMate.inCheckmate = true := by
  native_decide

theorem kingKnightsMate_CheckmateReachable : CheckmateReachable kingKnightsMate :=
  checkmateReachable_of_inCheckmate
    ((inCheckmate_eq_true_iff _).mp kingKnightsMate_inCheckmate)

end Position

end Chess
