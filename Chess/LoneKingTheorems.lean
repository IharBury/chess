import Chess.LoneKingMaterial
import Chess.KingBishops

/-!
# Lone king versus arbitrary material: soundness and completeness

`Position.loneKingCheckmateReachable` answers `true` only when it has a
proof in hand: either the position is a recognized king-and-queen,
king-and-rook, or king-and-pawn ending whose state is not dead, or the
engineered line has been checked to be legal and to end in checkmate. So
a `true` answer is sound for every valid position
(`loneKingCheckmateReachable_sound`).

For valid positions with at most three pieces and no castling rights the
answer is also complete (`loneKingCheckmateReachable_iff_of_card_le_three`):
the two-king, lone-minor-piece, and same-color-bishop endings are dead, and
the queen, rook, and pawn endings are decided by their proven state
machines. This gives a `Decidable` instance for `CheckmateReachable` on
those positions.

With more material a `false` answer only reports that the engineered line
did not succeed; it is not a proof that the position is dead.
-/

namespace Chess

namespace Position

/-! ### A recognized three-piece state describes the position -/

theorem kq_ofPositionBlack?_fields {p : Position} {s : KQState}
    (h : KQState.ofPositionBlack? p = some s) :
    p.castling = ∅ ∧ p.enPassant = none := by
  unfold KQState.ofPositionBlack? at h
  split at h
  · split_ifs at h with hcond
    have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
    have ⟨_, hcst⟩ := Bool.and_eq_true_iff.mp hrest
    exact ⟨of_decide_eq_true hcst, of_decide_eq_true hep⟩
  · cases h

theorem kr_ofPositionBlack?_fields {p : Position} {s : KRState}
    (h : KRState.ofPositionBlack? p = some s) :
    p.castling = ∅ ∧ p.enPassant = none := by
  unfold KRState.ofPositionBlack? at h
  split at h
  · split_ifs at h with hcond
    have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
    have ⟨_, hcst⟩ := Bool.and_eq_true_iff.mp hrest
    exact ⟨of_decide_eq_true hcst, of_decide_eq_true hep⟩
  · cases h

theorem kp_ofPositionBlack?_fields {p : Position} {s : KPState}
    (h : KPState.ofPositionBlack? p = some s) :
    p.castling = ∅ ∧ p.enPassant = none := by
  unfold KPState.ofPositionBlack? at h
  split at h
  · split_ifs at h with hcond
    have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
    have ⟨_, hcst⟩ := Bool.and_eq_true_iff.mp hrest
    exact ⟨of_decide_eq_true hcst, of_decide_eq_true hep⟩
  · cases h

/-- A position recognized as a king-and-queen state is one. -/
theorem isKingAndQueen_of_ofPosition?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPosition? p = some s) : IsKingAndQueen p := by
  unfold KQState.ofPosition? at h
  split at h
  · rename_i s' hW
    obtain ⟨hok, hpos⟩ := kq_ofPositionWhite?_eq_some hW
    rw [← hpos]
    exact KQState.toPosition_isKingAndQueen hok
  · obtain ⟨hok, hpos⟩ := kq_ofPositionBlack?_eq_some h
    obtain ⟨hc, he⟩ := kq_ofPositionBlack?_fields h
    have hq : IsKingAndQueen p.rot180 := hpos ▸ KQState.toPosition_isKingAndQueen hok
    have hq' := hq.rot180
    rwa [rot180_involutive hc he] at hq'

/-- A position recognized as a king-and-rook state is one. -/
theorem isKingAndRook_of_ofPosition?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPosition? p = some s) : IsKingAndRook p := by
  unfold KRState.ofPosition? at h
  split at h
  · rename_i s' hW
    obtain ⟨hok, hpos⟩ := ofPositionWhite?_eq_some hW
    rw [← hpos]
    exact KRState.toPosition_isKingAndRook hok
  · obtain ⟨hok, hpos⟩ := ofPositionBlack?_eq_some h
    obtain ⟨hc, he⟩ := kr_ofPositionBlack?_fields h
    have hr : IsKingAndRook p.rot180 := hpos ▸ KRState.toPosition_isKingAndRook hok
    have hr' := hr.rot180
    rwa [rot180_involutive hc he] at hr'

/-- A position recognized as a king-and-pawn state is one. -/
theorem isKingAndPawn_of_ofPosition?_eq_some {p : Position} {s : KPState}
    (h : KPState.ofPosition? p = some s) : IsKingAndPawn p := by
  unfold KPState.ofPosition? at h
  split at h
  · rename_i s' hW
    obtain ⟨hok, hpos⟩ := kp_ofPositionWhite?_eq_some hW
    rw [← hpos]
    exact KPState.toPosition_isKingAndPawn hok
  · obtain ⟨hok, hpos⟩ := kp_ofPositionBlack?_eq_some h
    obtain ⟨hc, he⟩ := kp_ofPositionBlack?_fields h
    have hp : IsKingAndPawn p.rot180 := hpos ▸ KPState.toPosition_isKingAndPawn hok
    have hp' := hp.rot180
    rwa [rot180_involutive hc he] at hp'

/-! ### Soundness -/

/-- A `true` answer is backed either by a proven three-piece ending or by
a legal line that has been checked to end in checkmate. -/
theorem loneKingCheckmateReachable_sound {p : Position} (hv : Valid p)
    (h : loneKingCheckmateReachable p = true) : CheckmateReachable p := by
  unfold loneKingCheckmateReachable at h
  split at h
  · rename_i s hs
    obtain ⟨hok, hpos⟩ := kq_ofPosition?_eq_some hs
    exact ((isKingAndQueen_of_ofPosition?_eq_some hs).checkmateReachable_iff_deadB hv hok
      hpos).mpr (by simpa using h)
  · split at h
    · rename_i s hs
      obtain ⟨hok, hpos⟩ := ofPosition?_eq_some hs
      exact ((isKingAndRook_of_ofPosition?_eq_some hs).checkmateReachable_iff_deadB hv hok
        hpos).mpr (by simpa using h)
    · split at h
      · rename_i s hs
        obtain ⟨hok, hpos⟩ := kp_ofPosition?_eq_some hs
        exact ((isKingAndPawn_of_ofPosition?_eq_some hs).checkmateReachable_iff_deadB hv hok
          hpos).mpr (by simpa using h)
      · simp only [pathLegalN_eq, playSeqN_eq, Bool.and_eq_true] at h
        exact checkmateReachable_of_legalSeq ((pathLegal_iff _ _).mp h.1)
          ((inCheckmate_eq_true_iff _).mp h.2)

/-! ### Three pieces: the pawn ending from validity -/

/-- A valid position with exactly three occupied squares, one of them a
pawn, and no remaining castling rights, holds only the two kings and that
pawn, with the kings not adjacent. -/
theorem isKingAndPawn_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hpawn : ∃ s c, p.board s = some { color := c, kind := .pawn })
    (hcstl : p.castling = ∅) :
    IsKingAndPawn p := by
  obtain ⟨hbv, hopp, _, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨ps, c, hps⟩ := hpawn
  have hwking : p.board wk = some { color := .white, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
  have hbking : p.board bk = some { color := .black, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
  have hwk_bk : wk ≠ bk := by
    intro heq
    rw [heq] at hwking
    cases hwking.symm.trans hbking
  have hwk_ps : wk ≠ ps := by
    intro heq
    rw [heq] at hwking
    exact some_king_ne_pawn (hwking.symm.trans hps)
  have hbk_ps : bk ≠ ps := by
    intro heq
    rw [heq] at hbking
    exact some_king_ne_pawn (hbking.symm.trans hps)
  have hoccEq : p.board.occupied = {wk, bk, ps} := by
    have hsub : ({wk, bk, ps} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · simp [Board.mem_occupied, h, hwking]
      · simp [Board.mem_occupied, h, hbking]
      · simp [Board.mem_occupied, h, hps]
    have hcard : ({wk, bk, ps} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_ps]
      · simp [hwk_bk, hwk_ps]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsPawnBoard wk bk ps c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsPawnBoard_white]
      exact hwking
    · by_cases hb : s = bk
      · rw [hb, Board.kingsPawnBoard_black wk bk ps c hwk_bk]
        exact hbking
      · by_cases hs : s = ps
        · rw [hs, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps]
          exact hps
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsPawnBoard_other wk bk ps s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsPawnBoard_kingIsAttacked_black wk bk ps c
          hwk_bk hwk_ps hbk_ps).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsPawnBoard_kingIsAttacked_white wk bk ps c
          hwk_bk hwk_ps hbk_ps).mpr (Or.inl (kingAttacks_symmetric.mp hk))
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
  -- The only pawn has one color, so no en passant capture is available.
  have hpawnColor : ∀ s d, p.board s = some { color := d, kind := .pawn } → d = c := by
    intro s d hsd
    have hmem : s ∈ p.board.occupied := by
      simp [Board.mem_occupied, hsd]
    rw [hoccEq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hsq | hsq | hsq
    · rw [hsq, hwking] at hsd
      cases some_king_ne_pawn hsd
    · rw [hsq, hbking] at hsd
      cases some_king_ne_pawn hsd
    · rw [hsq, hps] at hsd
      simpa using hsd.symm
  have he : p.enPassant = none := by
    cases hep' : p.enPassant with
    | none => rfl
    | some ep =>
      obtain ⟨_, hland, hcap⟩ :=
        (enPassantOk_some p ep hep').mp (by simpa [hep'] using hep)
      obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp hcap
      have h₁ := hpawnColor _ _ ((hasPawn_eq_true_iff _ _ _).mp hs)
      have h₂ := hpawnColor _ _ ((hasPawn_eq_true_iff _ _ _).mp hland)
      rw [← h₁] at h₂
      exact (Color.other_ne _ h₂).elim
  exact ⟨wk, bk, ps, c, hwk_bk, hwk_ps, hbk_ps, hna, hboard, hcstl, he⟩

/-! ### Three pieces: the third piece -/

/-- A valid position with three occupied squares holds a piece besides the
two kings. -/
theorem exists_nonKing_of_card_eq_three {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3) :
    ∃ s c k, p.board s = some { color := c, kind := k } ∧ k ≠ .king := by
  obtain ⟨hbv, _, _, _⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  have hwking : p.board wk = some { color := .white, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
  have hbking : p.board bk = some { color := .black, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
  have hsub : ({wk, bk} : Finset Square) ⊆ p.board.occupied := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h
    · simp [Board.mem_occupied, h, hwking]
    · simp [Board.mem_occupied, h, hbking]
  have hlt : ({wk, bk} : Finset Square).card < p.board.occupied.card := by
    have := Finset.card_le_two (a := wk) (b := bk)
    omega
  obtain ⟨s, hs, hns⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hns
  obtain ⟨hsw, hsb⟩ := hns
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp ((Board.mem_occupied _ _).mp hs)
  rcases q with ⟨d, k⟩
  refine ⟨s, d, k, hq, ?_⟩
  intro hk
  subst hk
  cases d with
  | white =>
    have : s ∈ p.board.kingSquares .white := (Board.mem_kingSquares _ _ _).mpr hq
    rw [hwk] at this
    exact hsw (Finset.mem_singleton.mp this)
  | black =>
    have : s ∈ p.board.kingSquares .black := (Board.mem_kingSquares _ _ _).mpr hq
    rw [hbk] at this
    exact hsb (Finset.mem_singleton.mp this)

/-! ### Completeness for at most three pieces -/

theorem kq_ofPosition?_eq_none_of_not {p : Position} (h : ¬ IsKingAndQueen p) :
    KQState.ofPosition? p = none := by
  cases hs : KQState.ofPosition? p with
  | none => rfl
  | some s => exact (h (isKingAndQueen_of_ofPosition?_eq_some hs)).elim

theorem kr_ofPosition?_eq_none_of_not {p : Position} (h : ¬ IsKingAndRook p) :
    KRState.ofPosition? p = none := by
  cases hs : KRState.ofPosition? p with
  | none => rfl
  | some s => exact (h (isKingAndRook_of_ofPosition?_eq_some hs)).elim

/-- On a king-and-queen versus king position the answer is the state's
verdict. -/
theorem loneKingCheckmateReachable_of_isKingAndQueen {p : Position} (hv : Valid p)
    (h : IsKingAndQueen p) :
    loneKingCheckmateReachable p = true ↔ CheckmateReachable p := by
  obtain ⟨s, hs, hok, hpos⟩ := kq_ofPosition?_complete hv h
  rw [h.checkmateReachable_iff_deadB hv hok hpos]
  unfold loneKingCheckmateReachable
  rw [hs]
  simp

/-- On a king-and-rook versus king position the answer is the state's
verdict. -/
theorem loneKingCheckmateReachable_of_isKingAndRook {p : Position} (hv : Valid p)
    (h : IsKingAndRook p) :
    loneKingCheckmateReachable p = true ↔ CheckmateReachable p := by
  obtain ⟨s, hs, hok, hpos⟩ := ofPosition?_complete hv h
  rw [h.checkmateReachable_iff_deadB hv hok hpos]
  unfold loneKingCheckmateReachable
  rw [kq_ofPosition?_eq_none_of_not h.not_IsKingAndQueen, hs]
  simp

/-- On a king-and-pawn versus king position the answer is the state's
verdict. -/
theorem loneKingCheckmateReachable_of_isKingAndPawn {p : Position} (hv : Valid p)
    (h : IsKingAndPawn p) :
    loneKingCheckmateReachable p = true ↔ CheckmateReachable p := by
  obtain ⟨s, hs, hok, hpos⟩ := kp_ofPosition?_complete hv h
  rw [h.checkmateReachable_iff_deadB hv hok hpos]
  unfold loneKingCheckmateReachable
  rw [kq_ofPosition?_eq_none_of_not h.not_IsKingAndQueen,
    kr_ofPosition?_eq_none_of_not h.not_IsKingAndRook, hs]
  simp

/-- King and bishop versus king never reaches checkmate. -/
theorem IsKingAndBishop.not_checkmateReachable {p : Position} (h : IsKingAndBishop p) :
    ¬ CheckmateReachable p :=
  fun ⟨_, hr, hm⟩ => not_InCheckmate_of_kb_or_tk (h.of_reachable hr) hm

/-- King and knight versus king never reaches checkmate. -/
theorem IsKingAndKnight.not_checkmateReachable {p : Position} (h : IsKingAndKnight p) :
    ¬ CheckmateReachable p := by
  intro ⟨_, hr, hm⟩
  rcases h.of_reachable hr with hq | hq
  · exact hq.not_InCheckmate hm
  · exact hq.not_InCheckmate hm

/-- A valid position has at least the two kings on the board. -/
theorem two_le_card_occupied {p : Position} (hv : Valid p) : 2 ≤ p.board.occupied.card := by
  obtain ⟨hbv, _, _, _⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  have hwking : p.board wk = some { color := .white, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
  have hbking : p.board bk = some { color := .black, kind := .king } :=
    (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
  have hwk_bk : wk ≠ bk := by
    intro heq
    rw [heq] at hwking
    cases hwking.symm.trans hbking
  have hsub : ({wk, bk} : Finset Square) ⊆ p.board.occupied := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h
    · simp [Board.mem_occupied, h, hwking]
    · simp [Board.mem_occupied, h, hbking]
  have hcard : ({wk, bk} : Finset Square).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hwk_bk]), Finset.card_singleton]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- For valid positions with at most three pieces and no castling rights,
`loneKingCheckmateReachable` decides `CheckmateReachable`. -/
theorem loneKingCheckmateReachable_iff_of_card_le_three {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card ≤ 3) (hc : p.castling = ∅) :
    CheckmateReachable p ↔ loneKingCheckmateReachable p = true := by
  refine ⟨fun hcr => ?_, loneKingCheckmateReachable_sound hv⟩
  have hge := two_le_card_occupied hv
  rcases Nat.lt_or_ge p.board.occupied.card 3 with hlt | hge3
  · have h2 : p.board.occupied.card = 2 := by omega
    exact ((deadPosition_of_isTwoKings (isTwoKings_of_valid hv h2)) _ hcr.choose_spec.1
      hcr.choose_spec.2).elim
  · have h3 : p.board.occupied.card = 3 := by omega
    obtain ⟨s, c, k, hs, hk⟩ := exists_nonKing_of_card_eq_three hv h3
    cases k with
    | king => exact (hk rfl).elim
    | queen =>
      exact (loneKingCheckmateReachable_of_isKingAndQueen hv
        (isKingAndQueen_of_valid hv h3 ⟨s, c, hs⟩ hc)).mpr hcr
    | rook =>
      exact (loneKingCheckmateReachable_of_isKingAndRook hv
        (isKingAndRook_of_valid hv h3 ⟨s, c, hs⟩ hc)).mpr hcr
    | pawn =>
      exact (loneKingCheckmateReachable_of_isKingAndPawn hv
        (isKingAndPawn_of_valid hv h3 ⟨s, c, hs⟩ hc)).mpr hcr
    | bishop =>
      exact ((isKingAndBishop_of_valid hv h3 ⟨s, c, hs⟩).not_checkmateReachable hcr).elim
    | knight =>
      exact ((isKingAndKnight_of_valid hv h3 ⟨s, c, hs⟩).not_checkmateReachable hcr).elim

/-- Decides whether checkmate is reachable from a valid position with at
most three pieces and no castling rights. -/
def loneKingCheckmateReachableDecidable (p : Position) (hv : Valid p)
    (hocc : p.board.occupied.card ≤ 3) (hc : p.castling = ∅) :
    Decidable (CheckmateReachable p) :=
  decidable_of_iff (loneKingCheckmateReachable p = true)
    (loneKingCheckmateReachable_iff_of_card_le_three hv hocc hc).symm

/-! ### Deadness: soundness of `loneKingDead` -/

/-- A reachable position is the start itself or is reached through a first
legal move. -/
theorem Reachable.eq_or_exists_first {p q : Position} (hr : Reachable p q) :
    q = p ∨ ∃ m, LegalMove p m ∧ Reachable (p.play m) q := by
  induction hr with
  | refl => exact Or.inl rfl
  | step m _ hleg ih =>
    rcases ih with rfl | ⟨m₀, hl₀, hr₀⟩
    · exact Or.inr ⟨m, hleg, Reachable.refl⟩
    · exact Or.inr ⟨m₀, hl₀, Reachable.step m hr₀ hleg⟩

/-- A position that is not checkmate and all of whose legal moves lead to
dead positions is dead. -/
theorem deadPosition_of_forall_legalMove {p : Position} (h₀ : ¬ InCheckmate p)
    (h : ∀ m, LegalMove p m → DeadPosition (p.play m)) : DeadPosition p := by
  intro q hr hm
  rcases hr.eq_or_exists_first with rfl | ⟨m, hl, hr'⟩
  · exact h₀ hm
  · exact h m hl q hr' hm

theorem LoneKing.mem_candidateMoves_of_legalMove {p : Position} {m : Move}
    (h : LegalMove p m) : m ∈ LoneKing.candidateMoves p := by
  unfold LegalMove isLegalMove at h
  rcases m with ⟨src, dst, pr⟩
  simp only at h
  split at h
  · cases h
  · rename_i piece hpiece
    have hcolor : (piece.color == p.toMove) = true := by
      simp only [Bool.and_eq_true] at h
      exact h.1.1.1
    unfold LoneKing.candidateMoves
    simp only [List.mem_flatMap, List.mem_filter, List.mem_map]
    refine ⟨src, ⟨KQState.mem_allSquares src, ?_⟩, dst, KQState.mem_allSquares dst, pr, ?_,
      rfl⟩
    · simp [hpiece, hcolor]
    · rcases pr with _ | k
      · simp [LoneKing.promotionFields]
      · cases k <;> simp [LoneKing.promotionFields]

theorem LoneKing.deadLeaf_sound {p : Position} (h : LoneKing.deadLeaf p = true) :
    DeadPosition p := by
  unfold LoneKing.deadLeaf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hv, hocc⟩, hc⟩, hnr⟩ := h
  rw [DeadPosition_iff_not_CheckmateReachable,
    loneKingCheckmateReachable_iff_of_card_le_three ((isValid_eq_true_iff p).mp hv) hocc hc,
    hnr]
  exact Bool.false_ne_true

theorem LoneKing.deadWithin_sound :
    ∀ (fuel : Nat) (p : Position), LoneKing.deadWithin fuel p = true → DeadPosition p := by
  intro fuel
  induction fuel with
  | zero => exact fun p h => LoneKing.deadLeaf_sound h
  | succ fuel ih =>
    intro p h
    unfold LoneKing.deadWithin at h
    rcases Bool.or_eq_true_iff.mp h with hleaf | hrec
    · exact LoneKing.deadLeaf_sound hleaf
    · obtain ⟨hnm, hall⟩ := Bool.and_eq_true_iff.mp hrec
      refine deadPosition_of_forall_legalMove ?_ fun m hm => ?_
      · intro hm
        exact Bool.false_ne_true
          ((Bool.not_eq_true' _).mp hnm ▸ (inCheckmate_eq_true_iff p).mpr hm)
      · have hmem := LoneKing.mem_candidateMoves_of_legalMove hm
        have := List.all_eq_true.mp hall m hmem
        rcases Bool.or_eq_true_iff.mp this with hill | hdead
        · exact absurd hm (fun hl => Bool.false_ne_true ((Bool.not_eq_true' _).mp hill ▸ hl))
        · rw [normalize_eq] at hdead
          exact ih _ hdead

/-- A position recognized as dead is dead. No validity hypothesis is
needed: the leaves check validity themselves. -/
theorem loneKingDead_sound {p : Position} (h : loneKingDead p = true) : DeadPosition p := by
  unfold loneKingDead at h
  rw [normalize_eq] at h
  exact LoneKing.deadWithin_sound _ _ h

/-! ### The exhaustive fallback

`LoneKing.explore` answers `true` only at a position from which checkmate
is reachable (`explore_true`), and `false` only after closing off every
position reachable from the start: each is recognized as dead or is not
checkmate with all its legal moves leading to positions seen
(`explore_false`). Positions recognized as dead are dead indeed, the lone
king keeping its shape along every line (`deadNode_sound`). -/

namespace LoneKing

open Chess.LoneKing

theorem mem_successors {q r : Position} :
    r ∈ successors q ↔ ∃ m, LegalMove q m ∧ r = q.play m := by
  unfold successors
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨m, _, hm⟩
    split at hm
    · rename_i hleg
      rw [Option.some.injEq] at hm
      exact ⟨m, hleg, by rw [← hm, normalize_eq]⟩
    · cases hm
  · rintro ⟨m, hleg, rfl⟩
    exact ⟨m, mem_candidateMoves_of_legalMove hleg, by
      rw [if_pos (show q.isLegalMove m = true from hleg), normalize_eq]⟩

/-- A checked engineered line proves checkmate reachable. -/
theorem probeLive_sound {q : Position} (h : probeLive q = true) : CheckmateReachable q := by
  unfold probeLive at h
  simp only [pathLegalN_eq, playSeqN_eq, Bool.and_eq_true] at h
  exact checkmateReachable_of_legalSeq ((pathLegal_iff _ _).mp h.1)
    ((inCheckmate_eq_true_iff _).mp h.2)

theorem checkmateReachable_of_play {p : Position} {m : Move} (hleg : LegalMove p m)
    (h : CheckmateReachable (p.play m)) : CheckmateReachable p :=
  let ⟨q, hr, hm⟩ := h
  ⟨q, (Reachable.step m Reachable.refl hleg).trans hr, hm⟩

/-- In check without a successor is checkmate. -/
theorem inCheckmate_of_mateTest {q : Position}
    (h : (q.inCheck && (successors q).isEmpty) = true) : InCheckmate q := by
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h
  rw [InCheckmate_iff_forall_not_LegalMove]
  refine ⟨h.1, fun m hm => ?_⟩
  have := mem_successors.mpr ⟨m, hm, rfl⟩
  rw [h.2] at this
  cases this

/-- Not in check, or with a successor, is not checkmate. -/
theorem not_inCheckmate_of_mateTest {q : Position}
    (h : (q.inCheck && (successors q).isEmpty) = false) : ¬ InCheckmate q := by
  intro hm
  have hchk := inCheckmate_implies_inCheck ((inCheckmate_eq_true_iff q).mpr hm)
  have hnone := ((InCheckmate_iff_forall_not_LegalMove q).mp hm).2
  have hnil : successors q = [] := by
    cases hs : successors q with
    | nil => rfl
    | cons r rest =>
      obtain ⟨m, hleg, _⟩ := mem_successors.mp (hs ▸ List.mem_cons_self)
      exact (hnone m hleg).elim
  rw [hchk, hnil] at h
  cases h

theorem mem_fresh {V succ : List Position} {r : Position} :
    r ∈ fresh V succ ↔ r ∈ succ ∧ r ∉ V := by
  simp [fresh]

/-- `true` is answered only when checkmate is reachable from a position of
the work list. -/
theorem explore_true (c : Color) :
    ∀ V W, explore c V W = true → ∃ q ∈ W, CheckmateReachable q := by
  intro V W
  induction V, W using explore.induct c with
  | case1 V => intro h; rw [explore] at h; cases h
  | case2 V q W hlive => exact fun _ => ⟨q, List.mem_cons_self, probeLive_sound hlive⟩
  | case3 V q W hlive hdead ih =>
    intro h
    rw [explore, if_neg hlive, if_pos hdead] at h
    obtain ⟨r, hr, hcr⟩ := ih h
    exact ⟨r, List.mem_cons_of_mem q hr, hcr⟩
  | case4 V q W hlive hdead _ hmate =>
    exact fun _ => ⟨q, List.mem_cons_self, checkmateReachable_of_inCheckmate
      (inCheckmate_of_mateTest hmate)⟩
  | case5 V q W hlive hdead _ hmate ih =>
    intro h
    rw [explore, if_neg hlive, if_neg hdead, if_neg hmate] at h
    obtain ⟨r, hr, hcr⟩ := ih h
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_cons_of_mem q hr, hcr⟩
    · obtain ⟨m, hleg, rfl⟩ := mem_successors.mp (mem_fresh.mp hr).1
      exact ⟨q, List.mem_cons_self, checkmateReachable_of_play hleg hcr⟩

/-- A position of the seen list is closed off: recognized as dead, or not
checkmate with every legal move leading into the seen list. -/
def Closed (c : Color) (V : List Position) (q : Position) : Prop :=
  deadNode c q = true ∨ (¬ InCheckmate q ∧ ∀ m, LegalMove q m → q.play m ∈ V)

theorem Closed.mono {c : Color} {V V' : List Position} {q : Position} (h : Closed c V q)
    (hVV : ∀ r ∈ V, r ∈ V') : Closed c V' q := by
  rcases h with h | ⟨hnm, hsucc⟩
  · exact Or.inl h
  · exact Or.inr ⟨hnm, fun m hm => hVV _ (hsucc m hm)⟩

/-- `false` is answered only once every seen position is closed off. The
seen list contains the work list and consists of positions reachable from
`p`; every seen position not in the work list is already closed off. -/
theorem explore_false (c : Color) (p : Position) :
    ∀ V W, explore c V W = false → (∀ q ∈ W, q ∈ V) → (∀ q ∈ V, Reachable p q) →
      (∀ q ∈ V, q ∉ W → Closed c V q) →
      ∃ V', (∀ q ∈ V, q ∈ V') ∧ (∀ q ∈ V', Reachable p q) ∧ ∀ q ∈ V', Closed c V' q := by
  intro V W
  induction V, W using explore.induct c with
  | case1 V =>
    intro _ _ hreach hclosed
    exact ⟨V, fun q hq => hq, hreach, fun q hq => hclosed q hq (List.not_mem_nil)⟩
  | case2 V q W hlive =>
    intro h
    rw [explore, if_pos hlive] at h
    cases h
  | case3 V q W hlive hdead ih =>
    intro h hWV hreach hclosed
    rw [explore, if_neg hlive, if_pos hdead] at h
    refine ih h (fun r hr => hWV r (List.mem_cons_of_mem q hr)) hreach fun r hr hrW => ?_
    by_cases hrq : r = q
    · exact Or.inl (hrq ▸ hdead)
    · exact hclosed r hr fun hmem => (List.mem_cons.mp hmem).elim hrq hrW
  | case4 V q W hlive hdead _ hmate =>
    intro h
    rw [explore, if_neg hlive, if_neg hdead, if_pos hmate] at h
    cases h
  | case5 V q W hlive hdead _ hmate ih =>
    intro h hWV hreach hclosed
    rw [explore, if_neg hlive, if_neg hdead, if_neg hmate] at h
    have hqV : q ∈ V := hWV q List.mem_cons_self
    have hWV' : ∀ r ∈ W ++ fresh V (successors q), r ∈ V ++ fresh V (successors q) := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ (hWV r (List.mem_cons_of_mem q hr))
      · exact List.mem_append_right _ hr
    have hreach' : ∀ r ∈ V ++ fresh V (successors q), Reachable p r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hreach r hr
      · obtain ⟨m, hleg, rfl⟩ := mem_successors.mp (mem_fresh.mp hr).1
        exact Reachable.step m (hreach q hqV) hleg
    have hclosed' : ∀ r ∈ V ++ fresh V (successors q), r ∉ W ++ fresh V (successors q) →
        Closed c (V ++ fresh V (successors q)) r := by
      intro r hr hrW
      have hrV : r ∈ V := by
        rcases List.mem_append.mp hr with hr | hr
        · exact hr
        · exact (hrW (List.mem_append_right _ hr)).elim
      have hrW' : r ∉ W := fun h' => hrW (List.mem_append_left _ h')
      by_cases hrq : r = q
      · subst hrq
        refine Or.inr ⟨not_inCheckmate_of_mateTest (Bool.eq_false_iff.mpr hmate), fun m hm => ?_⟩
        have hsucc : r.play m ∈ successors r := mem_successors.mpr ⟨m, hm, rfl⟩
        by_cases hmem : r.play m ∈ V
        · exact List.mem_append_left _ hmem
        · exact List.mem_append_right _ (mem_fresh.mpr ⟨hsucc, hmem⟩)
      · exact (hclosed r hrV fun hmem => (List.mem_cons.mp hmem).elim hrq hrW').mono
          fun x hx => List.mem_append_left _ hx
    obtain ⟨V', hVV', hreach'', hclosed''⟩ := ih h hWV' hreach' hclosed'
    exact ⟨V', fun r hr => hVV' r (List.mem_append_left _ hr), hreach'', hclosed''⟩

/-- A start position of a closed-off list all of whose recognized-dead
members are dead is dead. -/
theorem deadPosition_of_closed {c : Color} {p : Position} {V' : List Position} (hp : p ∈ V')
    (hclosed : ∀ q ∈ V', Closed c V' q)
    (hdead : ∀ q ∈ V', deadNode c q = true → DeadPosition q) : DeadPosition p := by
  have key : ∀ q, Reachable p q → q ∈ V' ∨ ∃ d ∈ V', deadNode c d = true ∧ Reachable d q := by
    intro q hq
    induction hq with
    | refl => exact Or.inl hp
    | step m _ hleg ih =>
      rcases ih with hmem | ⟨d, hd, hdn, hrd⟩
      · rcases hclosed _ hmem with hdn | ⟨_, hsucc⟩
        · exact Or.inr ⟨_, hmem, hdn, Reachable.step m Reachable.refl hleg⟩
        · exact Or.inl (hsucc m hleg)
      · exact Or.inr ⟨d, hd, hdn, Reachable.step m hrd hleg⟩
  intro q hq hm
  rcases key q hq with hmem | ⟨d, hd, hdn, hrd⟩
  · rcases hclosed _ hmem with hdn | ⟨hnm, _⟩
    · exact hdead _ hmem hdn _ Reachable.refl hm
    · exact hnm hm
  · exact hdead d hd hdn q hrd hm

/-- A position recognized as dead is dead, provided the lone king has kept
its shape. -/
theorem deadNode_sound {c : Color} {q : Position} (hs : LoneShape c q)
    (h : deadNode c q = true) : DeadPosition q := by
  unfold deadNode at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (hleaf | hw) | hb
  · exact deadLeaf_sound hleaf
  · exact hs.deadPosition_of_onlyBishopsOn hw
  · exact hs.deadPosition_of_onlyBishopsOn hb

end LoneKing

/-! ### Deciding `CheckmateReachable` -/

/-- Under `HasLoneKing`, `loneColor` names a player with only a king. -/
theorem loneFor_loneColor {p : Position} (h : HasLoneKing p) : LoneFor (loneColor p) p := by
  unfold loneColor
  split_ifs with hb
  · exact hb
  · obtain ⟨c, hc⟩ := h
    cases c
    · exact hc
    · exact (hb hc).elim

/-- The verdict is correct for every valid position with a bare king. -/
theorem loneKingVerdict_iff {p : Position} (hv : Valid p) (h : HasLoneKing p) :
    loneKingVerdict p = true ↔ CheckmateReachable p := by
  unfold loneKingVerdict
  split_ifs with hr hd
  · exact ⟨fun _ => loneKingCheckmateReachable_sound hv hr, fun _ => rfl⟩
  · exact ⟨fun h => by simp at h, fun hc =>
      ((DeadPosition_iff_not_CheckmateReachable p).mp (loneKingDead_sound hd) hc).elim⟩
  · simp only [normalize_eq]
    constructor
    · intro he
      obtain ⟨q, hq, hcr⟩ := LoneKing.explore_true _ _ _ he
      rw [List.mem_singleton] at hq
      exact hq ▸ hcr
    · intro hcr
      by_contra he
      rw [Bool.not_eq_true] at he
      obtain ⟨V', hV, hreach, hclosed⟩ := LoneKing.explore_false _ p _ _ he (fun q hq => hq)
        (fun q hq => by rw [List.mem_singleton] at hq; exact hq ▸ Reachable.refl)
        (fun q hq hnq => (hnq hq).elim)
      have hs : LoneShape (loneColor p) p := LoneShape.of_valid hv (loneFor_loneColor h)
      exact (DeadPosition_iff_not_CheckmateReachable p).mp
        (LoneKing.deadPosition_of_closed (hV p (List.mem_singleton_self p)) hclosed
          fun q hq hdn => LoneKing.deadNode_sound (hs.of_reachable (hreach q hq)) hdn) hcr

/-- Decides whether checkmate is reachable from a valid position in which
one player has only a king, by evaluating `loneKingVerdict`. -/
def loneKingDecidable (p : Position) (hv : Valid p) (h : HasLoneKing p) :
    Decidable (CheckmateReachable p) :=
  decidable_of_iff (loneKingVerdict p = true) (loneKingVerdict_iff hv h)

/-- On a settled position the verdict is the engineered answer, without
exploration. -/
theorem loneKingVerdict_of_decided {p : Position} (h : loneKingDecided p = true) :
    loneKingVerdict p = loneKingCheckmateReachable p := by
  unfold loneKingVerdict
  unfold loneKingDecided at h
  split_ifs with hr hd
  · exact hr.symm
  · exact (Bool.eq_false_iff.mpr hr).symm
  · simp [hr, hd] at h

/-- Every valid position with at most three pieces and no castling rights
is settled. -/
theorem loneKingDecided_of_card_le_three {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card ≤ 3) (hc : p.castling = ∅) :
    loneKingDecided p = true := by
  unfold loneKingDecided
  cases hr : loneKingCheckmateReachable p
  · have hleaf : LoneKing.deadLeaf p = true := by
      unfold LoneKing.deadLeaf
      simp [(isValid_eq_true_iff p).mpr hv, hocc, hc, hr]
    have hdead : loneKingDead p = true := by
      unfold loneKingDead LoneKing.deadFuel
      rw [normalize_eq]
      simp [LoneKing.deadWithin, hleaf]
    simp [hdead]
  · rfl

/-! ### Examples

The engineered line is exercised on material that no earlier module
decides: two knights, bishop and knight, two bishops, a queen and a rook,
a rook with castling rights still recorded, a pawn blocked by its own
knight, a five-piece position with the lone king already cornered, and
Black as the strong side. In each case the line is legal and ends in
checkmate, so `loneKingCheckmateReachable` answers `true`, and by
`loneKingCheckmateReachable_sound` checkmate is reachable. -/

/-- A board from a list of squares and pieces. -/
def boardOfList (l : List (Square × Piece)) : Board := fun s =>
  (l.find? fun sp => sp.1 == s).map (·.2)

/-- White king `e1`, black king `e8`, white knights `b1` and `g1`, White to
move. -/
def loneKingKNN : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.b1, ⟨.white, .knight⟩), (Square.g1, ⟨.white, .knight⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKNN_isValid : isValid loneKingKNN = true := by
  native_decide

theorem loneKingKNN_reachable : loneKingCheckmateReachable loneKingKNN = true := by
  native_decide

theorem loneKingKNN_CheckmateReachable : CheckmateReachable loneKingKNN :=
  loneKingCheckmateReachable_sound ((isValid_eq_true_iff _).mp loneKingKNN_isValid)
    loneKingKNN_reachable

/-- White king `e1`, black king `e8`, white bishop `c1` (dark) and knight
`g1`, White to move. -/
def loneKingKBN : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.c1, ⟨.white, .bishop⟩), (Square.g1, ⟨.white, .knight⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKBN_isValid : isValid loneKingKBN = true := by
  native_decide

theorem loneKingKBN_reachable : loneKingCheckmateReachable loneKingKBN = true := by
  native_decide

theorem loneKingKBN_CheckmateReachable : CheckmateReachable loneKingKBN :=
  loneKingCheckmateReachable_sound ((isValid_eq_true_iff _).mp loneKingKBN_isValid)
    loneKingKBN_reachable

/-- White king `e1`, black king `e8`, white bishops `c1` and `f1`, White to
move. -/
def loneKingKBB : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.c1, ⟨.white, .bishop⟩), (Square.f1, ⟨.white, .bishop⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKBB_isValid : isValid loneKingKBB = true := by
  native_decide

theorem loneKingKBB_reachable : loneKingCheckmateReachable loneKingKBB = true := by
  native_decide

theorem loneKingKBB_CheckmateReachable : CheckmateReachable loneKingKBB :=
  loneKingCheckmateReachable_sound ((isValid_eq_true_iff _).mp loneKingKBB_isValid)
    loneKingKBB_reachable

/-- White king `e1`, black king `e8`, white queen `a1` and rook `h1`, White
to move: the rook is sacrificed and the queen mates. -/
def loneKingKQR : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.a1, ⟨.white, .queen⟩), (Square.h1, ⟨.white, .rook⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKQR_isValid : isValid loneKingKQR = true := by
  native_decide

theorem loneKingKQR_reachable : loneKingCheckmateReachable loneKingKQR = true := by
  native_decide

theorem loneKingKQR_CheckmateReachable : CheckmateReachable loneKingKQR :=
  loneKingCheckmateReachable_sound ((isValid_eq_true_iff _).mp loneKingKQR_isValid)
    loneKingKQR_reachable

/-- White king `e1`, black king `e8`, white rook `h1`, White to move, with
White's kingside castling right still recorded: not a `KRState`, so the
engineered line is used. -/
def loneKingKRCastling : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.h1, ⟨.white, .rook⟩)]
  toMove := .white
  castling := {⟨.white, .kingside⟩}
  enPassant := none

theorem loneKingKRCastling_isValid : isValid loneKingKRCastling = true := by
  native_decide

theorem loneKingKRCastling_reachable :
    loneKingCheckmateReachable loneKingKRCastling = true := by
  native_decide

theorem loneKingKRCastling_CheckmateReachable : CheckmateReachable loneKingKRCastling :=
  loneKingCheckmateReachable_sound
    ((isValid_eq_true_iff _).mp loneKingKRCastling_isValid) loneKingKRCastling_reachable

/-- White king `e1`, black king `e8`, white pawn `e2` blocked by the white
knight `e3`, White to move: the knight is sacrificed, the pawn promotes. -/
def loneKingKPN : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.e2, ⟨.white, .pawn⟩), (Square.e3, ⟨.white, .knight⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKPN_isValid : isValid loneKingKPN = true := by
  native_decide

theorem loneKingKPN_reachable : loneKingCheckmateReachable loneKingKPN = true := by
  native_decide

theorem loneKingKPN_CheckmateReachable : CheckmateReachable loneKingKPN :=
  loneKingCheckmateReachable_sound ((isValid_eq_true_iff _).mp loneKingKPN_isValid)
    loneKingKPN_reachable

/-- White king `c6`, black king `a8`, white queen `d5`, rook `e5`, and
knight `b2`, White to move. -/
def loneKingCornered : Position where
  board := boardOfList [(Square.c6, ⟨.white, .king⟩), (Square.a8, ⟨.black, .king⟩),
    (Square.d5, ⟨.white, .queen⟩), (Square.e5, ⟨.white, .rook⟩),
    (⟨1, 1⟩, ⟨.white, .knight⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingCornered_isValid : isValid loneKingCornered = true := by
  native_decide

theorem loneKingCornered_reachable :
    loneKingCheckmateReachable loneKingCornered = true := by
  native_decide

theorem loneKingCornered_CheckmateReachable : CheckmateReachable loneKingCornered :=
  loneKingCheckmateReachable_sound
    ((isValid_eq_true_iff _).mp loneKingCornered_isValid) loneKingCornered_reachable

/-- White king `e1`, black king `e8`, black bishop `c8` and knight `g8`,
Black to move: Black is the strong side. -/
def loneKingBlackBN : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.c8, ⟨.black, .bishop⟩), (Square.g8, ⟨.black, .knight⟩)]
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingBlackBN_isValid : isValid loneKingBlackBN = true := by
  native_decide

theorem loneKingBlackBN_reachable :
    loneKingCheckmateReachable loneKingBlackBN = true := by
  native_decide

theorem loneKingBlackBN_CheckmateReachable : CheckmateReachable loneKingBlackBN :=
  loneKingCheckmateReachable_sound
    ((isValid_eq_true_iff _).mp loneKingBlackBN_isValid) loneKingBlackBN_reachable

/-- White king `e1` alone against the black king `e8`, queen `d8`, rook
`a8`, bishop `f8`, knight `b8`, and pawns `a7` and `b7`, with Black's
queenside castling right recorded, White to move. The knight, rook,
bishop, and both pawns (after promotion) are given up before the queen
mates. -/
def loneKingBlackArmy : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.d8, ⟨.black, .queen⟩), (Square.a8, ⟨.black, .rook⟩),
    (Square.f8, ⟨.black, .bishop⟩), (Square.b8, ⟨.black, .knight⟩),
    (Square.a7, ⟨.black, .pawn⟩), (⟨1, 6⟩, ⟨.black, .pawn⟩)]
  toMove := .white
  castling := {⟨.black, .queenside⟩}
  enPassant := none

theorem loneKingBlackArmy_isValid : isValid loneKingBlackArmy = true := by
  native_decide

theorem loneKingBlackArmy_reachable :
    loneKingCheckmateReachable loneKingBlackArmy = true := by
  native_decide

theorem loneKingBlackArmy_CheckmateReachable : CheckmateReachable loneKingBlackArmy :=
  loneKingCheckmateReachable_sound
    ((isValid_eq_true_iff _).mp loneKingBlackArmy_isValid) loneKingBlackArmy_reachable

/-! Material that cannot mate is answered `false`; on three pieces this is
the complete verdict. -/

/-- White king `e1`, black king `e8`, white bishop `c1`, White to move. -/
def loneKingKB : Position where
  board := boardOfList [(Square.e1, ⟨.white, .king⟩), (Square.e8, ⟨.black, .king⟩),
    (Square.c1, ⟨.white, .bishop⟩)]
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingKB_isValid : isValid loneKingKB = true := by
  native_decide

theorem loneKingKB_not_reachable : loneKingCheckmateReachable loneKingKB = false := by
  native_decide

theorem loneKingKB_deadPosition : DeadPosition loneKingKB := by
  rw [DeadPosition_iff_not_CheckmateReachable,
    loneKingCheckmateReachable_iff_of_card_le_three
      ((isValid_eq_true_iff _).mp loneKingKB_isValid) (by native_decide) (by native_decide),
    loneKingKB_not_reachable]
  exact Bool.false_ne_true

/-- The same-color bishops of `kingBishopsSame` are also answered `false`,
in agreement with `kingBishopsSame_deadPosition`. -/
theorem kingBishopsSame_loneKing_not_reachable :
    loneKingCheckmateReachable kingBishopsSame = false := by
  native_decide

/-! `loneKingDecided` settles positions in both directions: the mating
examples above, and dead positions with more than three pieces recognized
through stalemate. -/

theorem loneKingKNN_decided : loneKingDecided loneKingKNN = true := by
  native_decide

theorem loneKingKNN_hasLoneKing : HasLoneKing loneKingKNN := by
  native_decide

/-- Checkmate is reachable from `loneKingKNN`, decided by `loneKingDecidable`. -/
theorem loneKingKNN_decide :
    @decide (CheckmateReachable loneKingKNN)
      (loneKingDecidable _ ((isValid_eq_true_iff _).mp loneKingKNN_isValid)
        loneKingKNN_hasLoneKing) = true := by
  native_decide

theorem loneKingBlackArmy_decided : loneKingDecided loneKingBlackArmy = true := by
  native_decide

/-- Black king `a8` stalemated by the white king `c7`, bishop `b6`, and pawn
`h2`, Black to move: four pieces, dead. -/
def loneKingStalemate : Position where
  board := boardOfList [(Square.a8, ⟨.black, .king⟩), (⟨2, 6⟩, ⟨.white, .king⟩),
    (Square.b6, ⟨.white, .bishop⟩), (⟨7, 1⟩, ⟨.white, .pawn⟩)]
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingStalemate_isValid : isValid loneKingStalemate = true := by
  native_decide

theorem loneKingStalemate_dead : loneKingDead loneKingStalemate = true := by
  native_decide

theorem loneKingStalemate_deadPosition : DeadPosition loneKingStalemate :=
  loneKingDead_sound loneKingStalemate_dead

/-- Black king `h8` in check from the white rook `g8`, with the white king
`f6` and bishop `d3` covering `g7` and `h7`, Black to move. The only legal
move captures the rook, leaving king and bishop against king: dead,
recognized one ply deep although five pieces stand on the board. -/
def loneKingForcedCapture : Position where
  board := boardOfList [(⟨7, 7⟩, ⟨.black, .king⟩), (⟨5, 5⟩, ⟨.white, .king⟩),
    (⟨3, 2⟩, ⟨.white, .bishop⟩), (Square.g8, ⟨.white, .rook⟩)]
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem loneKingForcedCapture_isValid : isValid loneKingForcedCapture = true := by
  native_decide

theorem loneKingForcedCapture_not_reachable :
    loneKingCheckmateReachable loneKingForcedCapture = false := by
  native_decide

theorem loneKingForcedCapture_dead : loneKingDead loneKingForcedCapture = true := by
  native_decide

theorem loneKingForcedCapture_deadPosition : DeadPosition loneKingForcedCapture :=
  loneKingDead_sound loneKingForcedCapture_dead

theorem loneKingForcedCapture_decided : loneKingDecided loneKingForcedCapture = true := by
  unfold loneKingDecided
  rw [loneKingForcedCapture_dead, Bool.or_true]

theorem loneKingForcedCapture_hasLoneKing : HasLoneKing loneKingForcedCapture := by
  native_decide

/-- Checkmate is not reachable from `loneKingForcedCapture`, decided by
`loneKingDecidable`. -/
theorem loneKingForcedCapture_decide :
    @decide (CheckmateReachable loneKingForcedCapture)
      (loneKingDecidable _ ((isValid_eq_true_iff _).mp loneKingForcedCapture_isValid)
        loneKingForcedCapture_hasLoneKing) = false := by
  native_decide

end Position

end Chess
