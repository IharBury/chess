import Chess.KingKnights

/-!
`mateB` of a legal king-and-knight state is checkmate. Proved from the
geometry of knight checks: the checking knight cannot be captured, king
flights are covered, and a knight hop cannot block a knight check.
-/

namespace Chess

theorem not_kingAttacks_of_knightAttacks {s t : Square} (h : KnightAttacks s t) :
    ¬ KingAttacks s t := by
  revert s t
  native_decide

theorem knightAttacks_symm {s t : Square} : KnightAttacks s t ↔ KnightAttacks t s := by
  revert s t
  native_decide

namespace Board

theorem ne_of_kingsKnightsBoard_eq_none {wk bk wn bn s : Square}
    (h : kingsKnightsBoard wk bk wn bn s = none) :
    s ≠ wk ∧ s ≠ bk ∧ s ≠ wn ∧ s ≠ bn := by
  unfold kingsKnightsBoard at h
  split_ifs at h with h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end Board

namespace KNState

open Position

theorem destOk_kingsKnightsBoard {p : Position} {m : Move} {wk bk wn bn : Square}
    (hboard : p.board = Board.kingsKnightsBoard wk bk wn bn)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = wn ∨ m.dst = bn := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsKnightsBoard wk bk wn bn m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsKnightsBoard at hdst
    split_ifs at hdst with h1 h2 h3 h4
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h4)

theorem kingKnights_legalMove_core {p : Position} {m : Move} {wk bk wn bn : Square}
    (hboard : p.board = Board.kingsKnightsBoard wk bk wn bn)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = wn ∨ m.dst = bn) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      p.board.attacks m.src m.dst = true ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .knight) ∧
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
    have hdstOr := destOk_kingsKnightsBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsKnightsBoard wk bk wn bn m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .knight := by
      have hsrc' := hsrc
      unfold Board.kingsKnightsBoard at hsrc'
      split_ifs at hsrc' with _h1 _h2 _h3 _h4
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inr rfl
      · cases hsrc'; exact Or.inr rfl
    have hpawn : (piece.kind == PieceKind.pawn) = false := by
      cases hkind with
      | inl hk => simp [hk]
      | inr hn => simp [hn]
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
      | inr hn =>
        simpa [hpawn, hn, Bool.and_eq_true, beq_iff_eq] using hifs
    exact ⟨hgeo.2, hdestOk, hdstOr, hsafe, hgeo.1, piece, rfl, hcol', hkind, hside⟩

theorem destOk_toMove_of_dst_whiteKnight {p : Position} {m : Move}
    {wk bk wn bn : Square}
    (hboard : p.board = Board.kingsKnightsBoard wk bk wn bn)
    (hwk_wn : wk ≠ wn) (hbk_wn : bk ≠ wn)
    (hdst : m.dst = wn) (hok : p.destOk m = true) :
    p.toMove = Color.black := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsKnightsBoard_whiteKnight wk bk wn bn hwk_wn hbk_wn] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem destOk_toMove_of_dst_blackKnight {p : Position} {m : Move}
    {wk bk wn bn : Square}
    (hboard : p.board = Board.kingsKnightsBoard wk bk wn bn)
    (hwk_bn : wk ≠ bn) (hbk_bn : bk ≠ bn) (hwn_bn : wn ≠ bn)
    (hdst : m.dst = bn) (hok : p.destOk m = true) :
    p.toMove = Color.white := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsKnightsBoard_blackKnight wk bk wn bn hwk_bn hbk_bn hwn_bn] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem play_board_of_src {p : Position} {m : Move} {piece : Piece}
    (h : p.board m.src = some piece) : (p.play m).board = p.boardAfter m piece := by
  rw [play_of_some p m h]

theorem inCheck_knightAttacks_white {s : KNState} (hok : s.okB = true)
    (_ht : s.toMove = .white) (hchk : kingAttackedAt s.wk s.bk s.bn = true) :
    KnightAttacks s.bn s.wk := by
  have hna := (okB_iff s).mp hok |>.2.2.2.2.2.2.1
  rcases (kingAttackedAt_iff s.wk s.bk s.bn).mp hchk with hk | hn
  · exact (hna (KingAttacks_symm.mp hk)).elim
  · exact hn

theorem inCheck_knightAttacks_black {s : KNState} (hok : s.okB = true)
    (_ht : s.toMove = .black) (hchk : kingAttackedAt s.bk s.wk s.wn = true) :
    KnightAttacks s.wn s.bk := by
  have hna := (okB_iff s).mp hok |>.2.2.2.2.2.2.1
  rcases (kingAttackedAt_iff s.bk s.wk s.wn).mp hchk with hk | hn
  · exact (hna hk).elim
  · exact hn

/-- In a state with White to move and `mateB`, no move is legal. -/
theorem mateB_white_no_legalMove {s : KNState} (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : s.mateB = true) (m : Move) : ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, h4, h5, h6, hnaK, _⟩ := (okB_iff s).mp hok
  obtain ⟨hchk, hcap, hall⟩ := (mateB_iff s).mp hm
  simp only [ht, king, knight, Color.other] at hchk hcap hall
  have hnchk := inCheck_knightAttacks_white hok ht hchk
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingKnights_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .white = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .white := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsKnightsBoard s.wk s.bk s.wn s.bn m.src = some ⟨.white, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.wk := Board.kingsKnightsBoard_eq_white_king hsrc'
    have hka : KingAttacks s.wk m.dst := by
      have hatt' : (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .white = none := ht ▸ hside rfl
    have hboard : (s.toPosition.play m).board =
        (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.wk m.dst
          { color := .white, kind := .king } := by
      rw [play_board_of_src hsrc, boardAfter_king_no_castle _ _ hside' hpromo, hsq]
      rfl
    have hmem := hall m.dst (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hwn | hbn
    · obtain ⟨hdwk, hdbk, hdwn, hdbn⟩ := Board.ne_of_kingsKnightsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsKnightsBoard_whiteKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk
        hdwn hdbn, kingIsAttacked_white_eq _ _ _ _ hdbk hdwn hdbn h4 h5 h6] at hsafe'
      rcases hmem with hmem | hmem
      · exact hdwn hmem
      · exact Bool.false_ne_true (hsafe'.symm.trans hmem)
    · have this : s.toMove = .black := destOk_toMove_of_dst_whiteKnight rfl h2 h4 hwn hdestOk
      exact Color.other_ne .white (ht.symm.trans this).symm
    · exact not_kingAttacks_of_knightAttacks (knightAttacks_symm.mp hnchk) (hbn ▸ hka)
  · simp only at hk
    subst hk
    have hsq : m.src = s.wn := Board.kingsKnightsBoard_eq_white_knight hsrc'
    have hnaM : KnightAttacks s.wn m.dst := by
      have hatt0 : (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks s.wn m.dst =
          true := by
        have hatt' :
            (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks m.src m.dst = true := hatt
        rwa [hsq] at hatt'
      rw [Board.attacks_knight (Board.kingsKnightsBoard_whiteKnight _ _ _ _ h2 h4)] at hatt0
      exact of_decide_eq_true hatt0
    have hboard : (s.toPosition.play m).board =
        (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.wn m.dst
          { color := .white, kind := .knight } := by
      rw [play_board_of_src hsrc, boardAfter_knight _ _ hpromo, hsq]
      rfl
    rcases hdstOr with hempty | hwn | hbn
    · obtain ⟨hdwk, hdbk, hdwn, hdbn⟩ := Board.ne_of_kingsKnightsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsKnightsBoard_whiteKnight _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk
        hdwn hdbn, kingIsAttacked_white_eq _ _ _ _ h1 hdwk.symm h3 hdbk.symm h5 hdbn] at hsafe'
      exact Bool.false_ne_true
        (hsafe'.symm.trans ((kingAttackedAt_iff _ _ _).mpr (Or.inr hnchk)))
    · exact knightAttacks_ne hnaM hwn.symm
    · exact hcap (hbn ▸ hnaM)

/-- In a state with Black to move and `mateB`, no move is legal. -/
theorem mateB_black_no_legalMove {s : KNState} (hok : s.okB = true) (ht : s.toMove = .black)
    (hm : s.mateB = true) (m : Move) : ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, h4, h5, h6, hnaK, _⟩ := (okB_iff s).mp hok
  obtain ⟨hchk, hcap, hall⟩ := (mateB_iff s).mp hm
  simp only [ht, king, knight, Color.other] at hchk hcap hall
  have hnchk := inCheck_knightAttacks_black hok ht hchk
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingKnights_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .black := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsKnightsBoard s.wk s.bk s.wn s.bn m.src = some ⟨.black, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.bk := Board.kingsKnightsBoard_eq_black_king hsrc'
    have hka : KingAttacks s.bk m.dst := by
      have hatt' : (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .black = none := ht ▸ hside rfl
    have hboard : (s.toPosition.play m).board =
        (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.bk m.dst
          { color := .black, kind := .king } := by
      rw [play_board_of_src hsrc, boardAfter_king_no_castle _ _ hside' hpromo, hsq]
      rfl
    have hmem := hall m.dst (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hwn | hbn
    · obtain ⟨hdwk, hdbk, hdwn, hdbn⟩ := Board.ne_of_kingsKnightsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsKnightsBoard_blackKing _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk hdbk
        hdwn hdbn, kingIsAttacked_black_eq _ _ _ _ hdwk.symm h2 h3 hdwn hdbn h6] at hsafe'
      rcases hmem with hmem | hmem
      · exact hdbn hmem
      · exact Bool.false_ne_true (hsafe'.symm.trans hmem)
    · exact not_kingAttacks_of_knightAttacks (knightAttacks_symm.mp hnchk) (hwn ▸ hka)
    · have this : s.toMove = .white := destOk_toMove_of_dst_blackKnight rfl h3 h5 h6 hbn hdestOk
      exact Color.other_ne .black (ht.symm.trans this).symm
  · simp only at hk
    subst hk
    have hsq : m.src = s.bn := Board.kingsKnightsBoard_eq_black_knight hsrc'
    have hnaM : KnightAttacks s.bn m.dst := by
      have hatt0 : (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks s.bn m.dst =
          true := by
        have hatt' :
            (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).attacks m.src m.dst = true := hatt
        rwa [hsq] at hatt'
      rw [Board.attacks_knight (Board.kingsKnightsBoard_blackKnight _ _ _ _ h3 h5 h6)] at hatt0
      exact of_decide_eq_true hatt0
    have hboard : (s.toPosition.play m).board =
        (Board.kingsKnightsBoard s.wk s.bk s.wn s.bn).relocate s.bn m.dst
          { color := .black, kind := .knight } := by
      rw [play_board_of_src hsrc, boardAfter_knight _ _ hpromo, hsq]
      rfl
    rcases hdstOr with hempty | hwn | hbn
    · obtain ⟨hdwk, hdbk, hdwn, hdbn⟩ := Board.ne_of_kingsKnightsBoard_eq_none hempty
      rw [hboard, Board.relocate_kingsKnightsBoard_blackKnight _ _ _ _ _ h1 h2 h3 h4 h5 h6 hdwk
        hdbk hdwn hdbn, kingIsAttacked_black_eq _ _ _ _ h1 h2 hdwk.symm h4 hdbk.symm hdwn.symm]
        at hsafe'
      exact Bool.false_ne_true
        (hsafe'.symm.trans ((kingAttackedAt_iff _ _ _).mpr (Or.inr hnchk)))
    · exact hcap (hwn ▸ hnaM)
    · exact knightAttacks_ne hnaM hbn.symm

/-- A `mateB` state of an `okB` state is a checkmate position. -/
theorem inCheckmate_of_mateB {s : KNState} (hok : s.okB = true) (hm : s.mateB = true) :
    InCheckmate s.toPosition := by
  rw [InCheckmate_iff_forall_not_LegalMove]
  refine ⟨?_, ?_⟩
  · change s.toPosition.board.kingIsAttacked s.toPosition.toMove = true
    rw [kingIsAttacked_eq s hok]
    exact ((mateB_iff s).mp hm).1
  · cases ht : s.toMove with
    | white => exact mateB_white_no_legalMove hok ht hm
    | black => exact mateB_black_no_legalMove hok ht hm

end KNState

end Chess
