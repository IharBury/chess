import Chess.KingRookCover

/-!
# King and rook versus king: reachability

`Chess.KingRook` stores states in a white-rook frame and shows that every
non-dead legal state in that frame can reach checkmate, given `checkAll`.
This module uses `checkAll_true` from the covering files, rotates a
black-rook position into that frame, transfers `CheckmateReachable`
across the rotation, and decides the property for an arbitrary valid
king-and-rook versus king position.
-/

namespace Chess

namespace Position

theorem IsKingAndRook.castling_eq {p : Position} (h : IsKingAndRook p) :
    p.castling = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

theorem IsKingAndRook.enPassant_eq {p : Position} (h : IsKingAndRook p) :
    p.enPassant = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := h
  exact he

theorem IsKingAndRook.rot180 {p : Position} (h : IsKingAndRook p) :
    IsKingAndRook p.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
  have h2' : wk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h2
  have h3' : bk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h3
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  cases c with
  | white =>
    refine ⟨bk.rot180, wk.rot180, rs.rot180, .black, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsRookBoard_white wk bk rs h1 h2 h3]
  | black =>
    refine ⟨bk.rot180, wk.rot180, rs.rot180, .white, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsRookBoard_black wk bk rs h1 h2 h3]

theorem IsKingAndRook.not_IsTwoKings {p : Position} (h : IsKingAndRook p) :
    ¬ IsTwoKings p := by
  intro htk
  obtain ⟨wk, bk, rs, c, h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', hne', _, hboard', _, _⟩ := htk
  have h3c : p.board.occupied.card = 3 := by
    rw [hboard, Board.kingsRookBoard_occupied wk bk rs c h1 h2 h3]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [h3]
    · simp [h1, h2]
  have h2c : p.board.occupied.card = 2 := by
    rw [hboard', Board.kingsBoard_occupied wk' bk' hne']
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne']
  omega

theorem piece_of_kind_rook (piece : Piece) (hr : piece.kind = .rook) :
    piece = { color := piece.color, kind := .rook } := by
  rcases piece with ⟨pc, pk⟩
  subst hr
  rfl

theorem IsKingAndRook.play_rot180 {p : Position} {m : Move}
    (h : IsKingAndRook p) (hm : LegalMove p m) :
    (p.play m).rot180 = p.rot180.play m.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, _, hboard, hc, he⟩ := h
  obtain ⟨hpromo, _, _, _, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hplay := play_of_some p m hsrc
  have hplayR := play_of_some p.rot180 m.rot180 hsrcR
  cases hkind with
  | inl hk =>
    have hpiece := piece_of_kind_king piece hk
    have hs : m.castlingSide? piece.color = none := by
      simpa [hpc] using hside hk
    have hba := boardAfter_king_no_castle p m (c := piece.color) hs hpromo
    have hka : KingAttacks m.src m.dst := by
      have hatt' : p.board.attacks m.src m.dst = true := hatt
      rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
      exact of_decide_eq_true hatt'
    have hsR : m.rot180.castlingSide? piece.flip.color = none := by
      have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
        rcases m with ⟨s, d, pr⟩
        simp [Move.rot180, Move.std] at hpromo ⊢
        simp [hpromo]
      rw [hmstd]
      exact KRState.castlingSide_none_of_kingAttacks _
        ((Square.kingAttacks_rot180 _ _).mp hka)
    have hbaR := boardAfter_king_no_castle p.rot180 m.rot180
      (c := piece.flip.color) hsR (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_king m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_king m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.king } : Piece).flip =
          { color := piece.flip.color, kind := .king } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .king }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]
  | inr hr =>
    have hpiece := piece_of_kind_rook piece hr
    have hba := boardAfter_rook p m (c := piece.color) hpromo
    have hbaR := boardAfter_rook p.rot180 m.rot180 (c := piece.flip.color)
      (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_rook m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_rook m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.rook } : Piece).flip =
          { color := piece.flip.color, kind := .rook } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .rook }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]

theorem IsKingAndRook.legalMove_rot180_of {p : Position} {m : Move}
    (h : IsKingAndRook p) (hm : LegalMove p m) :
    LegalMove p.rot180 m.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  obtain ⟨hpromo, hdestOk, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hdestR : p.rot180.destOk m.rot180 = true := by
    rwa [← destOk_rot180]
  have hnpawn : (piece.flip.kind == PieceKind.pawn) = false := by
    cases hkind <;> simp [Piece.flip, ‹_›]
  have hka_of_king (hk : piece.kind = .king) : KingAttacks m.src m.dst := by
    have hpiece := piece_of_kind_king piece hk
    have hatt' : p.board.attacks m.src m.dst = true := hatt
    rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
    exact of_decide_eq_true hatt'
  have hkingB : (piece.flip.kind == PieceKind.king &&
      (m.rot180.castlingSide? p.rot180.toMove).isSome) = false := by
    cases hkind with
    | inl hk =>
      have hs : m.rot180.castlingSide? p.rot180.toMove = none := by
        have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
          rcases m with ⟨s, d, pr⟩
          simp [Move.rot180, Move.std] at hpromo ⊢
          simp [hpromo]
        rw [hmstd]
        exact KRState.castlingSide_none_of_kingAttacks p.rot180.toMove
          ((Square.kingAttacks_rot180 _ _).mp (hka_of_king hk))
      simp [Piece.flip, hk, hs]
    | inr hr => simp [Piece.flip, hr]
  have hattR : p.rot180.board.attacks m.rot180.src m.rot180.dst = true := by
    rw [rot180_board, Move.rot180_src, Move.rot180_dst, ← Board.attacks_rot180, hatt]
  have hsafeR :
      (p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove = false := by
    have hpl := IsKingAndRook.play_rot180
      (⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ : IsKingAndRook p) hm
    rw [← hpl]
    change (p.play m).board.rot180.kingIsAttacked p.toMove.other = false
    rw [← Board.kingIsAttacked_rot180]
    exact hsafe
  unfold LegalMove isLegalMove
  rw [hsrcR]
  have hcolR : (piece.flip.color == p.rot180.toMove) = true := by
    simp [Piece.flip, hpc, rot180_toMove]
  simp only [hcolR, Bool.true_and]
  rw [hdestR]
  simp only [Bool.true_and]
  simp only [hnpawn, hkingB]
  exact legal_king_step_bool _ _ _
    hattR (by simp [Move.rot180, hpromo]) hsafeR

theorem IsKingAndRook.legalMove_rot180 {p : Position} {m : Move}
    (h : IsKingAndRook p) :
    LegalMove p m ↔ LegalMove p.rot180 m.rot180 := by
  constructor
  · exact legalMove_rot180_of h
  · intro hm
    have := legalMove_rot180_of h.rot180 (m := m.rot180) hm
    simpa [rot180_involutive h.castling_eq h.enPassant_eq, Move.rot180_involutive]
      using this

theorem IsKingAndRook.inCheckmate_rot180 {p : Position} (h : IsKingAndRook p)
    (hm : InCheckmate p) : InCheckmate p.rot180 := by
  rw [InCheckmate_iff_forall_not_LegalMove] at hm ⊢
  refine ⟨?_, ?_⟩
  · change (p.rot180).board.kingIsAttacked p.rot180.toMove = true
    have this : p.board.kingIsAttacked p.toMove = true := hm.1
    rw [Board.kingIsAttacked_rot180] at this
    simpa [rot180_board, rot180_toMove] using this
  · intro m hleg
    exact hm.2 m.rot180 ((h.legalMove_rot180 (m := m.rot180)).mpr (by
      simpa [Move.rot180_involutive] using hleg))

theorem IsKingAndRook.reachable_rot180 {p : Position} (hp : IsKingAndRook p)
    {q : Position} (hr : Reachable p q) (hq : IsKingAndRook q) :
    Reachable p.rot180 q.rot180 := by
  refine Reachable.rec (motive := fun q _ => IsKingAndRook q →
      Reachable p.rot180 q.rot180) ?_ ?_ hr hq
  · intro _hq
    exact Reachable.refl
  · intro q m hrq hleg ih hq'
    have hqKR : IsKingAndRook q := by
      rcases hp.of_reachable hrq with h | htk
      · exact h
      · exact (hq'.not_IsTwoKings (htk.of_play hleg)).elim
    have hstep := Reachable.step m.rot180 (ih hqKR) (hqKR.legalMove_rot180.mp hleg)
    rwa [← hqKR.play_rot180 hleg] at hstep

theorem IsKingAndRook.checkmateReachable_rot180 {p : Position}
    (h : IsKingAndRook p) :
    CheckmateReachable p ↔ CheckmateReachable p.rot180 := by
  constructor
  · intro ⟨q, hr, hm⟩
    rcases h.of_reachable hr with hq | htk
    · exact ⟨q.rot180, h.reachable_rot180 hr hq, hq.inCheckmate_rot180 hm⟩
    · exact (htk.not_InCheckmate hm).elim
  · intro ⟨q, hr, hm⟩
    have h' := h.rot180
    rcases h'.of_reachable hr with hq | htk
    · have hr' := h'.reachable_rot180 hr hq
      have hm' := hq.inCheckmate_rot180 hm
      rw [rot180_involutive h.castling_eq h.enPassant_eq] at hr'
      exact ⟨q.rot180, hr', hm'⟩
    · exact (htk.not_InCheckmate hm).elim

/-- A valid position with exactly three occupied squares, one of them a
rook, and no remaining castling rights, holds only the two kings and that
rook, with the kings not adjacent. Castling rights are an extra hypothesis:
a rook on `a1`/`h1` with its king on `e1` could otherwise still have rights. -/
theorem isKingAndRook_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hrook : ∃ s c, p.board s = some { color := c, kind := .rook })
    (hcstl : p.castling = ∅) :
    IsKingAndRook p := by
  obtain ⟨hbv, hopp, _, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨rs, c, hrs⟩ := hrook
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_rs : wk ≠ rs := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_rook (hking.symm.trans hrs)
  have hbk_rs : bk ≠ rs := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_rook (hking.symm.trans hrs)
  have hoccEq : p.board.occupied = {wk, bk, rs} := by
    have hsub : ({wk, bk, rs} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hrs]
    have hcard : ({wk, bk, rs} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_rs]
      · simp [hwk_bk, hwk_rs]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsRookBoard wk bk rs c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsRookBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsRookBoard_black wk bk rs c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = rs
        · rw [hs, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs]
          exact hrs
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsRookBoard_other wk bk rs s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsRookBoard_kingIsAttacked_black wk bk rs c
          hwk_bk hwk_rs hbk_rs).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsRookBoard_kingIsAttacked_white wk bk rs c
          hwk_bk hwk_rs hbk_rs).mpr (Or.inl (kingAttacks_symmetric.mp hk))
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
  have he : p.enPassant = none := by
    cases hep' : p.enPassant with
    | none => rfl
    | some ep =>
      obtain ⟨_, _, hcap⟩ :=
        (enPassantOk_some p ep hep').mp (by simpa [hep'] using hep)
      obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp
        (existsPawnAttacking_of_existsLegalEnPassantCapture hcap)
      have hpawn := (hasPawn_eq_true_iff _ _ _).mp hs
      have hmem : s ∈ p.board.occupied := by
        simp [Board.mem_occupied, hpawn]
      rw [hoccEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsq | hsq | hsq
      · rw [hsq, hboard, Board.kingsRookBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsRookBoard_black wk bk rs c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs] at hpawn
        cases some_rook_ne_pawn hpawn
  exact ⟨wk, bk, rs, c, hwk_bk, hwk_rs, hbk_rs, hna, hboard, hcstl, he⟩

theorem exists_krState_white {p : Position} (hv : Valid p)
    {wk bk rs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsRookBoard wk bk rs .white)
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    ∃ s : KRState, s.okB = true ∧ s.toPosition = p := by
  refine ⟨⟨p.toMove, wk, bk, rs⟩, ?_, ?_⟩
  · rw [KRState.okB_iff]
    refine ⟨h1, h2, h3, hna, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have hopp' : (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .black =
          false := by simpa [ht] using hopp
      simpa [KRState.inCheckB, KRState.kingIsAttacked_black_eq wk bk rs h1 h2 h3] using hopp'
    | black =>
      have hopp' : (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      simpa [KRState.inCheckB, KRState.kingIsAttacked_white_eq wk bk rs h1 h2 h3] using hopp'
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

theorem exists_krState_black {p : Position} (hv : Valid p)
    {wk bk rs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsRookBoard wk bk rs .black)
    (_hc : p.castling = ∅) (_he : p.enPassant = none) :
    ∃ s : KRState, s.okB = true ∧ s.toPosition = p.rot180 := by
  let s : KRState := ⟨p.toMove.other, bk.rot180, wk.rot180, rs.rot180⟩
  refine ⟨s, ?_, ?_⟩
  · have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
    have h2' : wk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h2
    have h3' : bk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h3
    have hna' : ¬ KingAttacks bk.rot180 wk.rot180 :=
      fun hk => hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
    rw [KRState.okB_iff]
    refine ⟨h1', h3', h2', hna', ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have : s.toMove.other = .white := by simp [s, ht]
      rw [this]
      simpa [s, KRState.inCheckB, KRState.kingAttackedWhite] using hna'
    | black =>
      have hopp' : (Board.kingsRookBoard wk bk rs .black).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      have hiff := Board.kingsRookBoard_kingIsAttacked_white wk bk rs .black h1 h2 h3
      have hn : ¬ (KingAttacks bk wk ∨
          (Color.black = .black ∧ RookAttacks rs wk ∧ ¬ Between rs wk bk)) := by
        intro h'
        exact Bool.false_ne_true (hopp'.symm.trans (hiff.mpr h'))
      have : s.toMove.other = .black := by simp [s, ht]
      rw [this]
      unfold KRState.inCheckB KRState.kingAttackedBlack
      simp only [Bool.or_eq_false_iff]
      refine ⟨decide_eq_false (by simpa [s] using hna'), ?_⟩
      cases hrc : KRState.rookChecks s.rs s.bk s.wk
      · rfl
      · have ⟨hR, hnb⟩ := (KRState.rookChecks_iff s.rs s.bk s.wk).mp hrc
        exact False.elim (hn (Or.inr ⟨rfl,
          (Square.rookAttacks_rot180 rs wk).mpr (by simpa [s] using hR),
          mt (Square.between_rot180 rs wk bk).mp (by simpa [s] using hnb)⟩))
  · simp [s, KRState.toPosition, rot180, hboard,
      Board.rot180_kingsRookBoard_black wk bk rs h1 h2 h3]

theorem exists_krState {p : Position} (hv : Valid p) (h : IsKingAndRook p) :
    (∃ s : KRState, s.okB = true ∧ s.toPosition = p) ∨
      (∃ s : KRState, s.okB = true ∧ s.toPosition = p.rot180) := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  cases c with
  | white => exact Or.inl (exists_krState_white hv h1 h2 h3 hna hboard hc he)
  | black => exact Or.inr (exists_krState_black hv h1 h2 h3 hna hboard hc he)

theorem IsKingAndRook.checkmateReachable_of_not_dead {p : Position}
    (_hv : Valid p) (h : IsKingAndRook p) {s : KRState}
    (hok : s.okB = true) (hnd : s.deadB = false)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p := by
  have hcr := KRState.checkmateReachable_of_okB_of_not_dead KRState.checkAll_true hok hnd
  rcases hpos with hpos | hpos
  · rwa [hpos] at hcr
  · rw [h.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem IsKingAndRook.checkmateReachable_iff_deadB {p : Position}
    (hv : Valid p) (h : IsKingAndRook p) {s : KRState}
    (hok : s.okB = true)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p ↔ s.deadB = false := by
  constructor
  · intro hcr
    have hiff := KRState.checkmateReachable_iff_not_dead KRState.checkAll_true hok
    rcases hpos with hpos | hpos
    · rw [← hpos] at hcr
      exact hiff.mp hcr
    · rw [h.checkmateReachable_rot180] at hcr
      rw [← hpos] at hcr
      exact hiff.mp hcr
  · intro hnd
    exact h.checkmateReachable_of_not_dead hv hok hnd hpos

/-- If the player to move owns the rook, checkmate is reachable. -/
theorem IsKingAndRook.checkmateReachable_of_rookToMove {p : Position}
    (hv : Valid p) (h : IsKingAndRook p)
    (hr : ∃ s, p.board s = some { color := p.toMove, kind := .rook }) :
    CheckmateReachable p := by
  have hKR : IsKingAndRook p := h
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have ht : p.toMove = c := by
    obtain ⟨sq, hsq⟩ := hr
    have hsqb : Board.kingsRookBoard wk bk rs c sq =
        some { color := p.toMove, kind := .rook } := by rwa [hboard] at hsq
    have hsqrs : sq = rs := by
      unfold Board.kingsRookBoard at hsqb
      split_ifs at hsqb <;>
        first | cases some_king_ne_rook hsqb | assumption
    rw [hsqrs, Board.kingsRookBoard_rook wk bk rs c h2 h3] at hsqb
    injection hsqb with hpiece
    injection hpiece with hcol _
    exact hcol.symm
  cases c with
  | white =>
    obtain ⟨s, hok, hpos⟩ := exists_krState_white hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, ht]
    have hcr := KRState.checkmateReachable_of_okB_white KRState.checkAll_true hok this
    rwa [hpos] at hcr
  | black =>
    obtain ⟨s, hok, hpos⟩ := exists_krState_black hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, rot180_toMove, ht]
      rfl
    have hcr := KRState.checkmateReachable_of_okB_white KRState.checkAll_true hok this
    rw [hKR.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem ofPositionWhite?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPositionWhite? p = some s) :
    s.okB = true ∧ s.toPosition = p := by
  unfold KRState.ofPositionWhite? at h
  split at h
  · rename_i wk bk rs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      have hboard : p.board = Board.kingsRookBoard wk bk rs .white := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KRState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      rfl
  · cases h

theorem ofPositionBlack?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPositionBlack? p = some s) :
    s.okB = true ∧ s.toPosition = p.rot180 := by
  unfold KRState.ofPositionBlack? at h
  split at h
  · rename_i wk bk rs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      obtain ⟨h1s, h2s, h3s, _, _⟩ := (KRState.okB_iff _).mp hok
      have hwk_bk : wk ≠ bk := fun heq => h1s (by simp [heq])
      have hwk_rs : wk ≠ rs := fun heq => h3s (by simp [heq])
      have hbk_rs : bk ≠ rs := fun heq => h2s (by simp [heq])
      have hboard : p.board = Board.kingsRookBoard wk bk rs .black := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KRState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      simp [KRState.toPosition, rot180,
        Board.rot180_kingsRookBoard_black wk bk rs hwk_bk hwk_rs hbk_rs]
  · cases h

theorem ofPositionWhite?_of_eq {p : Position} {s : KRState}
    (hok : s.okB = true) (hpos : s.toPosition = p) :
    KRState.ofPositionWhite? p = some s := by
  have hboard : p.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
    rw [← hpos]; rfl
  have htm : p.toMove = s.toMove := by
    have : s.toPosition.toMove = p.toMove := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  have hcst : p.castling = ∅ := by
    have : s.toPosition.castling = p.castling := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  have hep : p.enPassant = none := by
    have : s.toPosition.enPassant = p.enPassant := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
  have hwk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.wk := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsRookBoard_white])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.bk := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_black s.wk s.bk s.rs .white h1])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .rook }) = some s.rs := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_rook s.wk s.bk s.rs .white h2 h3])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_rook (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KRState.allSquares.all fun q =>
      p.board q == Board.kingsRookBoard s.wk s.bk s.rs .white q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove, s.wk, s.bk, s.rs⟩ : KRState) = s := by
    cases s
    simp [htm]
  unfold KRState.ofPositionWhite?
  rw [hwk, hbk, hrs]
  simp [hs, hok, hall, hcst, hep]

theorem ofPositionBlack?_of_eq {p : Position} {s : KRState}
    (hok : s.okB = true) (hpos : s.toPosition = p.rot180)
    (hcst : p.castling = ∅) (hep : p.enPassant = none) :
    KRState.ofPositionBlack? p = some s := by
  obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
  have hboardR : p.rot180.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
    rw [← hpos]; rfl
  have hboard : p.board =
      Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180 .black := by
    have hrot := congrArg Board.rot180 hboardR
    rw [rot180_board, Board.board_rot180_involutive,
      Board.rot180_kingsRookBoard_white s.wk s.bk s.rs h1 h2 h3] at hrot
    exact hrot
  have htm : p.toMove.other = s.toMove := by
    have : s.toPosition.toMove = p.rot180.toMove := by rw [hpos]
    simpa [KRState.toPosition, rot180_toMove] using this.symm
  have hneWB : s.bk.rot180 ≠ s.wk.rot180 := Ne.symm (mt Board.rot180_injective h1)
  have hneWR : s.wk.rot180 ≠ s.rs.rot180 := mt Board.rot180_injective h2
  have hneBR : s.bk.rot180 ≠ s.rs.rot180 := mt Board.rot180_injective h3
  have hwk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.bk.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsRookBoard_white])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.wk.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_black s.bk.rot180 s.wk.rot180 s.rs.rot180
          .black hneWB])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .rook }) = some s.rs.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_rook s.bk.rot180 s.wk.rot180 s.rs.rot180
          .black hneBR hneWR])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_rook (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KRState.allSquares.all fun q =>
      p.board q == Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180
        .black q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove.other, s.wk, s.bk, s.rs⟩ : KRState) = s := by
    cases s
    simp [htm]
  unfold KRState.ofPositionBlack?
  rw [hwk, hbk, hrs]
  simp [Square.rot180_involutive, hs, hok, hall, hcst, hep]

theorem ofPositionWhite?_eq_none_of_black {p : Position} {wk bk rs : Square}
    (hboard : p.board = Board.kingsRookBoard wk bk rs .black) :
    KRState.ofPositionWhite? p = none := by
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .rook }) = none := by
    refine List.find?_eq_none.mpr ?_
    intro q _
    cases hb : (p.board q == some { color := .white, kind := .rook })
    · exact Bool.false_ne_true
    · have heq : p.board q = some { color := .white, kind := .rook } :=
        beq_iff_eq.mp hb
      rw [hboard] at heq
      unfold Board.kingsRookBoard at heq
      split_ifs at heq <;> cases heq
  unfold KRState.ofPositionWhite?
  rw [hrs]
  split
  · rename_i _ _ _ heq
    cases heq
  · rfl

theorem ofPosition?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPosition? p = some s) :
    s.okB = true ∧ (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  unfold KRState.ofPosition? at h
  split at h
  · rename_i s' hW
    injection h with hs
    subst hs
    have ⟨hok, hpos⟩ := ofPositionWhite?_eq_some hW
    exact ⟨hok, Or.inl hpos⟩
  · have ⟨hok, hpos⟩ := ofPositionBlack?_eq_some h
    exact ⟨hok, Or.inr hpos⟩

theorem ofPosition?_complete {p : Position} (hv : Valid p) (h : IsKingAndRook p) :
    ∃ s, KRState.ofPosition? p = some s ∧ s.okB = true ∧
      (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  rcases exists_krState hv h with ⟨s, hok, hpos⟩ | ⟨s, hok, hpos⟩
  · refine ⟨s, ?_, hok, Or.inl hpos⟩
    unfold KRState.ofPosition?
    rw [ofPositionWhite?_of_eq hok hpos]
  · refine ⟨s, ?_, hok, Or.inr hpos⟩
    obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
    have hboardR : p.rot180.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
      rw [← hpos]; rfl
    have hboard : p.board =
        Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180 .black := by
      have hrot := congrArg Board.rot180 hboardR
      rw [rot180_board, Board.board_rot180_involutive,
        Board.rot180_kingsRookBoard_white s.wk s.bk s.rs h1 h2 h3] at hrot
      exact hrot
    unfold KRState.ofPosition?
    rw [ofPositionWhite?_eq_none_of_black hboard,
      ofPositionBlack?_of_eq hok hpos h.castling_eq h.enPassant_eq]

/-- The engineered mating line of a king-and-rook versus king position;
`[]` when the position is dead or not of this material. Black-rook
positions are rotated into the white-rook frame, and the resulting moves
are rotated back. -/
def kingRookMatingLine (p : Position) : List Move :=
  match KRState.ofPositionWhite? p with
  | some s => s.matingLine
  | none =>
    match KRState.ofPositionBlack? p with
    | some s => s.matingLine.map Move.rot180
    | none => []

/-- Whether a king-and-rook versus king position is dead for helpmate
(`true` when the board is not of this material). -/
def kingRookDead (p : Position) : Bool :=
  match KRState.ofPosition? p with
  | some s => s.deadB
  | none => true

/-- In a valid king-and-rook versus king position, checkmate is reachable
exactly when the corresponding three-piece state is not dead. -/
theorem IsKingAndRook.checkmateReachable_iff {p : Position}
    (hv : Valid p) (h : IsKingAndRook p) :
    CheckmateReachable p ↔ kingRookDead p = false := by
  obtain ⟨s, hs, hok, hpos⟩ := ofPosition?_complete hv h
  have hdeq : kingRookDead p = s.deadB := by simp [kingRookDead, hs]
  rw [hdeq]
  exact h.checkmateReachable_iff_deadB hv hok hpos

/-- Decides whether checkmate is reachable from a valid king-and-rook
versus king position: exactly when the corresponding three-piece state
is not dead. -/
def kingRookCheckmateReachable (p : Position) (hv : Valid p)
    (h : IsKingAndRook p) : Decidable (CheckmateReachable p) :=
  decidable_of_iff (kingRookDead p = false) (h.checkmateReachable_iff hv).symm

/-! ### Example: kings on `e1` and `e8`, white rook on `a1` -/

/-- White king on `e1`, black king on `e8`, white rook on `a1`, White to
move. -/
def kingRookStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.a1 then some { color := .white, kind := .rook }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingRookStart_isValid : isValid kingRookStart = true := by
  native_decide

theorem kingRookStart_valid : Valid kingRookStart :=
  (isValid_eq_true_iff _).mp kingRookStart_isValid

theorem kingRookStart_isKingAndRook : IsKingAndRook kingRookStart :=
  isKingAndRook_of_valid kingRookStart_valid (by native_decide)
    ⟨Square.a1, Color.white, by native_decide⟩ (by native_decide)

theorem kingRookStart_CheckmateReachable : CheckmateReachable kingRookStart :=
  kingRookStart_isKingAndRook.checkmateReachable_of_rookToMove kingRookStart_valid
    ⟨Square.a1, by native_decide⟩

theorem kingRookStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingRookStart)
      (kingRookCheckmateReachable kingRookStart kingRookStart_valid
        kingRookStart_isKingAndRook) = true := by
  native_decide

theorem kingRookStart_not_deadPosition : ¬ DeadPosition kingRookStart :=
  not_deadPosition_of_checkmateReachable kingRookStart_CheckmateReachable

theorem kingRookStart_matingLine_legal :
    pathLegal kingRookStart (kingRookMatingLine kingRookStart) = true := by
  native_decide

theorem kingRookStart_matingLine_inCheckmate :
    (playSeq kingRookStart (kingRookMatingLine kingRookStart)).inCheckmate = true := by
  native_decide

theorem kingRookStart_CheckmateReachable' : CheckmateReachable kingRookStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingRookStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingRookStart_matingLine_inCheckmate)

/-- Forced capture of an unprotected rook: Black to move, in check, and
the only legal move takes the rook, leaving two kings. -/
def rookForcedCapture : Position where
  board := fun s =>
    if s = Square.c8 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .rook }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookForcedCapture_isValid : isValid rookForcedCapture = true := by
  native_decide

theorem rookForcedCapture_valid : Valid rookForcedCapture :=
  (isValid_eq_true_iff _).mp rookForcedCapture_isValid

theorem rookForcedCapture_isKingAndRook : IsKingAndRook rookForcedCapture :=
  isKingAndRook_of_valid rookForcedCapture_valid (by native_decide)
    ⟨Square.a7, Color.white, by native_decide⟩ (by native_decide)

theorem rookForcedCapture_deadB : ∃ s : KRState, s.okB = true ∧
    s.toPosition = rookForcedCapture ∧ s.deadB = true := by
  refine ⟨⟨.black, Square.c8, Square.a8, Square.a7⟩, by native_decide, ?_,
    by native_decide⟩
  have hboard : Board.kingsRookBoard Square.c8 Square.a8 Square.a7 .white =
      rookForcedCapture.board := by
    funext q
    simp [rookForcedCapture, Board.kingsRookBoard]
  simp [KRState.toPosition, rookForcedCapture, hboard, CastlingRights.empty]

theorem rookForcedCapture_not_CheckmateReachable :
    ¬ CheckmateReachable rookForcedCapture := by
  obtain ⟨s, hok, hpos, hd⟩ := rookForcedCapture_deadB
  intro hcr
  have := (rookForcedCapture_isKingAndRook.checkmateReachable_iff_deadB
    rookForcedCapture_valid hok (Or.inl hpos)).mp hcr
  exact Bool.false_ne_true (this.symm.trans hd)

theorem rookForcedCapture_decide_CheckmateReachable :
    @decide (CheckmateReachable rookForcedCapture)
      (kingRookCheckmateReachable rookForcedCapture rookForcedCapture_valid
        rookForcedCapture_isKingAndRook) = false := by
  native_decide

theorem rookStalemate_isKingAndRook : IsKingAndRook rookStalemate :=
  isKingAndRook_of_valid
    ((isValid_eq_true_iff rookStalemate).mp rookStalemate_isValid)
    (by native_decide) ⟨Square.g7, Color.white, by native_decide⟩ (by native_decide)

theorem rookStalemate_not_CheckmateReachable :
    ¬ CheckmateReachable rookStalemate :=
  not_CheckmateReachable_of_InStalemate
    ((inStalemate_eq_true_iff _).mp rookStalemate_inStalemate)

theorem rookStalemate_decide_CheckmateReachable :
    @decide (CheckmateReachable rookStalemate)
      (kingRookCheckmateReachable rookStalemate
        ((isValid_eq_true_iff rookStalemate).mp rookStalemate_isValid)
        rookStalemate_isKingAndRook) = false := by
  native_decide

theorem rookStalemate_deadPosition : DeadPosition rookStalemate :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr
    rookStalemate_not_CheckmateReachable

end Position

end Chess
