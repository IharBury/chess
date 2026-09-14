import Chess.KingQueenCover

/-!
# King and queen versus king: reachability

`Chess.KingQueen` stores states in a white-queen frame and shows that every
non-dead legal state in that frame can reach checkmate, given `checkAll`.
This module uses `checkAll_true` from the covering files, rotates a
black-queen position into that frame, transfers `CheckmateReachable`
across the rotation, and decides the property for an arbitrary valid
king-and-queen versus king position.
-/

namespace Chess

namespace Position


theorem IsKingAndQueen.castling_eq {p : Position} (h : IsKingAndQueen p) :
    p.castling = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

theorem IsKingAndQueen.enPassant_eq {p : Position} (h : IsKingAndQueen p) :
    p.enPassant = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := h
  exact he

theorem IsKingAndQueen.rot180 {p : Position} (h : IsKingAndQueen p) :
    IsKingAndQueen p.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
  have h2' : wk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h2
  have h3' : bk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h3
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  cases c with
  | white =>
    refine ⟨bk.rot180, wk.rot180, qs.rot180, .black, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsQueenBoard_white wk bk qs h1 h2 h3]
  | black =>
    refine ⟨bk.rot180, wk.rot180, qs.rot180, .white, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsQueenBoard_black wk bk qs h1 h2 h3]

theorem IsKingAndQueen.not_IsTwoKings {p : Position} (h : IsKingAndQueen p) :
    ¬ IsTwoKings p := by
  intro htk
  obtain ⟨wk, bk, qs, c, h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', hne', _, hboard', _, _⟩ := htk
  have h3c : p.board.occupied.card = 3 := by
    rw [hboard, Board.kingsQueenBoard_occupied wk bk qs c h1 h2 h3]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [h3]
    · simp [h1, h2]
  have h2c : p.board.occupied.card = 2 := by
    rw [hboard', Board.kingsBoard_occupied wk' bk' hne']
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne']
  omega


theorem piece_of_kind_queen (piece : Piece) (hr : piece.kind = .queen) :
    piece = { color := piece.color, kind := .queen } := by
  rcases piece with ⟨pc, pk⟩
  subst hr
  rfl

theorem IsKingAndQueen.play_rot180 {p : Position} {m : Move}
    (h : IsKingAndQueen p) (hm : LegalMove p m) :
    (p.play m).rot180 = p.rot180.play m.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, _, hboard, hc, he⟩ := h
  obtain ⟨hpromo, _, _, _, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core hboard hc hm
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
      exact KQState.castlingSide_none_of_kingAttacks _
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
    have hpiece := piece_of_kind_queen piece hr
    have hba := boardAfter_queen p m (c := piece.color) hpromo
    have hbaR := boardAfter_queen p.rot180 m.rot180 (c := piece.flip.color)
      (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_queen m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_queen m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.queen } : Piece).flip =
          { color := piece.flip.color, kind := .queen } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .queen }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]

theorem IsKingAndQueen.legalMove_rot180_of {p : Position} {m : Move}
    (h : IsKingAndQueen p) (hm : LegalMove p m) :
    LegalMove p.rot180 m.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  obtain ⟨hpromo, hdestOk, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core hboard hc hm
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
        exact KQState.castlingSide_none_of_kingAttacks p.rot180.toMove
          ((Square.kingAttacks_rot180 _ _).mp (hka_of_king hk))
      simp [Piece.flip, hk, hs]
    | inr hr => simp [Piece.flip, hr]
  have hattR : p.rot180.board.attacks m.rot180.src m.rot180.dst = true := by
    rw [rot180_board, Move.rot180_src, Move.rot180_dst, ← Board.attacks_rot180, hatt]
  have hsafeR :
      (p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove = false := by
    have hpl := IsKingAndQueen.play_rot180
      (⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ : IsKingAndQueen p) hm
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

theorem IsKingAndQueen.legalMove_rot180 {p : Position} {m : Move}
    (h : IsKingAndQueen p) :
    LegalMove p m ↔ LegalMove p.rot180 m.rot180 := by
  constructor
  · exact legalMove_rot180_of h
  · intro hm
    have := legalMove_rot180_of h.rot180 (m := m.rot180) hm
    simpa [rot180_involutive h.castling_eq h.enPassant_eq, Move.rot180_involutive]
      using this

theorem IsKingAndQueen.inCheckmate_rot180 {p : Position} (h : IsKingAndQueen p)
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

theorem IsKingAndQueen.reachable_rot180 {p : Position} (hp : IsKingAndQueen p)
    {q : Position} (hr : Reachable p q) (hq : IsKingAndQueen q) :
    Reachable p.rot180 q.rot180 := by
  refine Reachable.rec (motive := fun q _ => IsKingAndQueen q →
      Reachable p.rot180 q.rot180) ?_ ?_ hr hq
  · intro _hq
    exact Reachable.refl
  · intro q m hrq hleg ih hq'
    have hqKQ : IsKingAndQueen q := by
      rcases hp.of_reachable hrq with h | htk
      · exact h
      · exact (hq'.not_IsTwoKings (htk.of_play hleg)).elim
    have hstep := Reachable.step m.rot180 (ih hqKQ) (hqKQ.legalMove_rot180.mp hleg)
    rwa [← hqKQ.play_rot180 hleg] at hstep

theorem IsKingAndQueen.checkmateReachable_rot180 {p : Position}
    (h : IsKingAndQueen p) :
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
queen, and no remaining castling rights, holds only the two kings and that
queen, with the kings not adjacent. Castling rights are an extra hypothesis:
a queen on `a1`/`h1` with its king on `e1` could otherwise still have rights. -/
theorem isKingAndQueen_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hqueen : ∃ s c, p.board s = some { color := c, kind := .queen })
    (hcstl : p.castling = ∅) :
    IsKingAndQueen p := by
  obtain ⟨hbv, hopp, _, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨qs, c, hqs⟩ := hqueen
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_qs : wk ≠ qs := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_queen (hking.symm.trans hqs)
  have hbk_qs : bk ≠ qs := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_queen (hking.symm.trans hqs)
  have hoccEq : p.board.occupied = {wk, bk, qs} := by
    have hsub : ({wk, bk, qs} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hqs]
    have hcard : ({wk, bk, qs} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_qs]
      · simp [hwk_bk, hwk_qs]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsQueenBoard wk bk qs c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsQueenBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsQueenBoard_black wk bk qs c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = qs
        · rw [hs, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs]
          exact hqs
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsQueenBoard_other wk bk qs s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsQueenBoard_kingIsAttacked_black wk bk qs c
          hwk_bk hwk_qs hbk_qs).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsQueenBoard_kingIsAttacked_white wk bk qs c
          hwk_bk hwk_qs hbk_qs).mpr (Or.inl (kingAttacks_symmetric.mp hk))
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
      · rw [hsq, hboard, Board.kingsQueenBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsQueenBoard_black wk bk qs c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs] at hpawn
        cases some_queen_ne_pawn hpawn
  exact ⟨wk, bk, qs, c, hwk_bk, hwk_qs, hbk_qs, hna, hboard, hcstl, he⟩

theorem exists_kqState_white {p : Position} (hv : Valid p)
    {wk bk qs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .white)
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    ∃ s : KQState, s.okB = true ∧ s.toPosition = p := by
  refine ⟨⟨p.toMove, wk, bk, qs⟩, ?_, ?_⟩
  · rw [KQState.okB_iff]
    refine ⟨h1, h2, h3, hna, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .black =
          false := by simpa [ht] using hopp
      simpa [KQState.inCheckB, KQState.kingIsAttacked_black_eq wk bk qs h1 h2 h3] using hopp'
    | black =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      simpa [KQState.inCheckB, KQState.kingIsAttacked_white_eq wk bk qs h1 h2 h3] using hopp'
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

theorem exists_kqState_black {p : Position} (hv : Valid p)
    {wk bk qs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .black)
    (_hc : p.castling = ∅) (_he : p.enPassant = none) :
    ∃ s : KQState, s.okB = true ∧ s.toPosition = p.rot180 := by
  let s : KQState := ⟨p.toMove.other, bk.rot180, wk.rot180, qs.rot180⟩
  refine ⟨s, ?_, ?_⟩
  · have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
    have h2' : wk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h2
    have h3' : bk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h3
    have hna' : ¬ KingAttacks bk.rot180 wk.rot180 :=
      fun hk => hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
    rw [KQState.okB_iff]
    refine ⟨h1', h3', h2', hna', ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have : s.toMove.other = .white := by simp [s, ht]
      rw [this]
      simpa [s, KQState.inCheckB, KQState.kingAttackedWhite] using hna'
    | black =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .black).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      have hiff := Board.kingsQueenBoard_kingIsAttacked_white wk bk qs .black h1 h2 h3
      have hn : ¬ (KingAttacks bk wk ∨
          (Color.black = .black ∧ QueenAttacks qs wk ∧ ¬ Between qs wk bk)) := by
        intro h'
        exact Bool.false_ne_true (hopp'.symm.trans (hiff.mpr h'))
      have : s.toMove.other = .black := by simp [s, ht]
      rw [this]
      unfold KQState.inCheckB KQState.kingAttackedBlack
      simp only [Bool.or_eq_false_iff]
      refine ⟨decide_eq_false (by simpa [s] using hna'), ?_⟩
      cases hrc : KQState.queenChecks s.qs s.bk s.wk
      · rfl
      · have ⟨hR, hnb⟩ := (KQState.queenChecks_iff s.qs s.bk s.wk).mp hrc
        exact False.elim (hn (Or.inr ⟨rfl,
          (Square.queenAttacks_rot180 qs wk).mpr (by simpa [s] using hR),
          mt (Square.between_rot180 qs wk bk).mp (by simpa [s] using hnb)⟩))
  · simp [s, KQState.toPosition, rot180, hboard,
      Board.rot180_kingsQueenBoard_black wk bk qs h1 h2 h3]

theorem exists_kqState {p : Position} (hv : Valid p) (h : IsKingAndQueen p) :
    (∃ s : KQState, s.okB = true ∧ s.toPosition = p) ∨
      (∃ s : KQState, s.okB = true ∧ s.toPosition = p.rot180) := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  cases c with
  | white => exact Or.inl (exists_kqState_white hv h1 h2 h3 hna hboard hc he)
  | black => exact Or.inr (exists_kqState_black hv h1 h2 h3 hna hboard hc he)

theorem IsKingAndQueen.checkmateReachable_of_not_dead {p : Position}
    (_hv : Valid p) (h : IsKingAndQueen p) {s : KQState}
    (hok : s.okB = true) (hnd : s.deadB = false)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p := by
  have hcr := KQState.checkmateReachable_of_okB_of_not_dead KQState.checkAll_true hok hnd
  rcases hpos with hpos | hpos
  · rwa [hpos] at hcr
  · rw [h.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem IsKingAndQueen.checkmateReachable_iff_deadB {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p) {s : KQState}
    (hok : s.okB = true)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p ↔ s.deadB = false := by
  constructor
  · intro hcr
    have hiff := KQState.checkmateReachable_iff_not_dead KQState.checkAll_true hok
    rcases hpos with hpos | hpos
    · rw [← hpos] at hcr
      exact hiff.mp hcr
    · rw [h.checkmateReachable_rot180] at hcr
      rw [← hpos] at hcr
      exact hiff.mp hcr
  · intro hnd
    exact h.checkmateReachable_of_not_dead hv hok hnd hpos

/-- If the player to move owns the queen, checkmate is reachable. -/
theorem IsKingAndQueen.checkmateReachable_of_queenToMove {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p)
    (hr : ∃ s, p.board s = some { color := p.toMove, kind := .queen }) :
    CheckmateReachable p := by
  have hKQ : IsKingAndQueen p := h
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have ht : p.toMove = c := by
    obtain ⟨sq, hsq⟩ := hr
    have hsqb : Board.kingsQueenBoard wk bk qs c sq =
        some { color := p.toMove, kind := .queen } := by rwa [hboard] at hsq
    have hsqrs : sq = qs := by
      unfold Board.kingsQueenBoard at hsqb
      split_ifs at hsqb <;>
        first | cases some_king_ne_queen hsqb | assumption
    rw [hsqrs, Board.kingsQueenBoard_queen wk bk qs c h2 h3] at hsqb
    injection hsqb with hpiece
    injection hpiece with hcol _
    exact hcol.symm
  cases c with
  | white =>
    obtain ⟨s, hok, hpos⟩ := exists_kqState_white hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, ht]
    have hcr := KQState.checkmateReachable_of_okB_white KQState.checkAll_true hok this
    rwa [hpos] at hcr
  | black =>
    obtain ⟨s, hok, hpos⟩ := exists_kqState_black hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, rot180_toMove, ht]
      rfl
    have hcr := KQState.checkmateReachable_of_okB_white KQState.checkAll_true hok this
    rw [hKQ.checkmateReachable_rot180]
    rwa [hpos] at hcr


theorem kq_ofPositionWhite?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPositionWhite? p = some s) :
    s.okB = true ∧ s.toPosition = p := by
  unfold KQState.ofPositionWhite? at h
  split at h
  · rename_i wk bk qs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      have hboard : p.board = Board.kingsQueenBoard wk bk qs .white := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KQState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      rfl
  · cases h

theorem kq_ofPositionBlack?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPositionBlack? p = some s) :
    s.okB = true ∧ s.toPosition = p.rot180 := by
  unfold KQState.ofPositionBlack? at h
  split at h
  · rename_i wk bk qs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      obtain ⟨h1s, h2s, h3s, _, _⟩ := (KQState.okB_iff _).mp hok
      have hwk_bk : wk ≠ bk := fun heq => h1s (by simp [heq])
      have hwk_qs : wk ≠ qs := fun heq => h3s (by simp [heq])
      have hbk_qs : bk ≠ qs := fun heq => h2s (by simp [heq])
      have hboard : p.board = Board.kingsQueenBoard wk bk qs .black := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KQState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      simp [KQState.toPosition, rot180,
        Board.rot180_kingsQueenBoard_black wk bk qs hwk_bk hwk_qs hbk_qs]
  · cases h

theorem kq_ofPositionWhite?_of_eq {p : Position} {s : KQState}
    (hok : s.okB = true) (hpos : s.toPosition = p) :
    KQState.ofPositionWhite? p = some s := by
  have hboard : p.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
    rw [← hpos]; rfl
  have htm : p.toMove = s.toMove := by
    have : s.toPosition.toMove = p.toMove := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  have hcst : p.castling = ∅ := by
    have : s.toPosition.castling = p.castling := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  have hep : p.enPassant = none := by
    have : s.toPosition.enPassant = p.enPassant := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
  have hwk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.wk := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsQueenBoard_white])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.bk := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_black s.wk s.bk s.qs .white h1])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .queen }) = some s.qs := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_queen s.wk s.bk s.qs .white h2 h3])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_queen (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KQState.allSquares.all fun q =>
      p.board q == Board.kingsQueenBoard s.wk s.bk s.qs .white q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove, s.wk, s.bk, s.qs⟩ : KQState) = s := by
    cases s
    simp [htm]
  unfold KQState.ofPositionWhite?
  rw [hwk, hbk, hqs]
  simp [hs, hok, hall, hcst, hep]

theorem kq_ofPositionBlack?_of_eq {p : Position} {s : KQState}
    (hok : s.okB = true) (hpos : s.toPosition = p.rot180)
    (hcst : p.castling = ∅) (hep : p.enPassant = none) :
    KQState.ofPositionBlack? p = some s := by
  obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
  have hboardR : p.rot180.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
    rw [← hpos]; rfl
  have hboard : p.board =
      Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180 .black := by
    have hrot := congrArg Board.rot180 hboardR
    rw [rot180_board, Board.board_rot180_involutive,
      Board.rot180_kingsQueenBoard_white s.wk s.bk s.qs h1 h2 h3] at hrot
    exact hrot
  have htm : p.toMove.other = s.toMove := by
    have : s.toPosition.toMove = p.rot180.toMove := by rw [hpos]
    simpa [KQState.toPosition, rot180_toMove] using this.symm
  have hneWB : s.bk.rot180 ≠ s.wk.rot180 := Ne.symm (mt Board.rot180_injective h1)
  have hneWR : s.wk.rot180 ≠ s.qs.rot180 := mt Board.rot180_injective h2
  have hneBR : s.bk.rot180 ≠ s.qs.rot180 := mt Board.rot180_injective h3
  have hwk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.bk.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsQueenBoard_white])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.wk.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_black s.bk.rot180 s.wk.rot180 s.qs.rot180
          .black hneWB])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .queen }) = some s.qs.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_queen s.bk.rot180 s.wk.rot180 s.qs.rot180
          .black hneBR hneWR])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_queen (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KQState.allSquares.all fun q =>
      p.board q == Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180
        .black q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove.other, s.wk, s.bk, s.qs⟩ : KQState) = s := by
    cases s
    simp [htm]
  unfold KQState.ofPositionBlack?
  rw [hwk, hbk, hqs]
  simp [Square.rot180_involutive, hs, hok, hall, hcst, hep]

theorem kq_ofPositionWhite?_eq_none_of_black {p : Position} {wk bk qs : Square}
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .black) :
    KQState.ofPositionWhite? p = none := by
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .queen }) = none := by
    refine List.find?_eq_none.mpr ?_
    intro q _
    cases hb : (p.board q == some { color := .white, kind := .queen })
    · exact Bool.false_ne_true
    · have heq : p.board q = some { color := .white, kind := .queen } :=
        beq_iff_eq.mp hb
      rw [hboard] at heq
      unfold Board.kingsQueenBoard at heq
      split_ifs at heq <;> cases heq
  unfold KQState.ofPositionWhite?
  rw [hqs]
  split
  · rename_i _ _ _ heq
    cases heq
  · rfl

theorem kq_ofPosition?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPosition? p = some s) :
    s.okB = true ∧ (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  unfold KQState.ofPosition? at h
  split at h
  · rename_i s' hW
    injection h with hs
    subst hs
    have ⟨hok, hpos⟩ := kq_ofPositionWhite?_eq_some hW
    exact ⟨hok, Or.inl hpos⟩
  · have ⟨hok, hpos⟩ := kq_ofPositionBlack?_eq_some h
    exact ⟨hok, Or.inr hpos⟩

theorem kq_ofPosition?_complete {p : Position} (hv : Valid p) (h : IsKingAndQueen p) :
    ∃ s, KQState.ofPosition? p = some s ∧ s.okB = true ∧
      (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  rcases exists_kqState hv h with ⟨s, hok, hpos⟩ | ⟨s, hok, hpos⟩
  · refine ⟨s, ?_, hok, Or.inl hpos⟩
    unfold KQState.ofPosition?
    rw [kq_ofPositionWhite?_of_eq hok hpos]
  · refine ⟨s, ?_, hok, Or.inr hpos⟩
    obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
    have hboardR : p.rot180.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
      rw [← hpos]; rfl
    have hboard : p.board =
        Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180 .black := by
      have hrot := congrArg Board.rot180 hboardR
      rw [rot180_board, Board.board_rot180_involutive,
        Board.rot180_kingsQueenBoard_white s.wk s.bk s.qs h1 h2 h3] at hrot
      exact hrot
    unfold KQState.ofPosition?
    rw [kq_ofPositionWhite?_eq_none_of_black hboard,
      kq_ofPositionBlack?_of_eq hok hpos h.castling_eq h.enPassant_eq]

/-- The engineered mating line of a king-and-queen versus king position;
`[]` when the position is dead or not of this material. Black-queen
positions are rotated into the white-queen frame, and the resulting moves
are rotated back. -/
def kingQueenMatingLine (p : Position) : List Move :=
  match KQState.ofPositionWhite? p with
  | some s => s.matingLine
  | none =>
    match KQState.ofPositionBlack? p with
    | some s => s.matingLine.map Move.rot180
    | none => []

/-- Whether a king-and-queen versus king position is dead for helpmate
(`true` when the board is not of this material). -/
def kingQueenDead (p : Position) : Bool :=
  match KQState.ofPosition? p with
  | some s => s.deadB
  | none => true

/-- In a valid king-and-queen versus king position, checkmate is reachable
exactly when the corresponding three-piece state is not dead. -/
theorem IsKingAndQueen.checkmateReachable_iff {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p) :
    CheckmateReachable p ↔ kingQueenDead p = false := by
  obtain ⟨s, hs, hok, hpos⟩ := kq_ofPosition?_complete hv h
  have hdeq : kingQueenDead p = s.deadB := by simp [kingQueenDead, hs]
  rw [hdeq]
  exact h.checkmateReachable_iff_deadB hv hok hpos

/-- Decides whether checkmate is reachable from a valid king-and-queen
versus king position: exactly when the corresponding three-piece state
is not dead. -/
def kingQueenCheckmateReachable (p : Position) (hv : Valid p)
    (h : IsKingAndQueen p) : Decidable (CheckmateReachable p) :=
  decidable_of_iff (kingQueenDead p = false) (h.checkmateReachable_iff hv).symm

/-! ### Example: kings on `e1` and `e8`, white queen on `a1` -/

/-- White king on `e1`, black king on `e8`, white queen on `a1`, White to
move. -/
def kingQueenStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.a1 then some { color := .white, kind := .queen }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingQueenStart_isValid : isValid kingQueenStart = true := by
  native_decide

theorem kingQueenStart_valid : Valid kingQueenStart :=
  (isValid_eq_true_iff _).mp kingQueenStart_isValid

theorem kingQueenStart_isKingAndQueen : IsKingAndQueen kingQueenStart :=
  isKingAndQueen_of_valid kingQueenStart_valid (by native_decide)
    ⟨Square.a1, Color.white, by native_decide⟩ (by native_decide)

theorem kingQueenStart_CheckmateReachable : CheckmateReachable kingQueenStart :=
  kingQueenStart_isKingAndQueen.checkmateReachable_of_queenToMove kingQueenStart_valid
    ⟨Square.a1, by native_decide⟩

theorem kingQueenStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingQueenStart)
      (kingQueenCheckmateReachable kingQueenStart kingQueenStart_valid
        kingQueenStart_isKingAndQueen) = true := by
  native_decide

theorem kingQueenStart_not_deadPosition : ¬ DeadPosition kingQueenStart :=
  not_deadPosition_of_checkmateReachable kingQueenStart_CheckmateReachable

theorem kingQueenStart_matingLine_legal :
    pathLegal kingQueenStart (kingQueenMatingLine kingQueenStart) = true := by
  native_decide

theorem kingQueenStart_matingLine_inCheckmate :
    (playSeq kingQueenStart (kingQueenMatingLine kingQueenStart)).inCheckmate = true := by
  native_decide

theorem kingQueenStart_CheckmateReachable' : CheckmateReachable kingQueenStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingQueenStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingQueenStart_matingLine_inCheckmate)

/-- Forced capture of an unprotected queen: Black to move, in check, and
the only legal move takes the queen, leaving two kings. -/
def queenForcedCapture : Position where
  board := fun s =>
    if s = Square.c8 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenForcedCapture_isValid : isValid queenForcedCapture = true := by
  native_decide

theorem queenForcedCapture_valid : Valid queenForcedCapture :=
  (isValid_eq_true_iff _).mp queenForcedCapture_isValid

theorem queenForcedCapture_isKingAndQueen : IsKingAndQueen queenForcedCapture :=
  isKingAndQueen_of_valid queenForcedCapture_valid (by native_decide)
    ⟨Square.a7, Color.white, by native_decide⟩ (by native_decide)

theorem queenForcedCapture_deadB : ∃ s : KQState, s.okB = true ∧
    s.toPosition = queenForcedCapture ∧ s.deadB = true := by
  refine ⟨⟨.black, Square.c8, Square.a8, Square.a7⟩, by native_decide, ?_,
    by native_decide⟩
  have hboard : Board.kingsQueenBoard Square.c8 Square.a8 Square.a7 .white =
      queenForcedCapture.board := by
    funext q
    simp [queenForcedCapture, Board.kingsQueenBoard]
  simp [KQState.toPosition, queenForcedCapture, hboard, CastlingRights.empty]

theorem queenForcedCapture_not_CheckmateReachable :
    ¬ CheckmateReachable queenForcedCapture := by
  obtain ⟨s, hok, hpos, hd⟩ := queenForcedCapture_deadB
  intro hcr
  have := (queenForcedCapture_isKingAndQueen.checkmateReachable_iff_deadB
    queenForcedCapture_valid hok (Or.inl hpos)).mp hcr
  exact Bool.false_ne_true (this.symm.trans hd)

theorem queenForcedCapture_decide_CheckmateReachable :
    @decide (CheckmateReachable queenForcedCapture)
      (kingQueenCheckmateReachable queenForcedCapture queenForcedCapture_valid
        queenForcedCapture_isKingAndQueen) = false := by
  native_decide

theorem queenStalemate_isKingAndQueen : IsKingAndQueen queenStalemate :=
  isKingAndQueen_of_valid
    ((isValid_eq_true_iff queenStalemate).mp queenStalemate_isValid)
    (by native_decide) ⟨Square.f7, Color.white, by native_decide⟩ (by native_decide)

theorem queenStalemate_not_CheckmateReachable :
    ¬ CheckmateReachable queenStalemate :=
  not_CheckmateReachable_of_InStalemate
    ((inStalemate_eq_true_iff _).mp queenStalemate_inStalemate)

theorem queenStalemate_decide_CheckmateReachable :
    @decide (CheckmateReachable queenStalemate)
      (kingQueenCheckmateReachable queenStalemate
        ((isValid_eq_true_iff queenStalemate).mp queenStalemate_isValid)
        queenStalemate_isKingAndQueen) = false := by
  native_decide

theorem queenStalemate_deadPosition : DeadPosition queenStalemate :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr
    queenStalemate_not_CheckmateReachable

/-- The known `h7` mate is king-and-queen versus king, already checkmate. -/
theorem queenMate_isKingAndQueen : IsKingAndQueen queenMate :=
  isKingAndQueen_of_valid
    ((isValid_eq_true_iff queenMate).mp queenMate_isValid)
    (by native_decide) ⟨Square.h7, Color.white, by native_decide⟩ (by native_decide)

theorem queenMate_CheckmateReachable : CheckmateReachable queenMate :=
  checkmateReachable_of_inCheckmate
    ((inCheckmate_eq_true_iff _).mp queenMate_inCheckmate)

theorem queenMate_decide_CheckmateReachable :
    @decide (CheckmateReachable queenMate)
      (kingQueenCheckmateReachable queenMate
        ((isValid_eq_true_iff queenMate).mp queenMate_isValid)
        queenMate_isKingAndQueen) = true := by
  native_decide

theorem queenMate_matingLine_legal :
    pathLegal queenMate (kingQueenMatingLine queenMate) = true := by
  native_decide

theorem queenMate_matingLine_inCheckmate :
    (playSeq queenMate (kingQueenMatingLine queenMate)).inCheckmate = true := by
  native_decide

end Position

end Chess
