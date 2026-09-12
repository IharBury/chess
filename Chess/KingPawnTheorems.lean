import Chess.KingPawn
import Chess.KingKnight

/-!
# King and pawn versus king: reachability for either pawn color

`Chess.KingPawn` stores states in a white-pawn frame and shows that every
non-dead legal state in that frame can reach checkmate. This module
rotates a black-pawn position into that frame, transfers `CheckmateReachable`
across the rotation, and decides the property for an arbitrary valid
king-and-pawn versus king position.
-/

namespace Chess

namespace Board

theorem relocate_kingsPawnBoard_promote_queen (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate ps dst { color := c, kind := .queen } =
      kingsQueenBoard wk bk dst c := by
  funext s
  unfold relocate kingsPawnBoard kingsQueenBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_promote_rook (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate ps dst { color := c, kind := .rook } =
      kingsRookBoard wk bk dst c := by
  funext s
  unfold relocate kingsPawnBoard kingsRookBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_promote_bishop (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate ps dst { color := c, kind := .bishop } =
      kingsBishopBoard wk bk dst c := by
  funext s
  unfold relocate kingsPawnBoard kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_promote_knight (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate ps dst { color := c, kind := .knight } =
      kingsKnightBoard wk bk dst c := by
  funext s
  unfold relocate kingsPawnBoard kingsKnightBoard
  split_ifs <;> simp_all

theorem relocate_capture_pawn_white (wk bk ps : Square)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps) :
    (kingsPawnBoard wk bk ps .black).relocate wk ps
      { color := .white, kind := .king } =
      kingsBoard ps bk := by
  funext s
  unfold relocate kingsPawnBoard kingsBoard
  split_ifs <;> simp_all

theorem rot180_kingsBoard (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).rot180 = kingsBoard bk.rot180 wk.rot180 := by
  funext s
  have hne : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h)
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsBoard_white]
    change some { color := Color.black, kind := .king } =
      kingsBoard bk.rot180 wk.rot180 wk.rot180
    rw [kingsBoard_black bk.rot180 wk.rot180 hne]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsBoard_black wk bk h]
      change some { color := Color.white, kind := .king } =
        kingsBoard bk.rot180 wk.rot180 bk.rot180
      rw [kingsBoard_white]
    · have hsW : s ≠ wk.rot180 := fun h' => hA (rot180_eq_iff.mpr h')
      have hsB : s ≠ bk.rot180 := fun h' => hB (rot180_eq_iff.mpr h')
      rw [kingsBoard_other wk bk s.rot180 hA hB]
      change none = kingsBoard bk.rot180 wk.rot180 s
      rw [kingsBoard_other bk.rot180 wk.rot180 s hsB hsW]

end Board

namespace Position

theorem existsPawnAttacking_eq_false_of {b : Board} {c : Color} {t : Square}
    (h : ∀ s, b s ≠ some { color := c, kind := .pawn }) :
    existsPawnAttacking b c t = false := by
  cases h' : existsPawnAttacking b c t
  · rfl
  · obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp h'
    exact (h s ((hasPawn_eq_true_iff _ _ _).mp hs)).elim

theorem existsPawnAttacking_kingsPawnBoard_other (wk bk ps t : Square) (c : Color) :
    existsPawnAttacking (Board.kingsPawnBoard wk bk ps c) c.other t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsPawnBoard at hs
  split_ifs at hs <;> try simp at hs
  exact (Color.other_ne c) hs.symm

theorem existsPawnAttacking_kingsQueenBoard (wk bk qs t : Square) (c cq : Color) :
    existsPawnAttacking (Board.kingsQueenBoard wk bk qs c) cq t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsQueenBoard at hs
  split_ifs at hs <;> cases hs

theorem existsPawnAttacking_kingsRookBoard (wk bk rs t : Square) (c cq : Color) :
    existsPawnAttacking (Board.kingsRookBoard wk bk rs c) cq t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsRookBoard at hs
  split_ifs at hs <;> cases hs

theorem existsPawnAttacking_kingsBishopBoard (wk bk bs t : Square) (c cq : Color) :
    existsPawnAttacking (Board.kingsBishopBoard wk bk bs c) cq t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsBishopBoard at hs
  split_ifs at hs <;> cases hs

theorem existsPawnAttacking_kingsKnightBoard (wk bk ns t : Square) (c cq : Color) :
    existsPawnAttacking (Board.kingsKnightBoard wk bk ns c) cq t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsKnightBoard at hs
  split_ifs at hs <;> cases hs

theorem existsPawnAttacking_kingsBoard (wk bk t : Square) (c : Color) :
    existsPawnAttacking (Board.kingsBoard wk bk) c t = false := by
  refine existsPawnAttacking_eq_false_of ?_
  intro s hs
  unfold Board.kingsBoard at hs
  split_ifs at hs <;> cases hs

theorem file_beq_rot180 (s t : Square) :
    (s.file == t.file) = (s.rot180.file == t.rot180.file) := by
  revert s t
  native_decide

theorem rank_beq_promo_rot180 (c : Color) (s : Square) :
    (s.rank == pawnPromotionRank c) =
      (s.rot180.rank == pawnPromotionRank c.other) := by
  revert c s
  native_decide

theorem rank_beq_start_rot180 (c : Color) (s : Square) :
    (s.rank == pawnStartRank c) =
      (s.rot180.rank == pawnStartRank c.other) := by
  revert c s
  native_decide

theorem deltaRank_push_rot180 (c : Color) (s t : Square) :
    decide (Square.deltaRank s t = pawnPushDelta c) =
      decide (Square.deltaRank s.rot180 t.rot180 = pawnPushDelta c.other) := by
  revert c s t
  native_decide

theorem deltaRank_double_rot180 (c : Color) (s t : Square) :
    decide (Square.deltaRank s t = 2 * pawnPushDelta c) =
      decide (Square.deltaRank s.rot180 t.rot180 = 2 * pawnPushDelta c.other) := by
  revert c s t
  native_decide

theorem jumpOver_rot180 (c : Color) (s : Square) :
    (⟨s.file, pawnJumpOverRank c⟩ : Square).rot180 =
      ⟨s.rot180.file, pawnJumpOverRank c.other⟩ := by
  revert c s
  native_decide

theorem board_src_rot180 (p : Position) (m : Move) :
    p.rot180.board m.rot180.src = (p.board m.src).map Piece.flip := by
  simp [rot180_board, Move.rot180_src, Board.rot180, Square.rot180_involutive]

theorem board_dst_rot180 (p : Position) (m : Move) :
    p.rot180.board m.rot180.dst = (p.board m.dst).map Piece.flip := by
  simp [rot180_board, Move.rot180_dst, Board.rot180, Square.rot180_involutive]

theorem isNone_rot180 (p : Position) (s : Square) :
    (p.board s).isNone = (p.rot180.board s.rot180).isNone := by
  cases h : p.board s <;> simp [rot180_board, Board.rot180, Square.rot180_involutive, h]

theorem destEnemy_rot180 (p : Position) (m : Move) (c : Color) :
    (match p.board m.dst with
      | some q => (q.color != c) && (q.kind != PieceKind.king)
      | none => false) =
    (match p.rot180.board m.rot180.dst with
      | some q => (q.color != c.other) && (q.kind != PieceKind.king)
      | none => false) := by
  rw [board_dst_rot180]
  cases h : p.board m.dst with
  | none => simp
  | some q =>
    simp [Piece.flip]
    cases q.color <;> cases c <;> rfl

theorem pawnAttacks_decide_rot180 (c : Color) (s t : Square) :
    decide (PawnAttacks c s t) =
      decide (PawnAttacks c.other s.rot180 t.rot180) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  exact Square.pawnAttacks_rot180 c s t

/-- `pawnMoveOk` is invariant under 180° rotation when there is no en
passant target (both sides then have a false en-passant clause). -/
theorem pawnMoveOk_rot180 (p : Position) (m : Move) (he : p.enPassant = none) :
    p.pawnMoveOk m = p.rot180.pawnMoveOk m.rot180 := by
  unfold pawnMoveOk
  rw [board_src_rot180]
  cases hsrc : p.board m.src with
  | none => simp
  | some piece =>
    simp only [Option.map_some]
    have hpromo :
        (if m.dst.rank == pawnPromotionRank piece.color then
            match m.promotion with
            | some k => k.canPromoteTo
            | none => false
          else m.promotion == none) =
        (if m.rot180.dst.rank == pawnPromotionRank piece.flip.color then
            match m.rot180.promotion with
            | some k => k.canPromoteTo
            | none => false
          else m.rot180.promotion == none) := by
      simp only [Move.rot180_promotion, Move.rot180_dst, Piece.flip]
      rw [rank_beq_promo_rot180]
      rfl
    have hempty :
        (p.board m.dst).isNone = (p.rot180.board m.rot180.dst).isNone :=
      isNone_rot180 p m.dst
    have hsingle :
        ((m.dst.file == m.src.file) &&
          decide (Square.deltaRank m.src m.dst = pawnPushDelta piece.color) &&
          (p.board m.dst).isNone) =
        ((m.rot180.dst.file == m.rot180.src.file) &&
          decide (Square.deltaRank m.rot180.src m.rot180.dst =
            pawnPushDelta piece.flip.color) &&
          (p.rot180.board m.rot180.dst).isNone) := by
      simp only [Move.rot180_src, Move.rot180_dst, Piece.flip]
      rw [file_beq_rot180, deltaRank_push_rot180, hempty]
      rfl
    have hmid : (p.board ⟨m.src.file, pawnJumpOverRank piece.color⟩).isNone =
        (p.rot180.board ⟨m.rot180.src.file, pawnJumpOverRank piece.flip.color⟩).isNone := by
      have hj := jumpOver_rot180 piece.color m.src
      have : (⟨m.src.file, pawnJumpOverRank piece.color⟩ : Square).rot180 =
          ⟨m.rot180.src.file, pawnJumpOverRank piece.flip.color⟩ := by
        simpa [Move.rot180_src, Piece.flip] using hj
      simpa [this] using isNone_rot180 p ⟨m.src.file, pawnJumpOverRank piece.color⟩
    have hdouble :
        ((m.src.rank == pawnStartRank piece.color) &&
          (m.dst.file == m.src.file) &&
          decide (Square.deltaRank m.src m.dst = 2 * pawnPushDelta piece.color) &&
          (p.board m.dst).isNone &&
          (p.board ⟨m.src.file, pawnJumpOverRank piece.color⟩).isNone) =
        ((m.rot180.src.rank == pawnStartRank piece.flip.color) &&
          (m.rot180.dst.file == m.rot180.src.file) &&
          decide (Square.deltaRank m.rot180.src m.rot180.dst =
            2 * pawnPushDelta piece.flip.color) &&
          (p.rot180.board m.rot180.dst).isNone &&
          (p.rot180.board ⟨m.rot180.src.file,
            pawnJumpOverRank piece.flip.color⟩).isNone) := by
      simp only [Move.rot180_src, Move.rot180_dst, Piece.flip]
      rw [rank_beq_start_rot180, file_beq_rot180, deltaRank_double_rot180,
        hempty, hmid]
      rfl
    have hcap :
        (decide (PawnAttacks piece.color m.src m.dst) &&
          (match p.board m.dst with
            | some q => (q.color != piece.color) && (q.kind != PieceKind.king)
            | none => false)) =
        (decide (PawnAttacks piece.flip.color m.rot180.src m.rot180.dst) &&
          (match p.rot180.board m.rot180.dst with
            | some q => (q.color != piece.flip.color) && (q.kind != PieceKind.king)
            | none => false)) := by
      simp only [Move.rot180_src, Move.rot180_dst, Piece.flip]
      rw [pawnAttacks_decide_rot180, destEnemy_rot180]
      rfl
    have hep : (p.enPassant == some m.dst) = false := by simp [he]
    have hepR : (p.rot180.enPassant == some m.rot180.dst) = false := by
      simp [rot180]
    have hepBoth :
        (decide (PawnAttacks piece.color m.src m.dst) &&
          (p.board m.dst).isNone && (p.enPassant == some m.dst)) =
        (decide (PawnAttacks piece.flip.color m.rot180.src m.rot180.dst) &&
          (p.rot180.board m.rot180.dst).isNone &&
            (p.rot180.enPassant == some m.rot180.dst)) := by
      simp only [hep, hepR, Bool.and_false]
    apply congrArg₂ (· && ·)
    · apply congrArg₂ (· || ·)
      · apply congrArg₂ (· || ·)
        · apply congrArg₂ (· || ·)
          · exact hsingle
          · exact hdouble
        · exact hcap
      · exact hepBoth
    · exact hpromo

theorem IsKingAndPawn.castling_eq {p : Position} (h : IsKingAndPawn p) :
    p.castling = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

theorem IsKingAndPawn.enPassant_eq {p : Position} (h : IsKingAndPawn p) :
    p.enPassant = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := h
  exact he

theorem IsKingAndPawn.rot180 {p : Position} (h : IsKingAndPawn p) :
    IsKingAndPawn p.rot180 := by
  obtain ⟨wk, bk, ps, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
  have h2' : wk.rot180 ≠ ps.rot180 := mt Board.rot180_injective h2
  have h3' : bk.rot180 ≠ ps.rot180 := mt Board.rot180_injective h3
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  cases c with
  | white =>
    refine ⟨bk.rot180, wk.rot180, ps.rot180, .black, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsPawnBoard_white wk bk ps h1 h2 h3]
  | black =>
    refine ⟨bk.rot180, wk.rot180, ps.rot180, .white, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsPawnBoard_black wk bk ps h1 h2 h3]

theorem IsKingAndPawn.not_IsTwoKings {p : Position} (h : IsKingAndPawn p) :
    ¬ IsTwoKings p := by
  intro htk
  obtain ⟨wk, bk, ps, c, h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', hne', _, hboard', _, _⟩ := htk
  have h3c : p.board.occupied.card = 3 := by
    rw [hboard, Board.kingsPawnBoard_occupied wk bk ps c h1 h2 h3]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [h3]
    · simp [h1, h2]
  have h2c : p.board.occupied.card = 2 := by
    rw [hboard', Board.kingsBoard_occupied wk' bk' hne']
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne']
  omega

theorem IsTwoKings.rot180 {p : Position} (h : IsTwoKings p) :
    IsTwoKings p.rot180 := by
  obtain ⟨wk, bk, hne, hna, hboard, hc, he⟩ := h
  have hne' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm hne)
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  refine ⟨bk.rot180, wk.rot180, hne', hna', ?_, rfl, rfl⟩
  rw [rot180_board, hboard, Board.rot180_kingsBoard wk bk hne]

theorem piece_eq_of_board {p : Position} {s : Square} {piece q : Piece}
    (h1 : p.board s = some piece) (h2 : p.board s = some q) : piece = q :=
  Option.some.inj (h1.symm.trans h2)

theorem piece_of_kind_pawn (piece : Piece) (hk : piece.kind = .pawn) :
    piece = { color := piece.color, kind := .pawn } := by
  rcases piece with ⟨pc, pk⟩
  subst hk
  rfl

theorem some_pawn_ne_queen {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .pawn } : Option Piece) =
      some { color := c₂, kind := .queen }) : False := by
  simp at h

theorem some_pawn_ne_rook {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .pawn } : Option Piece) =
      some { color := c₂, kind := .rook }) : False := by
  simp at h

theorem pawnMoveOk_promotion_of {p : Position} {m : Move} {c : Color}
    (hsrc : p.board m.src = some { color := c, kind := .pawn })
    (hpok : p.pawnMoveOk m = true) :
    (m.dst.rank = pawnPromotionRank c ∧ ∃ k, m.promotion = some k ∧ k.canPromoteTo = true) ∨
      (m.dst.rank ≠ pawnPromotionRank c ∧ m.promotion = none) := by
  unfold pawnMoveOk at hpok
  rw [hsrc] at hpok
  simp only [Bool.and_eq_true] at hpok
  have hpr := hpok.2
  by_cases hr : m.dst.rank = pawnPromotionRank c
  · have : (m.dst.rank == pawnPromotionRank c) = true := by simp [hr]
    simp only [this, ↓reduceIte] at hpr
    match hpromo : m.promotion with
    | none =>
      simp only [hpromo] at hpr
      exact (Bool.false_ne_true hpr).elim
    | some k =>
      simp only [hpromo] at hpr
      exact Or.inl ⟨hr, k, rfl, hpr⟩
  · have : (m.dst.rank == pawnPromotionRank c) = false := by
      cases h : (m.dst.rank == pawnPromotionRank c)
      · rfl
      · exact (hr (beq_iff_eq.mp h)).elim
    simp only [this, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hpr
    exact Or.inr ⟨hr, hpr⟩

inductive KingPawnPlay (p : Position) : Prop where
  | stay : IsKingAndPawn p → KingPawnPlay p
  | queen : IsKingAndQueen p → KingPawnPlay p
  | rook : IsKingAndRook p → KingPawnPlay p
  | bishop : IsKingAndBishop p → KingPawnPlay p
  | knight : IsKingAndKnight p → KingPawnPlay p
  | two : IsTwoKings p → KingPawnPlay p

theorem KingPawnPlay.not_InCheckmate {p : Position} (h : KingPawnPlay p)
    (hm : InCheckmate p) :
    IsKingAndPawn p ∨ IsKingAndQueen p ∨ IsKingAndRook p := by
  cases h with
  | stay h => exact Or.inl h
  | queen h => exact Or.inr (Or.inl h)
  | rook h => exact Or.inr (Or.inr h)
  | bishop h => exact (h.not_InCheckmate hm).elim
  | knight h => exact (h.not_InCheckmate hm).elim
  | two h => exact (h.not_InCheckmate hm).elim

theorem IsKingAndPawn.of_play {p : Position} {m : Move}
    (h : IsKingAndPawn p) (hm : LegalMove p m) :
    KingPawnPlay (p.play m) := by
  obtain ⟨wk, bk, ps, c, hwk_bk, hwk_ps, hbk_ps, hna, hboard, hcstl, hep⟩ := h
  obtain ⟨hdestOk, hdstOr, hsafe, piece, hsrcP, hcol', hkind, hside, hpawn⟩ :=
    kingPawn_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = ps :=
    (Board.kingsPawnBoard_isSome wk bk ps m.src c).mp (by
      have : (p.board m.src).isSome = true := by simp [hsrcP]
      simpa [hboard] using this)
  have hcast' : (p.play m).castling = ∅ := by
    rw [hplay]
    cases hkind with
    | inl hk =>
      have hpiece : piece = { color := p.toMove, kind := .king } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_king_no_castle p m (c := p.toMove)
        (hside (by simp [hpiece])).1 (hside (by simp [hpiece])).2.1, hcstl]
      exact castlingAfter_empty _
    | inr hb =>
      have hpiece : piece = { color := p.toMove, kind := .pawn } := by
        cases piece; simp_all
      have hba := boardAfter_pawn p m (c := p.toMove) hep
      rw [hpiece, hba, hcstl]
      exact castlingAfter_empty _
  rcases hdstOr with hdstNone | hdstPs
  · have hdstW : m.dst ≠ wk := by
      intro heq; rw [heq, hboard, Board.kingsPawnBoard_white] at hdstNone; cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsPawnBoard_black wk bk ps c hwk_bk] at hdstNone
      cases hdstNone
    have hdstS : m.dst ≠ ps := by
      intro heq
      rw [heq, hboard, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps] at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_board hsrcP (by rw [hsrcW, hboard, Board.kingsPawnBoard_white])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using (hside (by simp [hpiece])).1)
        (hside (by simp [hpiece])).2.1
      have hrel := Board.relocate_kingsPawnBoard_white wk bk ps m.dst c
        hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsPawnBoard m.dst bk ps c := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsPawnBoard wk bk ps c).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsPawnBoard m.dst bk ps c := hrel
      have hep' : (p.play m).enPassant = none := by
        rw [hplay, hpiece]
        exact enPassantAfter_king m Color.white
          (p.boardAfter m { color := .white, kind := .king })
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by simpa [ht] using hsafe
        have hiff := Board.kingsPawnBoard_kingIsAttacked_white m.dst bk ps c
          hdstB hdstS hbk_ps
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact KingPawnPlay.stay
        ⟨m.dst, bk, ps, c, hdstB, hdstS, hbk_ps, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_board hsrcP (by
          rw [hsrcB, hboard, Board.kingsPawnBoard_black wk bk ps c hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using (hside (by simp [hpiece])).1)
        (hside (by simp [hpiece])).2.1
      have hrel := Board.relocate_kingsPawnBoard_black wk bk ps m.dst c
        hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsPawnBoard wk m.dst ps c := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsPawnBoard wk bk ps c).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsPawnBoard wk m.dst ps c := hrel
      have hep' : (p.play m).enPassant = none := by
        rw [hplay, hpiece]
        exact enPassantAfter_king m Color.black
          (p.boardAfter m { color := .black, kind := .king })
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by simpa [ht] using hsafe
        have hiff := Board.kingsPawnBoard_kingIsAttacked_black wk m.dst ps c
          hdstW.symm hwk_ps hdstS
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact KingPawnPlay.stay
        ⟨wk, m.dst, ps, c, hdstW.symm, hwk_ps, hdstS, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := c, kind := .pawn } :=
        piece_eq_of_board hsrcP (by
          rw [hsrcS, hboard, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps])
      have ht : p.toMove = c := by simpa [hpiece] using hcol'.symm
      have hpok : p.pawnMoveOk m = true := hpawn (by simp [hpiece])
      have hba := boardAfter_pawn p m (c := c) hep
      rcases pawnMoveOk_promotion_of
          (by rw [hsrcS, hboard, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps])
          hpok with
        ⟨_, k, hpr, hk⟩ | ⟨_, hnone⟩
      · have hplaced : (match m.promotion with
            | some k' => Piece.mk c k'
            | none => Piece.mk c PieceKind.pawn) =
            Piece.mk c k := by simp [hpr]
        have hboardRel :
            p.boardAfter m { color := c, kind := .pawn } =
              (Board.kingsPawnBoard wk bk ps c).relocate ps m.dst
                { color := c, kind := k } := by
          rw [hba, hboard, hsrcS]
          exact congrArg ((Board.kingsPawnBoard wk bk ps c).relocate ps m.dst) hplaced
        cases k with
        | pawn | king => simp [PieceKind.canPromoteTo] at hk
        | queen =>
          have hboard' : (p.play m).board = Board.kingsQueenBoard wk bk m.dst c := by
            rw [hplay, hpiece, hboardRel]
            exact Board.relocate_kingsPawnBoard_promote_queen wk bk ps m.dst c
              hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
          have hep'' : (p.play m).enPassant = none := by
            rw [hplay, hpiece]
            exact enPassantAfter_pawn_no_enemy m c
              (p.boardAfter m { color := c, kind := .pawn })
              (by
                rw [hboardRel]
                rw [Board.relocate_kingsPawnBoard_promote_queen wk bk ps m.dst c
                  hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS]
                exact existsPawnAttacking_kingsQueenBoard wk bk m.dst
                  ⟨m.src.file, pawnJumpOverRank c⟩ c c.other)
          exact KingPawnPlay.queen
            ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep''⟩
        | rook =>
          have hboard' : (p.play m).board = Board.kingsRookBoard wk bk m.dst c := by
            rw [hplay, hpiece, hboardRel]
            exact Board.relocate_kingsPawnBoard_promote_rook wk bk ps m.dst c
              hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
          have hep'' : (p.play m).enPassant = none := by
            rw [hplay, hpiece]
            exact enPassantAfter_pawn_no_enemy m c
              (p.boardAfter m { color := c, kind := .pawn })
              (by
                rw [hboardRel]
                rw [Board.relocate_kingsPawnBoard_promote_rook wk bk ps m.dst c
                  hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS]
                exact existsPawnAttacking_kingsRookBoard wk bk m.dst
                  ⟨m.src.file, pawnJumpOverRank c⟩ c c.other)
          exact KingPawnPlay.rook
            ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep''⟩
        | bishop =>
          have hboard' : (p.play m).board = Board.kingsBishopBoard wk bk m.dst c := by
            rw [hplay, hpiece, hboardRel]
            exact Board.relocate_kingsPawnBoard_promote_bishop wk bk ps m.dst c
              hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
          have hep'' : (p.play m).enPassant = none := by
            rw [hplay, hpiece]
            exact enPassantAfter_pawn_no_enemy m c
              (p.boardAfter m { color := c, kind := .pawn })
              (by
                rw [hboardRel]
                rw [Board.relocate_kingsPawnBoard_promote_bishop wk bk ps m.dst c
                  hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS]
                exact existsPawnAttacking_kingsBishopBoard wk bk m.dst
                  ⟨m.src.file, pawnJumpOverRank c⟩ c c.other)
          exact KingPawnPlay.bishop
            ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep''⟩
        | knight =>
          have hboard' : (p.play m).board = Board.kingsKnightBoard wk bk m.dst c := by
            rw [hplay, hpiece, hboardRel]
            exact Board.relocate_kingsPawnBoard_promote_knight wk bk ps m.dst c
              hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
          have hep'' : (p.play m).enPassant = none := by
            rw [hplay, hpiece]
            exact enPassantAfter_pawn_no_enemy m c
              (p.boardAfter m { color := c, kind := .pawn })
              (by
                rw [hboardRel]
                rw [Board.relocate_kingsPawnBoard_promote_knight wk bk ps m.dst c
                  hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS]
                exact existsPawnAttacking_kingsKnightBoard wk bk m.dst
                  ⟨m.src.file, pawnJumpOverRank c⟩ c c.other)
          exact KingPawnPlay.knight
            ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep''⟩
      · have hboard' : (p.play m).board = Board.kingsPawnBoard wk bk m.dst c := by
          rw [hplay, hpiece, hba, hboard, hsrcS, hnone]
          exact Board.relocate_kingsPawnBoard_pawn wk bk ps m.dst c
            hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS
        have hep' : (p.play m).enPassant = none := by
          rw [hplay, hpiece]
          exact enPassantAfter_pawn_no_enemy m c
            (p.boardAfter m { color := c, kind := .pawn })
            (by
              rw [hba, hboard, hsrcS, hnone]
              rw [Board.relocate_kingsPawnBoard_pawn wk bk ps m.dst c
                hwk_bk hwk_ps hbk_ps hdstW hdstB hdstS]
              exact existsPawnAttacking_kingsPawnBoard_other wk bk m.dst
                ⟨ps.file, pawnJumpOverRank c⟩ c)
        exact KingPawnPlay.stay
          ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep'⟩
  · have ht : p.toMove = c.other :=
      destOk_toMove_of_dst_pawn hboard hwk_ps hbk_ps hdstPs hdestOk
    have hsrcNePs : m.src ≠ ps := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hboard, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps] at hsrcP'
      have hpc : c = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      exact Color.other_ne c hpc.symm
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_board hsrcP (by rw [hsrcW, hboard, Board.kingsPawnBoard_white])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.black := by
        have : c.other = Color.white := ht.symm.trans htW
        cases c
        · simp [Color.other] at this
        · rfl
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [htW] using (hside (by simp [hpiece])).1)
        (hside (by simp [hpiece])).2.1
      have hrel := Board.relocate_capture_pawn_white wk bk ps hwk_bk hwk_ps hbk_ps
      have hboard' : (p.play m).board = Board.kingsBoard ps bk := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsPawnBoard wk bk ps .black).relocate wk ps
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstPs, hc]
          _ = Board.kingsBoard ps bk := hrel
      have hep' : (p.play m).enPassant = none := by
        rw [hplay, hpiece]
        exact enPassantAfter_king m Color.white
          (p.boardAfter m { color := .white, kind := .king })
      have hna' : ¬ KingAttacks ps bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [htW] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_white ps bk hbk_ps.symm] at hsafe'
        exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
      exact KingPawnPlay.two ⟨ps, bk, hbk_ps.symm, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_board hsrcP (by
          rw [hsrcB, hboard, Board.kingsPawnBoard_black wk bk ps c hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.white := by
        have : c.other = Color.black := ht.symm.trans htB
        cases c
        · rfl
        · simp [Color.other] at this
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [htB] using (hside (by simp [hpiece])).1)
        (hside (by simp [hpiece])).2.1
      have hrel := Board.relocate_capture_pawn_black wk bk ps hwk_bk hwk_ps hbk_ps
      have hboard' : (p.play m).board = Board.kingsBoard wk ps := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsPawnBoard wk bk ps .white).relocate bk ps
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstPs, hc]
          _ = Board.kingsBoard wk ps := hrel
      have hep' : (p.play m).enPassant = none := by
        rw [hplay, hpiece]
        exact enPassantAfter_king m Color.black
          (p.boardAfter m { color := .black, kind := .king })
      have hna' : ¬ KingAttacks wk ps := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [htB] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_black wk ps hwk_ps] at hsafe'
        exact of_decide_eq_false hsafe'
      exact KingPawnPlay.two ⟨wk, ps, hwk_ps, hna', hboard', hcast', hep'⟩
    · exact (hsrcNePs hsrcS).elim

theorem IsKingAndPawn.of_reachable {p q : Position}
    (h : IsKingAndPawn p) (hr : Reachable p q) : KingPawnPlay q := by
  induction hr with
  | refl => exact KingPawnPlay.stay h
  | step m _hm hleg ih =>
    cases ih with
    | stay hkp => exact hkp.of_play hleg
    | queen hq =>
      rcases hq.of_play hleg with hq' | htk
      · exact KingPawnPlay.queen hq'
      · exact KingPawnPlay.two htk
    | rook hrk =>
      rcases hrk.of_play hleg with hrk' | htk
      · exact KingPawnPlay.rook hrk'
      · exact KingPawnPlay.two htk
    | bishop hb =>
      rcases hb.of_play hleg with hb' | htk
      · exact KingPawnPlay.bishop hb'
      · exact KingPawnPlay.two htk
    | knight hn =>
      rcases hn.of_play hleg with hn' | htk
      · exact KingPawnPlay.knight hn'
      · exact KingPawnPlay.two htk
    | two htk => exact KingPawnPlay.two (htk.of_play hleg)

theorem relocate_no_pawn_of_color (b : Board) (src dst : Square) (placed : Piece)
    (c : Color)
    (h : ∀ s, b s ≠ some { color := c, kind := .pawn })
    (hpl : placed ≠ { color := c, kind := .pawn }) :
    ∀ s, (b.relocate src dst placed) s ≠ some { color := c, kind := .pawn } := by
  intro s hs
  unfold Board.relocate at hs
  by_cases hdst : s = dst
  · rw [if_pos hdst] at hs
    injection hs with heq
    exact hpl heq
  · rw [if_neg hdst] at hs
    by_cases hsrc : s = src
    · rw [if_pos hsrc] at hs
      cases hs
    · rw [if_neg hsrc] at hs
      exact h s hs

theorem IsKingAndPawn.play_rot180 {p : Position} {m : Move}
    (h : IsKingAndPawn p) (hm : LegalMove p m) :
    (p.play m).rot180 = p.rot180.play m.rot180 := by
  obtain ⟨_wk, _bk, _ps, _c, _h1, _h2, _h3, _, hboard, hc, he⟩ := h
  obtain ⟨_, _, _, piece, hsrc, hpc, hkind, hside, _hpawn⟩ :=
    kingPawn_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hplay := play_of_some p m hsrc
  have hplayR := play_of_some p.rot180 m.rot180 hsrcR
  cases hkind with
  | inl hk =>
    have hpiece := piece_of_kind_king piece hk
    have hs : m.castlingSide? piece.color = none := by
      simpa [hpc] using (hside hk).1
    have hpromo : m.promotion = none := (hside hk).2.1
    have hba := boardAfter_king_no_castle p m (c := piece.color) hs hpromo
    have hka : KingAttacks m.src m.dst := by
      have hatt' : p.board.attacks m.src m.dst = true := (hside hk).2.2
      rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
      exact of_decide_eq_true hatt'
    have hsR : m.rot180.castlingSide? piece.flip.color = none := by
      have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
        rcases m with ⟨s, d, pr⟩
        simp [Move.rot180, Move.std] at hpromo ⊢
        simp [hpromo]
      rw [hmstd]
      exact KPState.castlingSide_none_of_kingAttacks _
        ((Square.kingAttacks_rot180 _ _).mp hka)
    have hbaR := boardAfter_king_no_castle p.rot180 m.rot180
      (c := piece.flip.color) hsR (by simpa [Move.rot180] using hpromo)
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
    have hpiece := piece_of_kind_pawn piece hr
    have hba := boardAfter_pawn p m (c := piece.color) he
    have hbaR := boardAfter_pawn p.rot180 m.rot180 (c := piece.flip.color) rfl
    have hno : ∀ s, p.board s ≠ some { color := piece.color.other, kind := .pawn } := by
      intro s hs
      have hsrc' : Board.kingsPawnBoard _wk _bk _ps _c m.src =
          some { color := piece.color, kind := .pawn } := by
        rw [← hboard, ← hpiece]; exact hsrc
      have hcol : piece.color = _c := by
        have hmem : m.src = _wk ∨ m.src = _bk ∨ m.src = _ps :=
          (Board.kingsPawnBoard_isSome _wk _bk _ps m.src _c).mp (by simp [hsrc'])
        rcases hmem with hwk | hbk | hps
        · rw [hwk, Board.kingsPawnBoard_white] at hsrc'
          cases some_king_ne_pawn' hsrc'
        · rw [hbk, Board.kingsPawnBoard_black _wk _bk _ps _c _h1] at hsrc'
          cases some_king_ne_pawn' hsrc'
        · rw [hps, Board.kingsPawnBoard_pawn _wk _bk _ps _c _h2 _h3] at hsrc'
          injection hsrc' with hpeq
          exact (congrArg Piece.color hpeq).symm
      rw [hboard] at hs
      have hmem : s = _wk ∨ s = _bk ∨ s = _ps :=
        (Board.kingsPawnBoard_isSome _wk _bk _ps s _c).mp (by simp [hs])
      rcases hmem with hwk | hbk | hps
      · rw [hwk, Board.kingsPawnBoard_white] at hs
        cases some_king_ne_pawn' hs
      · rw [hbk, Board.kingsPawnBoard_black _wk _bk _ps _c _h1] at hs
        cases some_king_ne_pawn' hs
      · rw [hps, Board.kingsPawnBoard_pawn _wk _bk _ps _c _h2 _h3] at hs
        injection hs with hpeq
        exact (Color.other_ne piece.color) (hcol.trans (congrArg Piece.color hpeq)).symm
    have hplaced :
        (match m.promotion with
          | some k => Piece.mk piece.color k
          | none => Piece.mk piece.color PieceKind.pawn) ≠
          Piece.mk piece.color.other PieceKind.pawn := by
      intro heq
      cases hpr : m.promotion
      · simp only [hpr] at heq
        injection heq with hcol
        exact (Color.other_ne piece.color) hcol.symm
      · simp only [hpr] at heq
        injection heq with hcol
        exact (Color.other_ne piece.color) hcol.symm
    have hplacedR :
        (match m.rot180.promotion with
          | some k => Piece.mk piece.flip.color k
          | none => Piece.mk piece.flip.color PieceKind.pawn) ≠
          Piece.mk piece.flip.color.other PieceKind.pawn := by
      intro heq
      cases hpr : m.rot180.promotion
      · simp only [hpr] at heq
        injection heq with hcol
        exact (Color.other_ne piece.flip.color) hcol.symm
      · simp only [hpr] at heq
        injection heq with hcol
        exact (Color.other_ne piece.flip.color) hcol.symm
    have hnoR : ∀ s, p.rot180.board s ≠
        some { color := piece.flip.color.other, kind := .pawn } := by
      intro s hs
      have : p.board s.rot180 = some { color := piece.color.other, kind := .pawn } := by
        rw [rot180_board] at hs
        change (p.board s.rot180).map Piece.flip =
          some { color := piece.flip.color.other, kind := .pawn } at hs
        cases hb : p.board s.rot180 with
        | none => simp [hb] at hs
        | some q =>
          simp only [hb, Option.map_some] at hs
          injection hs with hs'
          have hk : q.kind = PieceKind.pawn := by
            have := congrArg Piece.kind hs'
            simpa [Piece.flip] using this
          have hcol : q.color.other = piece.color := by
            have := congrArg Piece.color hs'
            simpa [Piece.flip] using this
          have hqc' : q.color = piece.color.other := by
            have h := congrArg Color.other hcol
            simpa [Color.other_other] using h
          rcases q with ⟨qc, qk⟩
          simp only at hqc' hk
          simp [hqc', hk]
      exact hno s.rot180 this
    have hep := enPassantAfter_pawn_no_enemy m piece.color
      (p.boardAfter m { color := piece.color, kind := .pawn })
      (existsPawnAttacking_eq_false_of (by
        intro s hs
        rw [hba] at hs
        exact relocate_no_pawn_of_color p.board m.src m.dst _ piece.color.other
          hno hplaced s hs))
    have hepR := enPassantAfter_pawn_no_enemy m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 { color := piece.flip.color, kind := .pawn })
      (existsPawnAttacking_eq_false_of (by
        intro s hs
        rw [hbaR] at hs
        exact relocate_no_pawn_of_color p.rot180.board m.rot180.src m.rot180.dst _
          piece.flip.color.other hnoR hplacedR s hs))
    have hflipPlaced :
        (match m.promotion with
          | some k => Piece.mk piece.color k
          | none => Piece.mk piece.color PieceKind.pawn).flip =
        (match m.rot180.promotion with
          | some k => Piece.mk piece.flip.color k
          | none => Piece.mk piece.flip.color PieceKind.pawn) := by
      cases h : m.promotion <;> simp [h, Move.rot180_promotion, Piece.flip]
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · have hpl := Board.relocate_rot180 p.board m.src m.dst
          (match m.promotion with
            | some k => Piece.mk piece.color k
            | none => Piece.mk piece.color PieceKind.pawn)
      change
        (p.board.relocate m.src m.dst
            (match m.promotion with
              | some k => Piece.mk piece.color k
              | none => Piece.mk piece.color PieceKind.pawn)).rot180 =
          p.rot180.board.relocate m.rot180.src m.rot180.dst
            (match m.rot180.promotion with
              | some k => Piece.mk piece.flip.color k
              | none => Piece.mk piece.flip.color PieceKind.pawn)
      rw [hpl, rot180_board, Move.rot180_src, Move.rot180_dst, hflipPlaced]
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · have hflipPawn : ({ color := piece.color, kind := PieceKind.pawn } : Piece).flip =
          { color := piece.flip.color, kind := .pawn } := rfl
      simpa [hflipPawn, Piece.flip] using hepR.symm

theorem IsKingAndPawn.legalMove_rot180_of {p : Position} {m : Move}
    (h : IsKingAndPawn p) (hm : LegalMove p m) :
    LegalMove p.rot180 m.rot180 := by
  obtain ⟨wk, bk, ps, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  obtain ⟨hdestOk, _, hsafe, piece, hsrc, hpc, hkind, hside, hpawn⟩ :=
    kingPawn_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hdestR : p.rot180.destOk m.rot180 = true := by
    rwa [← destOk_rot180]
  have hsafeR :
      (p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove = false := by
    have hpl := IsKingAndPawn.play_rot180
      (⟨wk, bk, ps, c, h1, h2, h3, hna, hboard, hc, he⟩ : IsKingAndPawn p) hm
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
  cases hkind with
  | inl hk =>
    have hnpawn : (piece.flip.kind == PieceKind.pawn) = false := by simp [Piece.flip, hk]
    have hs : m.rot180.castlingSide? p.rot180.toMove = none := by
      have hpromo : m.promotion = none := (hside hk).2.1
      have hka : KingAttacks m.src m.dst := by
        have hpiece := piece_of_kind_king piece hk
        have hatt' : p.board.attacks m.src m.dst = true := (hside hk).2.2
        rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
        exact of_decide_eq_true hatt'
      have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
        rcases m with ⟨s, d, pr⟩
        simp [Move.rot180, Move.std] at hpromo ⊢
        simp [hpromo]
      rw [hmstd]
      exact KPState.castlingSide_none_of_kingAttacks p.rot180.toMove
        ((Square.kingAttacks_rot180 _ _).mp hka)
    have hkingB : (piece.flip.kind == PieceKind.king &&
        (m.rot180.castlingSide? p.rot180.toMove).isSome) = false := by
      simp [Piece.flip, hk, hs]
    have hattR : p.rot180.board.attacks m.rot180.src m.rot180.dst = true := by
      have hatt : p.board.attacks m.src m.dst = true := (hside hk).2.2
      rw [rot180_board, Move.rot180_src, Move.rot180_dst, ← Board.attacks_rot180, hatt]
    simp only [hnpawn, hkingB]
    exact legal_king_step_bool _ _ _
      hattR (by simp [Move.rot180, (hside hk).2.1]) hsafeR
  | inr hr =>
    have hpawnB : (piece.flip.kind == PieceKind.pawn) = true := by simp [Piece.flip, hr]
    have hpok : p.pawnMoveOk m = true := hpawn hr
    have hpokR : p.rot180.pawnMoveOk m.rot180 = true := by
      rw [← pawnMoveOk_rot180 p m he]
      exact hpok
    simp only [hpawnB]
    have hsafeB :
        (!(p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove) = true := by
      simpa using hsafeR
    exact Bool.and_eq_true_iff.mpr ⟨hpokR, hsafeB⟩

theorem IsKingAndPawn.legalMove_rot180 {p : Position} {m : Move}
    (h : IsKingAndPawn p) :
    LegalMove p m ↔ LegalMove p.rot180 m.rot180 := by
  constructor
  · exact legalMove_rot180_of h
  · intro hm
    have := legalMove_rot180_of h.rot180 (m := m.rot180) hm
    simpa [rot180_involutive h.castling_eq h.enPassant_eq, Move.rot180_involutive]
      using this

theorem IsKingAndPawn.inCheckmate_rot180 {p : Position} (h : IsKingAndPawn p)
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

theorem IsKingAndPawn.not_IsKingAndQueen {p : Position} (h : IsKingAndPawn p) :
    ¬ IsKingAndQueen p := by
  intro hq
  obtain ⟨wk, bk, ps, c, _h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', qs, c', _, _, _, _, hboard', _, _⟩ := hq
  have hp : p.board ps = some { color := c, kind := .pawn } := by
    rw [hboard, Board.kingsPawnBoard_pawn wk bk ps c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsQueenBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndPawn.not_IsKingAndRook {p : Position} (h : IsKingAndPawn p) :
    ¬ IsKingAndRook p := by
  intro hr
  obtain ⟨wk, bk, ps, c, _h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', rs, c', _, _, _, _, hboard', _, _⟩ := hr
  have hp : p.board ps = some { color := c, kind := .pawn } := by
    rw [hboard, Board.kingsPawnBoard_pawn wk bk ps c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsRookBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndPawn.not_IsKingAndBishop {p : Position} (h : IsKingAndPawn p) :
    ¬ IsKingAndBishop p := by
  intro hb
  obtain ⟨wk, bk, ps, c, _h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', bs, c', _, _, _, _, hboard', _, _⟩ := hb
  have hp : p.board ps = some { color := c, kind := .pawn } := by
    rw [hboard, Board.kingsPawnBoard_pawn wk bk ps c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsBishopBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndPawn.not_IsKingAndKnight {p : Position} (h : IsKingAndPawn p) :
    ¬ IsKingAndKnight p := by
  intro hn
  obtain ⟨wk, bk, ps, c, _h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', ns, c', _, _, _, _, hboard', _, _⟩ := hn
  have hp : p.board ps = some { color := c, kind := .pawn } := by
    rw [hboard, Board.kingsPawnBoard_pawn wk bk ps c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsKnightBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndQueen.not_IsKingAndPawn {p : Position} (h : IsKingAndQueen p) :
    ¬ IsKingAndPawn p := fun hp => hp.not_IsKingAndQueen h

theorem IsKingAndRook.not_IsKingAndPawn {p : Position} (h : IsKingAndRook p) :
    ¬ IsKingAndPawn p := fun hp => hp.not_IsKingAndRook h

theorem IsKingAndBishop.not_IsKingAndQueen {p : Position} (h : IsKingAndBishop p) :
    ¬ IsKingAndQueen p := by
  intro hq
  obtain ⟨wk, bk, bs, c, _, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', qs, c', _, _, _, _, hboard', _, _⟩ := hq
  have hp : p.board bs = some { color := c, kind := .bishop } := by
    rw [hboard, Board.kingsBishopBoard_bishop wk bk bs c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsQueenBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndBishop.not_IsKingAndRook {p : Position} (h : IsKingAndBishop p) :
    ¬ IsKingAndRook p := by
  intro hr
  obtain ⟨wk, bk, bs, c, _, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', rs, c', _, _, _, _, hboard', _, _⟩ := hr
  have hp : p.board bs = some { color := c, kind := .bishop } := by
    rw [hboard, Board.kingsBishopBoard_bishop wk bk bs c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsRookBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndKnight.not_IsKingAndQueen {p : Position} (h : IsKingAndKnight p) :
    ¬ IsKingAndQueen p := by
  intro hq
  obtain ⟨wk, bk, ns, c, _, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', qs, c', _, _, _, _, hboard', _, _⟩ := hq
  have hp : p.board ns = some { color := c, kind := .knight } := by
    rw [hboard, Board.kingsKnightBoard_knight wk bk ns c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsQueenBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndKnight.not_IsKingAndRook {p : Position} (h : IsKingAndKnight p) :
    ¬ IsKingAndRook p := by
  intro hr
  obtain ⟨wk, bk, ns, c, _, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', rs, c', _, _, _, _, hboard', _, _⟩ := hr
  have hp : p.board ns = some { color := c, kind := .knight } := by
    rw [hboard, Board.kingsKnightBoard_knight wk bk ns c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsRookBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndQueen.not_IsKingAndRook {p : Position} (h : IsKingAndQueen p) :
    ¬ IsKingAndRook p := by
  intro hr
  obtain ⟨wk, bk, qs, c, _, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', rs, c', _, _, _, _, hboard', _, _⟩ := hr
  have hp : p.board qs = some { color := c, kind := .queen } := by
    rw [hboard, Board.kingsQueenBoard_queen wk bk qs c h2 h3]
  rw [hboard'] at hp
  unfold Board.kingsRookBoard at hp
  split_ifs at hp <;> simp at hp

theorem IsKingAndRook.not_IsKingAndQueen {p : Position} (h : IsKingAndRook p) :
    ¬ IsKingAndQueen p := fun hq => hq.not_IsKingAndRook h

theorem pawn_rank_of_noBack {b : Board} {s : Square} {c : Color}
    (h : b.noPawnOnBackRank = true)
    (hp : b s = some { color := c, kind := .pawn }) :
    1 ≤ s.rank.val ∧ s.rank.val ≤ 6 := by
  have hcard : (Finset.univ.filter fun t => b.isPawnOnBackRank t).card = 0 :=
    beq_iff_eq.mp h
  have hfalse : b.isPawnOnBackRank s = false := by
    by_contra htrue
    have : b.isPawnOnBackRank s = true := by simpa using htrue
    have hmem : s ∈ Finset.univ.filter fun t => b.isPawnOnBackRank t := by
      simp [this]
    have : 0 < (Finset.univ.filter fun t => b.isPawnOnBackRank t).card :=
      Finset.card_pos.mpr ⟨s, hmem⟩
    omega
  unfold Board.isPawnOnBackRank at hfalse
  rw [hp] at hfalse
  simp only [beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at hfalse
  omega

theorem exists_kpState_white {p : Position} (hv : Valid p)
    {wk bk ps : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsPawnBoard wk bk ps .white)
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    ∃ s : KPState, s.okB = true ∧ s.toPosition = p := by
  refine ⟨⟨p.toMove, wk, bk, ps⟩, ?_, ?_⟩
  · have hrank := pawn_rank_of_noBack hv.1.2.2.1
      (by rw [hboard]; exact Board.kingsPawnBoard_pawn wk bk ps .white h2 h3)
    rw [KPState.okB_iff]
    refine ⟨h1, h2, h3, hna, hrank.1, hrank.2, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have hopp' : (Board.kingsPawnBoard wk bk ps .white).kingIsAttacked .black =
          false := by simpa [ht] using hopp
      simpa [KPState.inCheckB, KPState.kingIsAttacked_black_eq wk bk ps h1 h2 h3]
        using hopp'
    | black =>
      have hopp' : (Board.kingsPawnBoard wk bk ps .white).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      simpa [KPState.inCheckB, KPState.kingIsAttacked_white_eq wk bk ps h1 h2 h3]
        using hopp'
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

theorem exists_kpState_black {p : Position} (hv : Valid p)
    {wk bk ps : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsPawnBoard wk bk ps .black)
    (_hc : p.castling = ∅) (_he : p.enPassant = none) :
    ∃ s : KPState, s.okB = true ∧ s.toPosition = p.rot180 := by
  let s : KPState := ⟨p.toMove.other, bk.rot180, wk.rot180, ps.rot180⟩
  refine ⟨s, ?_, ?_⟩
  · have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
    have h2' : wk.rot180 ≠ ps.rot180 := mt Board.rot180_injective h2
    have h3' : bk.rot180 ≠ ps.rot180 := mt Board.rot180_injective h3
    have hna' : ¬ KingAttacks bk.rot180 wk.rot180 :=
      fun hk => hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
    have hrank0 := pawn_rank_of_noBack hv.1.2.2.1
      (by rw [hboard]; exact Board.kingsPawnBoard_pawn wk bk ps .black h2 h3)
    have hrank : 1 ≤ ps.rot180.rank.val ∧ ps.rot180.rank.val ≤ 6 := by
      have : ps.rot180.rank.val = 7 - ps.rank.val := by
        simp [Square.rot180]
      omega
    rw [KPState.okB_iff]
    refine ⟨h1', h3', h2', hna', hrank.1, hrank.2, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have : s.toMove.other = .white := by simp [s, ht]
      rw [this]
      simpa [s, KPState.inCheckB, KPState.kingAttackedWhite] using hna'
    | black =>
      have hopp' : (Board.kingsPawnBoard wk bk ps .black).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      have hiff := Board.kingsPawnBoard_kingIsAttacked_white wk bk ps .black h1 h2 h3
      have hn : ¬ (KingAttacks bk wk ∨
          (Color.black = .black ∧ PawnAttacks .black ps wk)) := by
        intro h'
        exact Bool.false_ne_true (hopp'.symm.trans (hiff.mpr h'))
      have : s.toMove.other = .black := by simp [s, ht]
      rw [this]
      unfold KPState.inCheckB KPState.kingAttackedBlack
      simp only [Bool.or_eq_false_iff]
      refine ⟨decide_eq_false (by simpa [s] using hna'), ?_⟩
      refine decide_eq_false ?_
      intro hp
      exact hn (Or.inr ⟨rfl,
        (Square.pawnAttacks_rot180 Color.black ps wk).mpr (by simpa [s] using hp)⟩)
  · simp [s, KPState.toPosition, rot180, hboard,
      Board.rot180_kingsPawnBoard_black wk bk ps h1 h2 h3]

theorem exists_kpState {p : Position} (hv : Valid p) (h : IsKingAndPawn p) :
    (∃ s : KPState, s.okB = true ∧ s.toPosition = p) ∨
      (∃ s : KPState, s.okB = true ∧ s.toPosition = p.rot180) := by
  obtain ⟨wk, bk, ps, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  cases c with
  | white => exact Or.inl (exists_kpState_white hv h1 h2 h3 hna hboard hc he)
  | black => exact Or.inr (exists_kpState_black hv h1 h2 h3 hna hboard hc he)

theorem IsKingAndPawn.reachable_rot180 {p : Position} (hp : IsKingAndPawn p)
    {q : Position} (hr : Reachable p q) :
    (IsKingAndPawn q → Reachable p.rot180 q.rot180) ∧
    (IsKingAndQueen q → Reachable p.rot180 q.rot180) ∧
    (IsKingAndRook q → Reachable p.rot180 q.rot180) := by
  refine Reachable.rec (motive := fun q _ =>
      (IsKingAndPawn q → Reachable p.rot180 q.rot180) ∧
      (IsKingAndQueen q → Reachable p.rot180 q.rot180) ∧
      (IsKingAndRook q → Reachable p.rot180 q.rot180)) ?_ ?_ hr
  · exact ⟨fun _ => Reachable.refl,
      fun hq => (hp.not_IsKingAndQueen hq).elim,
      fun hrk => (hp.not_IsKingAndRook hrk).elim⟩
  · intro q m hrq hleg ih
    cases hp.of_reachable hrq with
    | stay hkp =>
      have hstep : Reachable p.rot180 (q.play m).rot180 := by
        have h0 := Reachable.step m.rot180 (ih.1 hkp) (hkp.legalMove_rot180.mp hleg)
        rwa [← hkp.play_rot180 hleg] at h0
      exact ⟨fun _ => hstep, fun _ => hstep, fun _ => hstep⟩
    | queen hq =>
      have hstep : Reachable p.rot180 (q.play m).rot180 := by
        have h0 := Reachable.step m.rot180 (ih.2.1 hq) (hq.legalMove_rot180.mp hleg)
        rwa [← hq.play_rot180 hleg] at h0
      exact ⟨fun _ => hstep, fun _ => hstep, fun _ => hstep⟩
    | rook hrk =>
      have hstep : Reachable p.rot180 (q.play m).rot180 := by
        have h0 := Reachable.step m.rot180 (ih.2.2 hrk) (hrk.legalMove_rot180.mp hleg)
        rwa [← hrk.play_rot180 hleg] at h0
      exact ⟨fun _ => hstep, fun _ => hstep, fun _ => hstep⟩
    | bishop hb =>
      rcases hb.of_play hleg with hb' | htk
      · exact ⟨fun hkp => (hkp.not_IsKingAndBishop hb').elim,
          fun hq => (hb'.not_IsKingAndQueen hq).elim,
          fun hrk => (hb'.not_IsKingAndRook hrk).elim⟩
      · exact ⟨fun hkp => (hkp.not_IsTwoKings htk).elim,
          fun hq => (hq.not_IsTwoKings htk).elim,
          fun hrk => (hrk.not_IsTwoKings htk).elim⟩
    | knight hn =>
      rcases hn.of_play hleg with hn' | htk
      · exact ⟨fun hkp => (hkp.not_IsKingAndKnight hn').elim,
          fun hq => (hn'.not_IsKingAndQueen hq).elim,
          fun hrk => (hn'.not_IsKingAndRook hrk).elim⟩
      · exact ⟨fun hkp => (hkp.not_IsTwoKings htk).elim,
          fun hq => (hq.not_IsTwoKings htk).elim,
          fun hrk => (hrk.not_IsTwoKings htk).elim⟩
    | two htk =>
      have htk' := htk.of_play hleg
      exact ⟨fun hkp => (hkp.not_IsTwoKings htk').elim,
        fun hq => (hq.not_IsTwoKings htk').elim,
        fun hrk => (hrk.not_IsTwoKings htk').elim⟩

theorem IsKingAndPawn.checkmateReachable_rot180 {p : Position}
    (h : IsKingAndPawn p) :
    CheckmateReachable p ↔ CheckmateReachable p.rot180 := by
  constructor
  · intro ⟨q, hr, hm⟩
    rcases KingPawnPlay.not_InCheckmate (h.of_reachable hr) hm with hkp | hq | hrk
    · exact ⟨q.rot180, (h.reachable_rot180 hr).1 hkp, hkp.inCheckmate_rot180 hm⟩
    · exact ⟨q.rot180, (h.reachable_rot180 hr).2.1 hq, hq.inCheckmate_rot180 hm⟩
    · exact ⟨q.rot180, (h.reachable_rot180 hr).2.2 hrk, hrk.inCheckmate_rot180 hm⟩
  · intro ⟨q, hr, hm⟩
    have h' := h.rot180
    rcases KingPawnPlay.not_InCheckmate (h'.of_reachable hr) hm with hkp | hq | hrk
    · have hr' := (h'.reachable_rot180 hr).1 hkp
      have hm' := hkp.inCheckmate_rot180 hm
      rw [rot180_involutive h.castling_eq h.enPassant_eq] at hr'
      exact ⟨q.rot180, hr', hm'⟩
    · have hr' := (h'.reachable_rot180 hr).2.1 hq
      have hm' := hq.inCheckmate_rot180 hm
      rw [rot180_involutive h.castling_eq h.enPassant_eq] at hr'
      exact ⟨q.rot180, hr', hm'⟩
    · have hr' := (h'.reachable_rot180 hr).2.2 hrk
      have hm' := hrk.inCheckmate_rot180 hm
      rw [rot180_involutive h.castling_eq h.enPassant_eq] at hr'
      exact ⟨q.rot180, hr', hm'⟩

theorem IsKingAndPawn.checkmateReachable_of_not_dead {p : Position}
    (_hv : Valid p) (h : IsKingAndPawn p) {s : KPState}
    (hok : s.okB = true) (hnd : s.deadB = false)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p := by
  have hcr := KPState.checkmateReachable_of_okB_of_not_dead hok hnd
  rcases hpos with hpos | hpos
  · rwa [hpos] at hcr
  · rw [h.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem IsKingAndPawn.checkmateReachable_iff_deadB {p : Position}
    (hv : Valid p) (h : IsKingAndPawn p) {s : KPState}
    (hok : s.okB = true)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p ↔ s.deadB = false := by
  constructor
  · intro hcr
    have hiff := KPState.checkmateReachable_iff_not_dead hok
    rcases hpos with hpos | hpos
    · rw [← hpos] at hcr
      exact hiff.mp hcr
    · rw [h.checkmateReachable_rot180] at hcr
      rw [← hpos] at hcr
      exact hiff.mp hcr
  · intro hnd
    exact h.checkmateReachable_of_not_dead hv hok hnd hpos

theorem kp_ofPositionWhite?_eq_some {p : Position} {s : KPState}
    (h : KPState.ofPositionWhite? p = some s) :
    s.okB = true ∧ s.toPosition = p := by
  unfold KPState.ofPositionWhite? at h
  split at h
  · rename_i wk bk ps _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      have hboard : p.board = Board.kingsPawnBoard wk bk ps .white := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KPState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      rfl
  · cases h

theorem kp_ofPositionBlack?_eq_some {p : Position} {s : KPState}
    (h : KPState.ofPositionBlack? p = some s) :
    s.okB = true ∧ s.toPosition = p.rot180 := by
  unfold KPState.ofPositionBlack? at h
  split at h
  · rename_i wk bk ps _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      obtain ⟨h1s, h2s, h3s, _, _, _, _⟩ := (KPState.okB_iff _).mp hok
      have hwk_bk : wk ≠ bk := fun heq => h1s (by simp [heq])
      have hwk_ps : wk ≠ ps := fun heq => h3s (by simp [heq])
      have hbk_ps : bk ≠ ps := fun heq => h2s (by simp [heq])
      have hboard : p.board = Board.kingsPawnBoard wk bk ps .black := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KPState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      simp [KPState.toPosition, rot180,
        Board.rot180_kingsPawnBoard_black wk bk ps hwk_bk hwk_ps hbk_ps]
  · cases h

theorem kp_ofPositionWhite?_of_eq {p : Position} {s : KPState}
    (hok : s.okB = true) (hpos : s.toPosition = p) :
    KPState.ofPositionWhite? p = some s := by
  have hboard : p.board = Board.kingsPawnBoard s.wk s.bk s.ps .white := by
    rw [← hpos]; rfl
  have htm : p.toMove = s.toMove := by
    have : s.toPosition.toMove = p.toMove := by rw [hpos]
    simpa [KPState.toPosition] using this.symm
  have hcst : p.castling = ∅ := by
    have : s.toPosition.castling = p.castling := by rw [hpos]
    simpa [KPState.toPosition] using this.symm
  have hep : p.enPassant = none := by
    have : s.toPosition.enPassant = p.enPassant := by rw [hpos]
    simpa [KPState.toPosition] using this.symm
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (KPState.okB_iff s).mp hok
  have hwk : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.wk := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsPawnBoard_white])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.bk := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsPawnBoard_black s.wk s.bk s.ps .white h1])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hps : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .pawn }) = some s.ps := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsPawnBoard_pawn s.wk s.bk s.ps .white h2 h3])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_pawn (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KPState.allSquares.all fun q =>
      p.board q == Board.kingsPawnBoard s.wk s.bk s.ps .white q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove, s.wk, s.bk, s.ps⟩ : KPState) = s := by
    cases s
    simp [htm]
  unfold KPState.ofPositionWhite?
  rw [hwk, hbk, hps]
  simp [hs, hok, hall, hcst, hep]

theorem kp_ofPositionBlack?_of_eq {p : Position} {s : KPState}
    (hok : s.okB = true) (hpos : s.toPosition = p.rot180)
    (hcst : p.castling = ∅) (hep : p.enPassant = none) :
    KPState.ofPositionBlack? p = some s := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (KPState.okB_iff s).mp hok
  have hboardR : p.rot180.board = Board.kingsPawnBoard s.wk s.bk s.ps .white := by
    rw [← hpos]; rfl
  have hboard : p.board =
      Board.kingsPawnBoard s.bk.rot180 s.wk.rot180 s.ps.rot180 .black := by
    have hrot := congrArg Board.rot180 hboardR
    rw [rot180_board, Board.board_rot180_involutive,
      Board.rot180_kingsPawnBoard_white s.wk s.bk s.ps h1 h2 h3] at hrot
    exact hrot
  have htm : p.toMove.other = s.toMove := by
    have : s.toPosition.toMove = p.rot180.toMove := by rw [hpos]
    simpa [KPState.toPosition, rot180_toMove] using this.symm
  have hneWB : s.bk.rot180 ≠ s.wk.rot180 := Ne.symm (mt Board.rot180_injective h1)
  have hneWR : s.wk.rot180 ≠ s.ps.rot180 := mt Board.rot180_injective h2
  have hneBR : s.bk.rot180 ≠ s.ps.rot180 := mt Board.rot180_injective h3
  have hwk : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.bk.rot180 := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsPawnBoard_white])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.wk.rot180 := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsPawnBoard_black s.bk.rot180 s.wk.rot180 s.ps.rot180
          .black hneWB])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hps : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .pawn }) = some s.ps.rot180 := by
    refine find?_eq_some_of_unique (KPState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsPawnBoard_pawn s.bk.rot180 s.wk.rot180 s.ps.rot180
          .black hneBR hneWR])
    · intro q _ hq
      exact Board.kingsPawnBoard_eq_pawn (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KPState.allSquares.all fun q =>
      p.board q == Board.kingsPawnBoard s.bk.rot180 s.wk.rot180 s.ps.rot180
        .black q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove.other, s.wk, s.bk, s.ps⟩ : KPState) = s := by
    cases s
    simp [htm]
  unfold KPState.ofPositionBlack?
  rw [hwk, hbk, hps]
  simp [Square.rot180_involutive, hs, hok, hall, hcst, hep]

theorem kp_ofPositionWhite?_eq_none_of_black {p : Position} {wk bk ps : Square}
    (hboard : p.board = Board.kingsPawnBoard wk bk ps .black) :
    KPState.ofPositionWhite? p = none := by
  have hps : KPState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .pawn }) = none := by
    refine List.find?_eq_none.mpr ?_
    intro q _
    cases hb : (p.board q == some { color := .white, kind := .pawn })
    · exact Bool.false_ne_true
    · have heq : p.board q = some { color := .white, kind := .pawn } :=
        beq_iff_eq.mp hb
      rw [hboard] at heq
      unfold Board.kingsPawnBoard at heq
      split_ifs at heq <;> cases heq
  unfold KPState.ofPositionWhite?
  rw [hps]
  split
  · rename_i _ _ _ heq
    cases heq
  · rfl

theorem kp_ofPosition?_eq_some {p : Position} {s : KPState}
    (h : KPState.ofPosition? p = some s) :
    s.okB = true ∧ (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  unfold KPState.ofPosition? at h
  split at h
  · rename_i s' hW
    injection h with hs
    subst hs
    have ⟨hok, hpos⟩ := kp_ofPositionWhite?_eq_some hW
    exact ⟨hok, Or.inl hpos⟩
  · have ⟨hok, hpos⟩ := kp_ofPositionBlack?_eq_some h
    exact ⟨hok, Or.inr hpos⟩

theorem kp_ofPosition?_complete {p : Position} (hv : Valid p) (h : IsKingAndPawn p) :
    ∃ s, KPState.ofPosition? p = some s ∧ s.okB = true ∧
      (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  rcases exists_kpState hv h with ⟨s, hok, hpos⟩ | ⟨s, hok, hpos⟩
  · refine ⟨s, ?_, hok, Or.inl hpos⟩
    unfold KPState.ofPosition?
    rw [kp_ofPositionWhite?_of_eq hok hpos]
  · refine ⟨s, ?_, hok, Or.inr hpos⟩
    obtain ⟨h1, h2, h3, _, _, _, _⟩ := (KPState.okB_iff s).mp hok
    have hboardR : p.rot180.board = Board.kingsPawnBoard s.wk s.bk s.ps .white := by
      rw [← hpos]; rfl
    have hboard : p.board =
        Board.kingsPawnBoard s.bk.rot180 s.wk.rot180 s.ps.rot180 .black := by
      have hrot := congrArg Board.rot180 hboardR
      rw [rot180_board, Board.board_rot180_involutive,
        Board.rot180_kingsPawnBoard_white s.wk s.bk s.ps h1 h2 h3] at hrot
      exact hrot
    unfold KPState.ofPosition?
    rw [kp_ofPositionWhite?_eq_none_of_black hboard,
      kp_ofPositionBlack?_of_eq hok hpos h.castling_eq h.enPassant_eq]

/-- The engineered mating line of a king-and-pawn versus king position;
`[]` when the position is dead or not of this material. Black-pawn
positions are rotated into the white-pawn frame, and the resulting moves
are rotated back. -/
def kingPawnMatingLine (p : Position) : List Move :=
  match KPState.ofPositionWhite? p with
  | some s => s.matingLine
  | none =>
    match KPState.ofPositionBlack? p with
    | some s => s.matingLine.map Move.rot180
    | none => []

/-- Whether a king-and-pawn versus king position is dead for helpmate
(`true` when the board is not of this material). -/
def kingPawnDead (p : Position) : Bool :=
  match KPState.ofPosition? p with
  | some s => s.deadB
  | none => true

/-- In a valid king-and-pawn versus king position, checkmate is reachable
exactly when the corresponding three-piece state is not dead. -/
theorem IsKingAndPawn.checkmateReachable_iff {p : Position}
    (hv : Valid p) (h : IsKingAndPawn p) :
    CheckmateReachable p ↔ kingPawnDead p = false := by
  obtain ⟨s, hs, hok, hpos⟩ := kp_ofPosition?_complete hv h
  have hdeq : kingPawnDead p = s.deadB := by simp [kingPawnDead, hs]
  rw [hdeq]
  exact h.checkmateReachable_iff_deadB hv hok hpos

/-- Decides whether checkmate is reachable from a valid king-and-pawn
versus king position: exactly when the corresponding three-piece state
is not dead. -/
def kingPawnCheckmateReachable (p : Position) (hv : Valid p)
    (h : IsKingAndPawn p) : Decidable (CheckmateReachable p) :=
  decidable_of_iff (kingPawnDead p = false) (h.checkmateReachable_iff hv).symm

/-! ### Examples -/

/-- White king on `e1`, black king on `e8`, white pawn on `e2`, White to
move. -/
def kingPawnStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e2 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingPawnStart_isValid : isValid kingPawnStart = true := by
  native_decide

theorem kingPawnStart_valid : Valid kingPawnStart :=
  (isValid_eq_true_iff _).mp kingPawnStart_isValid

theorem kingPawnStart_isKingAndPawn : IsKingAndPawn kingPawnStart := by
  refine ⟨Square.e1, Square.e8, Square.e2, Color.white,
    by native_decide, by native_decide, by native_decide, by native_decide, ?_,
    rfl, rfl⟩
  funext s
  simp [kingPawnStart, Board.kingsPawnBoard]

/-- White king on `g6`, black king on `h8`, white pawn on `f7`, White to
move. Promotion to a queen on `f8` is the known eighth-rank mate. -/
def kingPawnPromo : Position where
  board := fun s =>
    if s = Square.g6 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.f7 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingPawnPromo_isValid : isValid kingPawnPromo = true := by
  native_decide

theorem kingPawnPromo_valid : Valid kingPawnPromo :=
  (isValid_eq_true_iff _).mp kingPawnPromo_isValid

theorem kingPawnPromo_isKingAndPawn : IsKingAndPawn kingPawnPromo := by
  refine ⟨Square.g6, Square.h8, Square.f7, Color.white,
    by native_decide, by native_decide, by native_decide, by native_decide, ?_,
    rfl, rfl⟩
  funext s
  simp [kingPawnPromo, Board.kingsPawnBoard]

/-- Forced capture of an unprotected pawn: Black to move, not in check,
and the only legal move takes the pawn, leaving two kings. -/
def pawnForcedCapture : Position where
  board := fun s =>
    if s = Square.c8 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem pawnForcedCapture_isValid : isValid pawnForcedCapture = true := by
  native_decide

theorem pawnForcedCapture_valid : Valid pawnForcedCapture :=
  (isValid_eq_true_iff _).mp pawnForcedCapture_isValid

theorem pawnForcedCapture_isKingAndPawn : IsKingAndPawn pawnForcedCapture := by
  refine ⟨Square.c8, Square.a8, Square.a7, Color.white,
    by native_decide, by native_decide, by native_decide, by native_decide, ?_,
    rfl, rfl⟩
  funext s
  simp [pawnForcedCapture, Board.kingsPawnBoard]

theorem kingPawnStart_CheckmateReachable : CheckmateReachable kingPawnStart :=
  (kingPawnStart_isKingAndPawn.checkmateReachable_iff kingPawnStart_valid).mpr
    (by native_decide)

theorem kingPawnStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingPawnStart)
      (kingPawnCheckmateReachable kingPawnStart kingPawnStart_valid
        kingPawnStart_isKingAndPawn) = true := by
  native_decide

theorem kingPawnStart_not_deadPosition : ¬ DeadPosition kingPawnStart :=
  not_deadPosition_of_checkmateReachable kingPawnStart_CheckmateReachable

theorem kingPawnPromo_CheckmateReachable : CheckmateReachable kingPawnPromo :=
  (kingPawnPromo_isKingAndPawn.checkmateReachable_iff kingPawnPromo_valid).mpr
    (by native_decide)

theorem kingPawnPromo_matingLine_legal :
    pathLegal kingPawnPromo (kingPawnMatingLine kingPawnPromo) = true := by
  native_decide

theorem kingPawnPromo_matingLine_inCheckmate :
    (playSeq kingPawnPromo (kingPawnMatingLine kingPawnPromo)).inCheckmate = true := by
  native_decide

theorem kingPawnPromo_CheckmateReachable' : CheckmateReachable kingPawnPromo :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingPawnPromo_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingPawnPromo_matingLine_inCheckmate)

theorem pawnForcedCapture_deadB : ∃ s : KPState, s.okB = true ∧
    s.toPosition = pawnForcedCapture ∧ s.deadB = true := by
  refine ⟨⟨.black, Square.c8, Square.a8, Square.a7⟩, by native_decide, ?_,
    by native_decide⟩
  have hboard : Board.kingsPawnBoard Square.c8 Square.a8 Square.a7 .white =
      pawnForcedCapture.board := by
    funext q
    simp [pawnForcedCapture, Board.kingsPawnBoard]
  simp [KPState.toPosition, pawnForcedCapture, hboard, CastlingRights.empty]

theorem pawnForcedCapture_not_CheckmateReachable :
    ¬ CheckmateReachable pawnForcedCapture := by
  obtain ⟨s, hok, hpos, hd⟩ := pawnForcedCapture_deadB
  intro hcr
  have := (pawnForcedCapture_isKingAndPawn.checkmateReachable_iff_deadB
    pawnForcedCapture_valid hok (Or.inl hpos)).mp hcr
  exact Bool.false_ne_true (this.symm.trans hd)

theorem pawnForcedCapture_decide_CheckmateReachable :
    @decide (CheckmateReachable pawnForcedCapture)
      (kingPawnCheckmateReachable pawnForcedCapture pawnForcedCapture_valid
        pawnForcedCapture_isKingAndPawn) = false := by
  native_decide

theorem pawnStalemate_isKingAndPawn : IsKingAndPawn stalemate := by
  refine ⟨Square.a6, Square.a8, Square.a7, Color.white,
    by native_decide, by native_decide, by native_decide, by native_decide, ?_,
    rfl, rfl⟩
  funext s
  simp [stalemate, Board.kingsPawnBoard]

theorem pawnStalemate_not_CheckmateReachable :
    ¬ CheckmateReachable stalemate :=
  not_CheckmateReachable_of_InStalemate
    ((inStalemate_eq_true_iff _).mp stalemate_inStalemate)

theorem pawnStalemate_decide_CheckmateReachable :
    @decide (CheckmateReachable stalemate)
      (kingPawnCheckmateReachable stalemate
        ((isValid_eq_true_iff stalemate).mp stalemate_isValid)
        pawnStalemate_isKingAndPawn) = false := by
  native_decide

theorem pawnStalemate_deadPosition : DeadPosition stalemate :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr
    pawnStalemate_not_CheckmateReachable

end Position

end Chess







