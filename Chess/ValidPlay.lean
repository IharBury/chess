import Chess.LoneKingMaterial

/-!
# Playing a legal move preserves validity

A legal move from a valid position yields a valid position: the new
placement still has one king per side, at most sixteen pieces per side,
and no pawns on the back ranks; the mover's king is not under attack
(that is part of legality); remaining castling rights still have king
and rook at home; and an en passant target, if recorded, is consistent.
-/

namespace Chess

namespace Piece

theorem eq_of_color_kind (p : Piece) {c : Color} {k : PieceKind}
    (hc : p.color = c) (hk : p.kind = k) :
    p = { color := c, kind := k } := by
  cases p
  simp_all

theorem eq_king {p : Piece} {c : Color} (h : p.color = c ∧ p.kind = .king) :
    p = { color := c, kind := .king } :=
  eq_of_color_kind p h.1 h.2

end Piece

namespace Board

theorem relocate_dst (b : Board) (src dst : Square) (p : Piece) :
    b.relocate src dst p dst = some p := by
  simp [relocate]

theorem relocate_src (b : Board) (src dst : Square) (p : Piece)
    (h : src ≠ dst) :
    b.relocate src dst p src = none := by
  simp [relocate, h]

theorem relocate_other (b : Board) (src dst x : Square) (p : Piece)
    (hx : x ≠ dst) (hs : x ≠ src) :
    b.relocate src dst p x = b x := by
  simp [relocate, hx, hs]

theorem clear_self (b : Board) (s : Square) : b.clear s s = none := by
  simp [clear]

theorem clear_other (b : Board) (s x : Square) (h : x ≠ s) :
    b.clear s x = b x := by
  simp [clear, h]

theorem occupiedBy_relocate (b : Board) (src dst : Square) (p : Piece)
    (c : Color) :
    (b.relocate src dst p).occupiedBy c =
      if p.color = c then insert dst (b.occupiedBy c \ {src})
      else b.occupiedBy c \ {src, dst} := by
  ext x
  by_cases hp : p.color = c
  · rw [if_pos hp]
    simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_sdiff,
      Finset.mem_singleton]
    by_cases hx : x = dst
    · subst hx
      simp [relocate, hp]
    · by_cases hs : x = src
      · subst hs
        simp [relocate, hx]
      · simp [relocate, hx, hs]
  · rw [if_neg hp]
    simp only [mem_occupiedBy, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hx : x = dst
    · subst hx
      simp [relocate, hp]
    · by_cases hs : x = src
      · subst hs
        simp [relocate, hx]
      · simp [relocate, hx, hs]

theorem occupiedBy_clear (b : Board) (s : Square) (c : Color) :
    (b.clear s).occupiedBy c = b.occupiedBy c \ {s} := by
  ext x
  simp only [mem_occupiedBy, Finset.mem_sdiff, Finset.mem_singleton, clear]
  by_cases hx : x = s
  · subst hx
    simp
  · simp [hx]

theorem occupiedBy_relocate_card_le (b : Board) (src dst : Square) (p : Piece)
    (c : Color) (hsrc : (b src).map (·.color) = some p.color) :
    ((b.relocate src dst p).occupiedBy c).card ≤ (b.occupiedBy c).card := by
  have hmem : src ∈ b.occupiedBy p.color := by
    simpa [mem_occupiedBy] using hsrc
  rw [occupiedBy_relocate]
  split_ifs with hp
  · have hmemc : src ∈ b.occupiedBy c := by
      rwa [← hp]
    have hle := Finset.card_insert_le dst (b.occupiedBy c \ {src})
    have hsub : ({src} : Finset Square) ⊆ b.occupiedBy c := by
      simpa using hmemc
    have herase :
        (b.occupiedBy c \ {src}).card = (b.occupiedBy c).card - 1 := by
      rw [Finset.card_sdiff_of_subset hsub]
      simp
    have hpos : 1 ≤ (b.occupiedBy c).card :=
      Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨src, hmemc⟩)
    omega
  · exact Finset.card_le_card Finset.sdiff_subset

theorem occupiedBy_clear_card_le (b : Board) (s : Square) (c : Color) :
    ((b.clear s).occupiedBy c).card ≤ (b.occupiedBy c).card := by
  rw [occupiedBy_clear]
  exact Finset.card_le_card Finset.sdiff_subset

theorem kingSquares_relocate (b : Board) (src dst : Square) (p : Piece)
    (c : Color) :
    (b.relocate src dst p).kingSquares c =
      if p.color = c ∧ p.kind = .king then insert dst (b.kingSquares c \ {src})
      else b.kingSquares c \ {src, dst} := by
  ext x
  by_cases hk : p.color = c ∧ p.kind = .king
  · rw [if_pos hk]
    have hp : p = { color := c, kind := .king } := Piece.eq_king hk
    by_cases hx : x = dst
    · subst hx
      constructor
      · intro
        exact Finset.mem_insert_self _ _
      · intro
        exact (mem_kingSquares _ _ _).mpr (by rw [relocate_dst, hp])
    · by_cases hs : x = src
      · subst hs
        constructor
        · intro hmem
          have hget := (mem_kingSquares _ _ _).mp hmem
          rw [relocate_src _ _ _ _ hx] at hget
          cases hget
        · intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact (hx h).elim
          · exact ((Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self _)).elim
      · constructor
        · intro hmem
          have hget := (mem_kingSquares _ _ _).mp hmem
          rw [relocate_other _ _ _ _ _ hx hs] at hget
          refine Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ?_))
          exact ⟨(mem_kingSquares _ _ _).mpr hget, Finset.notMem_singleton.mpr hs⟩
        · intro hmem
          have hget : b x = some { color := c, kind := .king } := by
            rcases Finset.mem_insert.mp hmem with h | h
            · exact (hx h).elim
            · exact (mem_kingSquares _ _ _).mp (Finset.mem_sdiff.mp h).1
          apply (mem_kingSquares _ _ _).mpr
          rwa [relocate_other _ _ _ _ _ hx hs]
  · rw [if_neg hk]
    by_cases hx : x = dst
    · subst hx
      constructor
      · intro hmem
        have hget := (mem_kingSquares _ _ _).mp hmem
        rw [relocate_dst] at hget
        exact (hk ⟨congrArg Piece.color (Option.some.inj hget),
          congrArg Piece.kind (Option.some.inj hget)⟩).elim
      · intro hmem
        exact ((Finset.mem_sdiff.mp hmem).2 (by simp)).elim
    · by_cases hs : x = src
      · subst hs
        constructor
        · intro hmem
          have hget := (mem_kingSquares _ _ _).mp hmem
          rw [relocate_src _ _ _ _ hx] at hget
          cases hget
        · intro hmem
          exact ((Finset.mem_sdiff.mp hmem).2 (by simp)).elim
      · constructor
        · intro hmem
          have hget := (mem_kingSquares _ _ _).mp hmem
          rw [relocate_other _ _ _ _ _ hx hs] at hget
          refine Finset.mem_sdiff.mpr ⟨(mem_kingSquares _ _ _).mpr hget, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, hx, hs,
            or_self, not_false_eq_true]
        · intro hmem
          have hget := (mem_kingSquares _ _ _).mp (Finset.mem_sdiff.mp hmem).1
          apply (mem_kingSquares _ _ _).mpr
          rwa [relocate_other _ _ _ _ _ hx hs]

theorem kingSquares_clear (b : Board) (s : Square) (c : Color) :
    (b.clear s).kingSquares c = b.kingSquares c \ {s} := by
  ext x
  simp only [mem_kingSquares, Finset.mem_sdiff, Finset.mem_singleton, clear]
  by_cases hx : x = s
  · subst hx
    simp
  · simp [hx]

theorem kingSquares_relocate_card (b : Board) (src dst : Square) (p : Piece)
    (c : Color)
    (hcard : (b.kingSquares c).card = 1)
    (hdst : dst ∉ b.kingSquares c)
    (hsame : src ∈ b.kingSquares c ↔ (p.color = c ∧ p.kind = .king)) :
    ((b.relocate src dst p).kingSquares c).card = 1 := by
  rw [kingSquares_relocate]
  by_cases hpk : p.color = c ∧ p.kind = .king
  · rw [if_pos hpk]
    have hksrc : src ∈ b.kingSquares c := hsame.mpr hpk
    obtain ⟨k, hk1⟩ := Finset.card_eq_one.mp hcard
    have hsk : src = k := by
      have : src ∈ ({k} : Finset Square) := by simpa [hk1] using hksrc
      simpa using this
    subst hsk
    rw [hk1]
    have hdstn : dst ∉ ({src} : Finset Square) \ {src} := by simp
    rw [Finset.card_insert_of_notMem hdstn]
    simp only [Finset.sdiff_self, Finset.card_empty, Nat.zero_add]
  · rw [if_neg hpk]
    have hnotsrc : src ∉ b.kingSquares c := fun h => hpk (hsame.mp h)
    have heq : b.kingSquares c \ {src, dst} = b.kingSquares c := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        exact h.1
      · intro hx
        refine ⟨hx, ?_⟩
        intro hxd
        rcases hxd with h | h
        · exact hnotsrc (h ▸ hx)
        · exact hdst (h ▸ hx)
    simpa [heq] using hcard

theorem kingSquares_clear_card (b : Board) (s : Square) (c : Color)
    (hcard : (b.kingSquares c).card = 1) (hs : s ∉ b.kingSquares c) :
    ((b.clear s).kingSquares c).card = 1 := by
  have heq : b.kingSquares c \ {s} = b.kingSquares c :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (by simpa)
  simpa [kingSquares_clear, heq] using hcard

theorem noPawnOnBackRank_iff (b : Board) :
    b.noPawnOnBackRank = true ↔ ∀ s : Square, b.isPawnOnBackRank s = false := by
  simp [noPawnOnBackRank, beq_iff_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

theorem noPawnOnBackRank_relocate (b : Board) (src dst : Square) (p : Piece)
    (hb : b.noPawnOnBackRank = true)
    (hp : p.kind = .pawn → dst.rank.val ≠ 0 ∧ dst.rank.val ≠ 7) :
    (b.relocate src dst p).noPawnOnBackRank = true := by
  rw [noPawnOnBackRank_iff] at hb ⊢
  intro s
  by_cases hs : s = dst
  · subst hs
    unfold isPawnOnBackRank relocate
    cases hk : p.kind with
    | pawn =>
      have hr := hp hk
      simp [hk, hr.1, hr.2]
    | knight | bishop | rook | queen | king =>
      simp [hk]
  · by_cases hsrc : s = src
    · subst hsrc
      unfold isPawnOnBackRank relocate
      simp [hs]
    · have heq := relocate_other b src dst s p hs hsrc
      unfold isPawnOnBackRank
      rw [heq]
      exact hb s

theorem noPawnOnBackRank_clear (b : Board) (s : Square)
    (hb : b.noPawnOnBackRank = true) :
    (b.clear s).noPawnOnBackRank = true := by
  rw [noPawnOnBackRank_iff] at hb ⊢
  intro x
  by_cases hx : x = s
  · subst hx
    unfold isPawnOnBackRank clear
    simp
  · have heq := clear_other b s x hx
    unfold isPawnOnBackRank
    rw [heq]
    exact hb x

end Board

namespace CastlingRight

theorem rookSquare_ne_kingSquare : ∀ r : CastlingRight,
    r.rookSquare ≠ r.kingSquare := by
  decide

theorem rookDest_ne_kingSquare : ∀ r : CastlingRight,
    r.rookDest ≠ r.kingSquare := by
  decide

theorem rookSquare_ne_kingDest : ∀ r : CastlingRight,
    r.rookSquare ≠ r.kingDest := by
  decide

theorem rookDest_ne_kingDest : ∀ r : CastlingRight,
    r.rookDest ≠ r.kingDest := by
  decide

theorem rookSquare_ne_rookDest : ∀ r : CastlingRight,
    r.rookSquare ≠ r.rookDest := by
  decide

theorem rookDest_mem_clearSquares : ∀ r : CastlingRight,
    r.rookDest ∈ r.clearSquares := by
  decide

end CastlingRight

namespace Position

/-- Piece that `boardAfter` places on the destination square. -/
def placedOf (piece : Piece) (m : Move) : Piece :=
  match m.promotion with
  | some k => { color := piece.color, kind := k }
  | none => piece

theorem placedOf_color (piece : Piece) (m : Move) :
    (placedOf piece m).color = piece.color := by
  unfold placedOf
  cases m.promotion <;> rfl

theorem destOk_not_king {p : Position} {m : Move} (h : p.destOk m = true)
    {c : Color} : p.board m.dst ≠ some { color := c, kind := .king } := by
  unfold destOk at h
  cases hd : p.board m.dst with
  | none => simp
  | some q =>
    simp [hd, Bool.and_eq_true] at h
    intro heq
    have hk : q.kind = .king := congrArg Piece.kind (Option.some.inj heq)
    simp [hk] at h

theorem destOk_not_mem_kingSquares {p : Position} {m : Move} {c : Color}
    (h : p.destOk m = true) : m.dst ∉ p.board.kingSquares c := by
  intro hmem
  exact destOk_not_king h ((Board.mem_kingSquares _ _ _).mp hmem)

theorem src_ne_dst_of_LegalMove {p : Position} {m : Move} (hm : LegalMove p m) :
    m.src ≠ m.dst := by
  obtain ⟨piece, hsrc, hcol, hdest, _, _⟩ := legalMove_spec hm
  intro heq
  have hsrcd : p.board m.dst = some piece := by rw [← heq, hsrc]
  unfold destOk at hdest
  rw [hsrcd] at hdest
  simp [hcol] at hdest

theorem placedOf_kind_king_iff {p : Position} {m : Move} {piece : Piece}
    (hm : LegalMove p m) (hsrc : p.board m.src = some piece) :
    (placedOf piece m).kind = .king ↔ piece.kind = .king := by
  cases hpr : m.promotion with
  | none => simp [placedOf, hpr]
  | some k =>
    have hcan := legalMove_promotion_canPromoteTo hm hpr
    have hk : k ≠ .king := by
      intro h
      subst h
      simp at hcan
    have hnp : piece.kind = .pawn := by
      by_contra hne
      have := legalMove_promotion_none hm hsrc hne
      rw [hpr] at this
      cases this
    simp only [placedOf, hpr]
    constructor
    · intro h
      exact (hk h).elim
    · intro h
      rw [hnp] at h
      cases h

theorem pawn_dest_not_back_rank {c : Color} {src dst : Square}
    (hs : 1 ≤ src.rank.val ∧ src.rank.val ≤ 6)
    (hgeo : Square.deltaRank src dst = pawnPushDelta c ∨
      Square.deltaRank src dst = 2 * pawnPushDelta c ∨
      PawnAttacks c src dst) :
    dst.rank = pawnPromotionRank c ∨ (dst.rank.val ≠ 0 ∧ dst.rank.val ≠ 7) := by
  revert c src dst
  native_decide

theorem pawnMoveOk_geo {p : Position} {m : Move} {c : Color}
    (hsrc : p.board m.src = some { color := c, kind := .pawn })
    (hpok : p.pawnMoveOk m = true) :
    Square.deltaRank m.src m.dst = pawnPushDelta c ∨
      Square.deltaRank m.src m.dst = 2 * pawnPushDelta c ∨
      PawnAttacks c m.src m.dst := by
  by_cases hpa : PawnAttacks c m.src m.dst
  · exact Or.inr (Or.inr hpa)
  · have hdec : decide (PawnAttacks c m.src m.dst) = false := decide_eq_false hpa
    unfold pawnMoveOk at hpok
    rw [hsrc] at hpok
    dsimp only at hpok
    rw [hdec] at hpok
    simp only [Bool.false_and, Bool.or_false, Bool.and_eq_true,
      Bool.or_eq_true] at hpok
    rcases hpok.1 with hs | hd
    · simp only [decide_eq_true_eq] at hs
      exact Or.inl hs.1.2
    · simp only [decide_eq_true_eq] at hd
      exact Or.inr (Or.inl hd.1.1.2)

theorem pawnMoveOk_attacks_of_ne_file {p : Position} {m : Move} {c : Color}
    (hsrc : p.board m.src = some { color := c, kind := .pawn })
    (hpok : p.pawnMoveOk m = true)
    (hfile : m.src.file ≠ m.dst.file) :
    PawnAttacks c m.src m.dst := by
  by_cases hpa : PawnAttacks c m.src m.dst
  · exact hpa
  · have hdec : decide (PawnAttacks c m.src m.dst) = false := decide_eq_false hpa
    unfold pawnMoveOk at hpok
    rw [hsrc] at hpok
    dsimp only at hpok
    rw [hdec] at hpok
    simp only [Bool.false_and, Bool.or_false, Bool.and_eq_true,
      Bool.or_eq_true] at hpok
    rcases hpok.1 with hs | hd
    · simp only [beq_iff_eq] at hs
      exact (hfile hs.1.1.symm).elim
    · simp only [beq_iff_eq] at hd
      exact (hfile hd.1.1.1.2.symm).elim

theorem pawnMoveOk_of_LegalMove {p : Position} {m : Move} {piece : Piece}
    (hm : LegalMove p m) (hsrc : p.board m.src = some piece)
    (hpawn : piece.kind = .pawn) : p.pawnMoveOk m = true := by
  obtain ⟨piece', hsrc', _, _, _, hkind⟩ := legalMove_spec hm
  have := hsrc.symm.trans hsrc'
  rw [Option.some.injEq] at this
  subst this
  rcases hkind with ⟨_, hok⟩ | ⟨hk, _, _⟩ | ⟨hne, _, _, _⟩
  · exact hok
  · have h : PieceKind.pawn = .king := hpawn.symm.trans hk
    nomatch h
  · exact (hne hpawn).elim

theorem placedOf_pawn_dest_not_back {p : Position} {m : Move} {piece : Piece}
    (hv : p.board.noPawnOnBackRank = true) (hm : LegalMove p m)
    (hsrc : p.board m.src = some piece) (hpawn : piece.kind = .pawn)
    (hplaced : (placedOf piece m).kind = .pawn) :
    m.dst.rank.val ≠ 0 ∧ m.dst.rank.val ≠ 7 := by
  have hp : piece = { color := piece.color, kind := .pawn } :=
    Piece.eq_of_color_kind piece rfl hpawn
  have hpok := pawnMoveOk_of_LegalMove hm hsrc hpawn
  have hpr : m.promotion = none := by
    cases hpr : m.promotion with
    | none => rfl
    | some k =>
      simp [placedOf, hpr] at hplaced
      have hcases := pawnMoveOk_promotion_of (p := p) (m := m) (c := piece.color)
        (by rw [hsrc, hp]) hpok
      rcases hcases with ⟨_, ⟨k', hk', hcan⟩⟩ | ⟨_, hnone⟩
      · rw [hpr] at hk'
        cases hk'
        simp [hplaced] at hcan
      · rw [hpr] at hnone
        cases hnone
  have hcases := pawnMoveOk_promotion_of (p := p) (m := m) (c := piece.color)
    (by rw [hsrc, hp]) hpok
  rcases hcases with ⟨_, ⟨k, hk, _⟩⟩ | ⟨hne, _⟩
  · rw [hpr] at hk
    cases hk
  · have hr := pawn_rank_of_noBack hv (by rw [hsrc, hp])
    have hgeo := pawnMoveOk_geo (by rw [hsrc, hp]) hpok
    have hdest := pawn_dest_not_back_rank hr hgeo
    rcases hdest with hprom | hok
    · exact (hne hprom).elim
    · exact hok

theorem kingSquares_same_of_relocate {p : Position} {m : Move} {piece : Piece}
    {c : Color} (hm : LegalMove p m) (hsrc : p.board m.src = some piece) :
    m.src ∈ p.board.kingSquares c ↔
      ((placedOf piece m).color = c ∧ (placedOf piece m).kind = .king) := by
  constructor
  · intro hmem
    have hk := (Board.mem_kingSquares _ _ _).mp hmem
    rw [hsrc] at hk
    have hp : piece = { color := c, kind := .king } := Option.some.inj hk
    refine ⟨?_, ?_⟩
    · rw [placedOf_color, hp]
    · rw [placedOf_kind_king_iff hm hsrc, hp]
  · intro ⟨hc, hk⟩
    have hkind : piece.kind = .king := (placedOf_kind_king_iff hm hsrc).mp hk
    have hcc : piece.color = c := by
      rwa [placedOf_color] at hc
    have hp : piece = { color := c, kind := .king } :=
      Piece.eq_of_color_kind piece hcc hkind
    rw [Board.mem_kingSquares, hsrc, hp]

theorem castlingSide?_src_dst {m : Move} {c : Color} {side : CastlingSide}
    (h : m.castlingSide? c = some side) :
    m.src = (⟨c, side⟩ : CastlingRight).kingSquare ∧
      m.dst = (⟨c, side⟩ : CastlingRight).kingDest ∧
      m.promotion = none := by
  simp only [Move.castlingSide?] at h
  split_ifs at h with hk hq
  · simp only [Bool.and_eq_true, beq_iff_eq] at hk
    cases h
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    cases h
    exact ⟨hq.1.1, hq.1.2, hq.2⟩

theorem castleMoveOk_spec {p : Position} {m : Move} {side : CastlingSide}
    (hok : p.castleMoveOk m = true)
    (hside : m.castlingSide? p.toMove = some side) :
    let r : CastlingRight := ⟨p.toMove, side⟩
    p.board r.rookSquare = some { color := p.toMove, kind := .rook } ∧
      p.board r.rookDest = none := by
  intro r
  unfold castleMoveOk at hok
  simp only [hside, Bool.and_eq_true, beq_iff_eq] at hok
  refine ⟨hok.1.1.2, ?_⟩
  have hclear : CastlingRight.pathClear r p.board = true := hok.1.2
  unfold CastlingRight.pathClear at hclear
  have hforall : ∀ s ∈ r.clearSquares, (p.board s).isNone = true :=
    decide_eq_true_eq.mp hclear
  have hempty := hforall _ (CastlingRight.rookDest_mem_clearSquares r)
  exact Option.isNone_iff_eq_none.mp hempty

theorem boardAfter_of_plain {p : Position} {m : Move} {piece : Piece}
    (hnk : piece.kind ≠ .king)
    (hep : ¬ (piece.kind = .pawn ∧ p.enPassant = some m.dst ∧
      (p.board m.dst).isNone = true)) :
    p.boardAfter m piece = p.board.relocate m.src m.dst (placedOf piece m) := by
  unfold boardAfter
  have hk : (piece.kind == .king) = false := beq_eq_false_iff_ne.mpr hnk
  simp only [hk, Bool.false_eq_true, ↓reduceIte, placedOf]
  split_ifs with h
  · refine (hep ?_).elim
    simp only [beq_iff_eq, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · rfl

theorem boardAfter_of_king {p : Position} {m : Move} {piece : Piece}
    (hk : piece.kind = .king) :
    p.boardAfter m piece =
      match m.castlingSide? piece.color with
      | some side =>
        (p.board.relocate m.src m.dst (placedOf piece m)).relocate
          (⟨piece.color, side⟩ : CastlingRight).rookSquare
          (⟨piece.color, side⟩ : CastlingRight).rookDest
          { color := piece.color, kind := .rook }
      | none => p.board.relocate m.src m.dst (placedOf piece m) := by
  unfold boardAfter placedOf
  have hkb : (piece.kind == .king) = true := by simp [hk]
  simp only [hkb, ↓reduceIte]
  cases m.castlingSide? piece.color <;> rfl

theorem boardAfter_of_ep {p : Position} {m : Move} {piece : Piece}
    (hp : piece.kind = .pawn)
    (hep : p.enPassant = some m.dst)
    (hempty : (p.board m.dst).isNone = true) :
    p.boardAfter m piece =
      (p.board.relocate m.src m.dst (placedOf piece m)).clear
        ⟨m.dst.file, m.src.rank⟩ := by
  unfold boardAfter placedOf
  have hnk : (piece.kind == .king) = false := by simp [hp]
  have hpawn : (piece.kind == .pawn) = true := by simp [hp]
  have hep' : (p.enPassant == some m.dst) = true := by simp [hep]
  simp [hnk, hpawn, hep', hempty]
  rfl

theorem ep_captured_square (c : Color) (src dst : Square)
    (hpa : PawnAttacks c src dst)
    (hrank : dst.rank = pawnJumpOverRank c.other) :
    src.rank = pawnJumpToRank c.other ∧
      (⟨dst.file, src.rank⟩ : Square) = pawnJumpLanding c.other dst := by
  revert c src dst
  native_decide

theorem enPassantAfter_none_or {m : Move} {piece : Piece} {b : Board} :
    enPassantAfter m piece b = none ∨
      (piece.kind = .pawn ∧ m.src.file = m.dst.file ∧
        m.src.rank = pawnStartRank piece.color ∧
        m.dst.rank = pawnJumpToRank piece.color ∧
        enPassantAfter m piece b =
          some ⟨m.src.file, pawnJumpOverRank piece.color⟩ ∧
        existsPawnAttacking b piece.color.other
          ⟨m.src.file, pawnJumpOverRank piece.color⟩ = true) := by
  unfold enPassantAfter
  dsimp
  split_ifs with h hcap
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact Or.inr ⟨h.1.1.1, h.1.1.2, h.1.2, h.2, rfl, hcap⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem relocate_structural (b : Board) (src dst : Square) (placed : Piece)
    (hkings : ∀ c, (b.kingSquares c).card = 1)
    (hocc : ∀ c, (b.occupiedBy c).card ≤ 16)
    (hpawns : b.noPawnOnBackRank = true)
    (hsrc_map : (b src).map (·.color) = some placed.color)
    (hdst : ∀ c, dst ∉ b.kingSquares c)
    (hsame : ∀ c, src ∈ b.kingSquares c ↔
      (placed.color = c ∧ placed.kind = .king))
    (hpawn : placed.kind = .pawn → dst.rank.val ≠ 0 ∧ dst.rank.val ≠ 7) :
    (∀ c, ((b.relocate src dst placed).kingSquares c).card = 1) ∧
      (∀ c, ((b.relocate src dst placed).occupiedBy c).card ≤ 16) ∧
      (b.relocate src dst placed).noPawnOnBackRank = true :=
  ⟨fun c => Board.kingSquares_relocate_card b src dst placed c (hkings c)
      (hdst c) (hsame c),
    fun c => Nat.le_trans
      (Board.occupiedBy_relocate_card_le b src dst placed c hsrc_map) (hocc c),
    Board.noPawnOnBackRank_relocate b src dst placed hpawns hpawn⟩

/-- Playing a legal move from a valid position yields a valid position. -/
theorem valid_play {p : Position} {m : Move}
    (hv : Valid p) (hm : LegalMove p m) : Valid (p.play m) := by
  obtain ⟨piece, hsrc, hcol, hdest, hsafe, hkind⟩ := legalMove_spec hm
  have hne := src_ne_dst_of_LegalMove hm
  have hplay := play_of_some p m hsrc
  rw [hplay]
  let placed := placedOf piece m
  let b' := p.board.relocate m.src m.dst placed
  have hplaced_color : placed.color = piece.color := placedOf_color piece m
  have hsrc_map : (p.board m.src).map (·.color) = some placed.color := by
    simp [hsrc, hplaced_color]
  have hdstk : ∀ c, m.dst ∉ p.board.kingSquares c := fun c =>
    destOk_not_mem_kingSquares hdest
  have hsame : ∀ c,
      m.src ∈ p.board.kingSquares c ↔
        (placed.color = c ∧ placed.kind = .king) :=
    fun c => kingSquares_same_of_relocate hm hsrc
  have hpawn_back :
      placed.kind = .pawn → m.dst.rank.val ≠ 0 ∧ m.dst.rank.val ≠ 7 := by
    intro hp
    have hpk : piece.kind = .pawn := by
      have hiff := placedOf_kind_king_iff hm hsrc
      cases hk : piece.kind with
      | pawn => rfl
      | king =>
        have : placed.kind = .king := hiff.mpr hk
        rw [this] at hp
        cases hp
      | knight | bishop | rook | queen =>
        have hpr := legalMove_promotion_none hm hsrc (by simp [hk])
        simp [placed, placedOf, hpr, hk] at hp
    exact placedOf_pawn_dest_not_back hv.1.2.2.1 hm hsrc hpk hp
  have hb' := relocate_structural p.board m.src m.dst placed
    hv.1.1 hv.1.2.1 hv.1.2.2.1 hsrc_map hdstk hsame hpawn_back
  refine ⟨?board, ?opp, ?cstl, ?ep⟩
  · by_cases hking : piece.kind = .king
    · -- King move, possibly with the rook.
      have hba := boardAfter_of_king (p := p) (m := m) (piece := piece) hking
      match hside : m.castlingSide? piece.color with
      | none =>
        rw [hside] at hba
        rw [hba]
        exact ⟨hb'.1, hb'.2.1, hb'.2.2, ⟨p.toMove, by simpa [hplay, hba] using hsafe⟩⟩
      | some side =>
        rw [hside] at hba
        rw [hba]
        let r : CastlingRight := ⟨piece.color, side⟩
        have hcastle : p.castleMoveOk m = true := by
          rcases hkind with ⟨hp, _⟩ | ⟨_, _, hok⟩ | ⟨_, hnc, _, _⟩
          · have h : PieceKind.king = .pawn := hking.symm.trans hp
            nomatch h
          · exact hok
          · exact (hnc ⟨hking, by rw [← hcol, hside]; rfl⟩).elim
        have hside' : m.castlingSide? p.toMove = some side := by
          rwa [hcol] at hside
        have hinfo := castleMoveOk_spec hcastle hside'
        have hsq := castlingSide?_src_dst hside
        have hrook_src : b' r.rookSquare =
            some { color := piece.color, kind := .rook } := by
          dsimp [b', placed]
          have hne1 : r.rookSquare ≠ m.dst := by
            intro h
            exact CastlingRight.rookSquare_ne_kingDest r (h.trans hsq.2.1)
          have hne2 : r.rookSquare ≠ m.src := by
            intro h
            exact CastlingRight.rookSquare_ne_kingSquare r (h.trans hsq.1)
          rw [Board.relocate_other p.board m.src m.dst r.rookSquare _ hne1 hne2]
          simpa [r, hcol] using hinfo.1
        have hrook_dst_empty : b' r.rookDest = none := by
          dsimp [b', placed]
          have hne1 : r.rookDest ≠ m.dst := by
            intro h
            exact CastlingRight.rookDest_ne_kingDest r (h.trans hsq.2.1)
          have hne2 : r.rookDest ≠ m.src := by
            intro h
            exact CastlingRight.rookDest_ne_kingSquare r (h.trans hsq.1)
          rw [Board.relocate_other p.board m.src m.dst r.rookDest _ hne1 hne2]
          simpa [r, hcol] using hinfo.2
        have hdstk' : ∀ c, r.rookDest ∉ b'.kingSquares c := by
          intro c hmem
          have := (Board.mem_kingSquares _ _ _).mp hmem
          rw [hrook_dst_empty] at this
          cases this
        have hsame' : ∀ c,
            r.rookSquare ∈ b'.kingSquares c ↔
              (({ color := piece.color, kind := .rook } : Piece).color = c ∧
                PieceKind.rook = PieceKind.king) := by
          intro c
          constructor
          · intro hmem
            have := (Board.mem_kingSquares _ _ _).mp hmem
            rw [hrook_src] at this
            cases this
          · intro h
            cases h.2
        have hb'' := relocate_structural b' r.rookSquare r.rookDest
          { color := piece.color, kind := .rook }
          hb'.1 hb'.2.1 hb'.2.2
          (by simp [hrook_src]) hdstk' (by simpa using hsame')
          (by intro h; cases h)
        exact ⟨hb''.1, hb''.2.1, hb''.2.2, ⟨p.toMove, by
          simpa [hplay, hba] using hsafe⟩⟩
    · by_cases hep : piece.kind = .pawn ∧ p.enPassant = some m.dst ∧
          (p.board m.dst).isNone = true
      · have hba := boardAfter_of_ep (p := p) (m := m) (piece := piece)
          hep.1 hep.2.1 hep.2.2
        rw [hba]
        let cap : Square := ⟨m.dst.file, m.src.rank⟩
        have hcap_not_king : ∀ c, cap ∉ b'.kingSquares c := by
          intro c hmem
          have hks := (Board.mem_kingSquares _ _ _).mp hmem
          have hplaced_not_king : placed.kind ≠ .king := by
            intro hk
            have : piece.kind = .king :=
              (placedOf_kind_king_iff hm hsrc).mp hk
            rw [hep.1] at this
            cases this
          by_cases hcap_dst : cap = m.dst
          · dsimp [b', placed] at hks
            rw [hcap_dst, Board.relocate_dst] at hks
            exact hplaced_not_king (congrArg Piece.kind (Option.some.inj hks))
          · by_cases hcap_src : cap = m.src
            · dsimp [b', placed] at hks
              rw [hcap_src, Board.relocate_src p.board m.src m.dst _ hne] at hks
              cases hks
            · dsimp [b', placed] at hks
              rw [Board.relocate_other p.board m.src m.dst cap _ hcap_dst hcap_src] at hks
              have hfile : m.src.file ≠ m.dst.file := by
                intro h
                apply hcap_src
                apply Square.ext
                · simp [cap, h]
                · rfl
              have hp : piece = { color := piece.color, kind := .pawn } :=
                Piece.eq_of_color_kind piece rfl hep.1
              have hpok := pawnMoveOk_of_LegalMove hm hsrc hep.1
              have hpa := pawnMoveOk_attacks_of_ne_file
                (by rw [hsrc, hp]) hpok hfile
              have hve := valid_enPassant p hv
              have hve' :
                  m.dst.rank = pawnJumpOverRank p.toMove.other ∧
                    p.board (pawnJumpLanding p.toMove.other m.dst) =
                      some { color := p.toMove.other, kind := .pawn } := by
                rw [hep.2.1] at hve
                exact ⟨hve.1, hve.2.1⟩
              have hcap_eq := ep_captured_square piece.color m.src m.dst hpa
                (by simpa [hcol] using hve'.1)
              have hcap_pawn : p.board cap =
                  some { color := p.toMove.other, kind := .pawn } := by
                simpa [cap, hcap_eq.2, hcol] using hve'.2
              rw [hcap_pawn] at hks
              cases hks
        have hbclear :
            (∀ c, ((b'.clear cap).kingSquares c).card = 1) ∧
              (∀ c, ((b'.clear cap).occupiedBy c).card ≤ 16) ∧
              (b'.clear cap).noPawnOnBackRank = true :=
          ⟨fun c => Board.kingSquares_clear_card b' cap c (hb'.1 c)
              (hcap_not_king c),
            fun c => Nat.le_trans (Board.occupiedBy_clear_card_le b' cap c)
              (hb'.2.1 c),
            Board.noPawnOnBackRank_clear b' cap hb'.2.2⟩
        exact ⟨hbclear.1, hbclear.2.1, hbclear.2.2, ⟨p.toMove, by
          simpa [hplay, hba] using hsafe⟩⟩
      · have hba := boardAfter_of_plain (p := p) (m := m) (piece := piece)
          hking hep
        rw [hba]
        exact ⟨hb'.1, hb'.2.1, hb'.2.2, ⟨p.toMove, by
          simpa [hplay, hba] using hsafe⟩⟩
  · simpa [hplay] using hsafe
  · intro r hr
    simp only [castlingAfter, Finset.mem_filter] at hr
    exact hr.2
  · cases hen : enPassantAfter m piece (p.boardAfter m piece) with
    | none =>
      simp [enPassantOk]
    | some ep =>
      have hchar := enPassantAfter_none_or (m := m) (piece := piece)
        (b := p.boardAfter m piece)
      rcases hchar with hnone | ⟨hpawn, hfile, hstart, hto, hep_eq, hcap⟩
      · cases (hen.symm.trans hnone)
      · have hep' : ep = ⟨m.src.file, pawnJumpOverRank piece.color⟩ := by
          have := hen.symm.trans hep_eq
          exact Option.some.inj this
        subst hep'
        refine (enPassantOk_some _
            ⟨m.src.file, pawnJumpOverRank piece.color⟩ rfl).mpr ⟨?_, ?_, ?_⟩
        · simpa [Color.other_other] using congrArg pawnJumpOverRank hcol
        · -- The jumped pawn now stands on `m.dst`.
          have hpr : m.promotion = none := by
            have hp : piece = { color := piece.color, kind := .pawn } :=
              Piece.eq_of_color_kind piece rfl hpawn
            have hpok := pawnMoveOk_of_LegalMove hm hsrc hpawn
            have hcases := pawnMoveOk_promotion_of (by rw [hsrc, hp]) hpok
            rcases hcases with ⟨hpr, _⟩ | ⟨_, hnone⟩
            · have hbad : pawnJumpToRank piece.color = pawnPromotionRank piece.color :=
                hto.symm.trans hpr
              have hne : pawnJumpToRank piece.color ≠ pawnPromotionRank piece.color := by
                cases piece.color <;> decide
              exact (hne hbad).elim
            · exact hnone
          have hdst_ne_cap : m.dst ≠ ⟨m.dst.file, m.src.rank⟩ := by
            intro heq
            have hrr : m.dst.rank = m.src.rank := by
              rw [heq]
            have hbad : pawnJumpToRank piece.color = pawnStartRank piece.color :=
              hto.symm.trans (hrr.trans hstart)
            have hne : pawnJumpToRank piece.color ≠ pawnStartRank piece.color := by
              cases piece.color <;> decide
            exact (hne hbad).elim
          have hnk : piece.kind ≠ .king := by
            intro h
            rw [h] at hpawn
            cases hpawn
          have hpiece : piece = { color := piece.color, kind := .pawn } :=
            Piece.eq_of_color_kind piece rfl hpawn
          have hplaced_pawn : placedOf piece m =
              { color := piece.color, kind := .pawn } := by
            unfold placedOf
            rw [hpr]
            exact hpiece
          rw [hasPawn_eq_true_iff]
          have hland : pawnJumpLanding piece.color
              ⟨m.src.file, pawnJumpOverRank piece.color⟩ = m.dst := by
            apply Square.ext
            · simp [pawnJumpLanding, hfile]
            · simp [pawnJumpLanding, hto]
          simp only [Color.other_other]
          rw [← hcol, hland]
          by_cases hep2 : piece.kind = .pawn ∧ p.enPassant = some m.dst ∧
              (p.board m.dst).isNone = true
          · have hba := boardAfter_of_ep (p := p) (m := m) (piece := piece)
              hep2.1 hep2.2.1 hep2.2.2
            rw [hba]
            rw [Board.clear_other (s := ⟨m.dst.file, m.src.rank⟩) (x := m.dst)
              _ hdst_ne_cap]
            rw [Board.relocate_dst, hplaced_pawn]
          · have hba := boardAfter_of_plain (p := p) (m := m) (piece := piece)
              hnk hep2
            rw [hba, Board.relocate_dst, hplaced_pawn]
        · simpa [hcol] using hcap

end Position

end Chess
