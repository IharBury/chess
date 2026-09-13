import Chess.LoneKing

/-!
# Lone king versus bishops of one color

Structural facts about positions in which one player has only a king,
preserved by every legal move, and the material verdict they support: a
bare king cannot be checkmated by a king and any number of bishops all
standing on squares of one color.

`Position.LoneShape c p` records that every piece of color `c` is a king,
that neither player has two kings, and that the kings are not adjacent.
It holds in every valid position with a bare king and is preserved by
legal moves, without any appeal to validity: a legal move never creates a
king, and it leaves the mover's king unattacked, so the kings cannot end
up adjacent. `Position.OnlyBishopsOn c.other χ p` adds that the other
player's pieces besides the king are bishops on squares of color `χ`; bishops keep
their square color, so this is preserved too. In such a position the
player to move is never checkmated: the strong side is not in check at
all, and the lone king in check from a bishop always has an orthogonal
neighbor that no bishop can attack and the strong king does not cover.
-/

namespace Chess

namespace Position

/-! ### Facts about a legal move -/

theorem castlingSide?_promotion {m : Move} {c : Color} {side : CastlingSide}
    (h : m.castlingSide? c = some side) : m.promotion = none := by
  simp only [Move.castlingSide?] at h
  split_ifs at h with h₁ h₂
  · have := (Bool.and_eq_true_iff.mp h₁).2
    simpa using this
  · have := (Bool.and_eq_true_iff.mp h₂).2
    simpa using this

/-- The checks that `isLegalMove` performs on the moving piece. -/
theorem legalMove_spec {p : Position} {m : Move} (h : LegalMove p m) :
    ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
      p.destOk m = true ∧ (p.play m).board.kingIsAttacked p.toMove = false ∧
      ((piece.kind = .pawn ∧ p.pawnMoveOk m = true) ∨
        (piece.kind = .king ∧ (m.castlingSide? p.toMove).isSome = true ∧
          p.castleMoveOk m = true) ∨
        (piece.kind ≠ .pawn ∧ ¬ (piece.kind = .king ∧ (m.castlingSide? p.toMove).isSome = true) ∧
          p.board.attacks m.src m.dst = true ∧ m.promotion = none)) := by
  unfold LegalMove isLegalMove at h
  split at h
  · cases h
  · rename_i piece hpiece
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hcol, hdest⟩, hkind⟩, hsafe⟩ := h
    refine ⟨piece, hpiece, hcol, hdest, hsafe, ?_⟩
    split at hkind
    · rename_i hp
      exact Or.inl ⟨hp, hkind⟩
    · rename_i hp
      split at hkind
      · rename_i hk
        exact Or.inr (Or.inl ⟨hk.1, hk.2, hkind⟩)
      · rename_i hk
        have hkind' := Bool.and_eq_true_iff.mp hkind
        exact Or.inr (Or.inr ⟨hp, hk, hkind'.1, beq_iff_eq.mp hkind'.2⟩)

/-- A legal move by a piece other than a pawn carries no promotion. -/
theorem legalMove_promotion_none {p : Position} {m : Move} {piece : Piece}
    (h : LegalMove p m) (hsrc : p.board m.src = some piece) (hk : piece.kind ≠ .pawn) :
    m.promotion = none := by
  obtain ⟨piece', hsrc', _, _, _, hkind⟩ := legalMove_spec h
  have := hsrc.symm.trans hsrc'
  rw [Option.some.injEq] at this
  subst this
  rcases hkind with ⟨hp, _⟩ | ⟨_, hc, _⟩ | ⟨_, _, _, hpr⟩
  · exact (hk hp).elim
  · obtain ⟨side, hside⟩ := Option.isSome_iff_exists.mp hc
    exact castlingSide?_promotion hside
  · exact hpr

/-- A legal promotion is to a kind a pawn may become: never a king. -/
theorem legalMove_promotion_canPromoteTo {p : Position} {m : Move} {k : PieceKind}
    (h : LegalMove p m) (hpr : m.promotion = some k) : k.canPromoteTo = true := by
  obtain ⟨piece, hsrc, _, _, _, hkind⟩ := legalMove_spec h
  rcases hkind with ⟨_, hok⟩ | ⟨_, hc, _⟩ | ⟨_, _, _, hpr'⟩
  · unfold pawnMoveOk at hok
    rw [hsrc] at hok
    simp only [Bool.and_eq_true] at hok
    have hpromo := hok.2
    split at hpromo
    · rw [hpr] at hpromo
      exact hpromo
    · rw [hpr] at hpromo
      cases hpromo
  · obtain ⟨side, hside⟩ := Option.isSome_iff_exists.mp hc
    rw [castlingSide?_promotion hside] at hpr
    cases hpr
  · rw [hpr'] at hpr
    cases hpr

/-- A legal castling manoeuvre has the mover's rook on its starting
square. -/
theorem legalMove_castling_rook {p : Position} {m : Move} {piece : Piece} {side : CastlingSide}
    (h : LegalMove p m) (hsrc : p.board m.src = some piece) (hk : piece.kind = .king)
    (hside : m.castlingSide? piece.color = some side) :
    p.board (⟨piece.color, side⟩ : CastlingRight).rookSquare =
      some { color := piece.color, kind := .rook } := by
  obtain ⟨piece', hsrc', hcol, _, _, hkind⟩ := legalMove_spec h
  have := hsrc.symm.trans hsrc'
  rw [Option.some.injEq] at this
  subst this
  rw [hcol] at hside ⊢
  rcases hkind with ⟨hp, _⟩ | ⟨_, _, hok⟩ | ⟨_, hnk, _, _⟩
  · rw [hk] at hp
    cases hp
  · unfold castleMoveOk at hok
    rw [hside] at hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    exact hok.1.1.2
  · exact (hnk ⟨hk, by simp [hside]⟩).elim

/-- A legal move of a piece that is neither a pawn nor a castling king
follows the attack geometry of the piece. -/
theorem legalMove_attacks {p : Position} {m : Move} {piece : Piece}
    (h : LegalMove p m) (hsrc : p.board m.src = some piece) (hp : piece.kind ≠ .pawn)
    (hk : piece.kind ≠ .king) : p.board.attacks m.src m.dst = true := by
  obtain ⟨piece', hsrc', _, _, _, hkind⟩ := legalMove_spec h
  have := hsrc.symm.trans hsrc'
  rw [Option.some.injEq] at this
  subst this
  rcases hkind with ⟨hp', _⟩ | ⟨hk', _, _⟩ | ⟨_, _, hatt, _⟩
  · exact (hp hp').elim
  · exact (hk hk').elim
  · exact hatt

/-- After a legal move the mover's king is not attacked. -/
theorem legalMove_safe {p : Position} {m : Move} (h : LegalMove p m) :
    (p.play m).board.kingIsAttacked p.toMove = false :=
  (legalMove_spec h).choose_spec.2.2.2.1

/-- The piece a legal move puts on its destination: the moving piece, or
the promoted piece. -/
def placed (m : Move) (piece : Piece) : Piece :=
  match m.promotion with
  | some k => { color := piece.color, kind := k }
  | none => piece

@[simp] theorem placed_color (m : Move) (piece : Piece) : (placed m piece).color = piece.color := by
  unfold placed
  split <;> rfl

theorem placed_of_promotion_none {m : Move} (h : m.promotion = none) (piece : Piece) :
    placed m piece = piece := by
  simp [placed, h]

theorem boardAfter_eq (p : Position) (m : Move) (piece : Piece) :
    p.boardAfter m piece =
      let b' := p.board.relocate m.src m.dst (placed m piece)
      if piece.kind == .king then
        match m.castlingSide? piece.color with
        | some side =>
          let r : CastlingRight := ⟨piece.color, side⟩
          b'.relocate r.rookSquare r.rookDest { color := piece.color, kind := .rook }
        | none => b'
      else if piece.kind == .pawn && p.enPassant == some m.dst &&
          (p.board m.dst).isNone then
        b'.clear ⟨m.dst.file, m.src.rank⟩
      else
        b' := rfl

/-- Where a piece standing on the board after a move came from: it is the
piece placed on the destination, the rook of a castling manoeuvre on its
destination, or a piece that did not move. -/
theorem play_board_some {p : Position} {m : Move} {piece : Piece}
    (hsrc : p.board m.src = some piece) {x : Square} {q : Piece}
    (hx : (p.play m).board x = some q) :
    (x = m.dst ∧ q = placed m piece) ∨
      (piece.kind = .king ∧ ∃ side, m.castlingSide? piece.color = some side ∧
        x = (⟨piece.color, side⟩ : CastlingRight).rookDest ∧
        q = { color := piece.color, kind := .rook }) ∨
      (x ≠ m.src ∧ x ≠ m.dst ∧ p.board x = some q) := by
  rw [play_of_some p m hsrc] at hx
  simp only [boardAfter_eq] at hx
  split at hx
  · rename_i hking
    split at hx
    · rename_i side hside
      simp only [Board.relocate] at hx
      split_ifs at hx with h₁ h₂ h₃ h₄
      · exact Or.inr (Or.inl ⟨beq_iff_eq.mp hking, side, hside, h₁, (Option.some.inj hx).symm⟩)
      · exact Or.inl ⟨h₃, (Option.some.inj hx).symm⟩
      · exact Or.inr (Or.inr ⟨h₄, h₃, hx⟩)
    · simp only [Board.relocate] at hx
      split_ifs at hx with h₁ h₂
      · exact Or.inl ⟨h₁, (Option.some.inj hx).symm⟩
      · exact Or.inr (Or.inr ⟨h₂, h₁, hx⟩)
  · split at hx
    · simp only [Board.clear, Board.relocate] at hx
      split_ifs at hx with h₁ h₂ h₃
      · exact Or.inl ⟨h₂, (Option.some.inj hx).symm⟩
      · exact Or.inr (Or.inr ⟨h₃, h₂, hx⟩)
    · simp only [Board.relocate] at hx
      split_ifs at hx with h₁ h₂
      · exact Or.inl ⟨h₁, (Option.some.inj hx).symm⟩
      · exact Or.inr (Or.inr ⟨h₂, h₁, hx⟩)

/-- A piece of the opponent of the mover did not move. -/
theorem play_board_some_of_color_ne {p : Position} {m : Move} {piece : Piece}
    (hsrc : p.board m.src = some piece) {x : Square} {q : Piece}
    (hx : (p.play m).board x = some q) (hq : q.color ≠ piece.color) :
    x ≠ m.src ∧ x ≠ m.dst ∧ p.board x = some q := by
  rcases play_board_some hsrc hx with ⟨_, hq'⟩ | ⟨_, _, _, _, hq'⟩ | h
  · exact (hq (by rw [hq', placed_color])).elim
  · exact (hq (by rw [hq'])).elim
  · exact h

/-- A king standing on the board after a legal move is the moved king on
the destination, or a king that did not move. -/
theorem play_board_king {p : Position} {m : Move} {piece : Piece} (h : LegalMove p m)
    (hsrc : p.board m.src = some piece) {x : Square} {d : Color}
    (hx : (p.play m).board x = some { color := d, kind := .king }) :
    (x = m.dst ∧ piece = { color := d, kind := .king }) ∨
      (x ≠ m.src ∧ x ≠ m.dst ∧ p.board x = some { color := d, kind := .king }) := by
  rcases play_board_some hsrc hx with ⟨hxd, hq⟩ | ⟨_, _, _, _, hq⟩ | h'
  · refine Or.inl ⟨hxd, ?_⟩
    cases hpr : m.promotion with
    | none =>
      rw [placed_of_promotion_none hpr] at hq
      exact hq.symm
    | some k =>
      have hk := legalMove_promotion_canPromoteTo h hpr
      simp only [placed, hpr, Piece.mk.injEq] at hq
      rw [← hq.2] at hk
      cases hk
  · cases hq
  · exact Or.inr h'

theorem Board.kingIsAttacked_of_attacks {b : Board} {d : Color} {s t : Square} {k : PieceKind}
    (ht : b t = some { color := d, kind := .king })
    (hs : b s = some { color := d.other, kind := k })
    (hatt : b.attacks s t = true) : b.kingIsAttacked d = true := by
  unfold Board.kingIsAttacked
  rw [decide_eq_true_iff]
  exact ⟨t, (Board.mem_kingSquares _ _ _).mpr ht, s, by simp [hs], hatt⟩

/-- Unfolding `kingIsAttacked`. -/
theorem Board.exists_of_kingIsAttacked {b : Board} {d : Color} (h : b.kingIsAttacked d = true) :
    ∃ t s q, b t = some { color := d, kind := .king } ∧ b s = some q ∧ q.color = d.other ∧
      b.attacks s t = true := by
  unfold Board.kingIsAttacked at h
  rw [decide_eq_true_iff] at h
  obtain ⟨t, ht, s, hs, hatt⟩ := h
  cases hq : b s with
  | none => simp [hq] at hs
  | some q =>
    rw [hq] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    exact ⟨t, s, q, (Board.mem_kingSquares _ _ _).mp ht, hq, hs, hatt⟩

/-! ### The shape of a lone-king position -/

/-- Every piece of color `c` is a king, neither player has two kings, and
the kings are not adjacent. -/
structure LoneShape (c : Color) (p : Position) : Prop where
  /-- The player `c` has only a king. -/
  lone : LoneFor c p
  /-- No player has two kings. -/
  oneKing : ∀ d s t, p.board s = some { color := d, kind := .king } →
    p.board t = some { color := d, kind := .king } → s = t
  /-- The kings are not adjacent. -/
  noAdj : ∀ s t, p.board s = some { color := c, kind := .king } →
    p.board t = some { color := c.other, kind := .king } → ¬ KingAttacks s t

theorem Color.eq_or_eq_other (a c : Color) : a = c ∨ a = c.other := by
  cases a <;> cases c <;> simp

/-- Every valid position with a bare king has the shape. -/
theorem LoneShape.of_valid {c : Color} {p : Position} (hv : Valid p) (hl : LoneFor c p) :
    LoneShape c p := by
  obtain ⟨⟨hkings, _, _, _⟩, hopp, _, _⟩ := hv
  refine ⟨hl, ?_, ?_⟩
  · intro d s t hs ht
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hkings d)
    have hs' : s ∈ p.board.kingSquares d := (Board.mem_kingSquares _ _ _).mpr hs
    have ht' : t ∈ p.board.kingSquares d := (Board.mem_kingSquares _ _ _).mpr ht
    rw [ha, Finset.mem_singleton] at hs' ht'
    exact hs'.trans ht'.symm
  · intro s t hs ht hatt
    rcases Color.eq_or_eq_other p.toMove c with htm | htm
    · rw [htm] at hopp
      have := Board.kingIsAttacked_of_attacks ht (by rw [Color.other_other]; exact hs)
        (by rw [Board.attacks_king hs]; exact decide_eq_true hatt)
      exact Bool.false_ne_true (hopp.symm.trans this)
    · rw [htm, Color.other_other] at hopp
      have := Board.kingIsAttacked_of_attacks hs ht
        (by rw [Board.attacks_king ht]; exact decide_eq_true (kingAttacks_symmetric.mp hatt))
      exact Bool.false_ne_true (hopp.symm.trans this)

/-- The shape is preserved by every legal move. -/
theorem LoneShape.of_play {c : Color} {p : Position} {m : Move} (h : LoneShape c p)
    (hm : LegalMove p m) : LoneShape c (p.play m) := by
  obtain ⟨piece, hsrc, hcol, _, _, _⟩ := legalMove_spec hm
  refine ⟨?_, ?_, ?_⟩
  · intro x q hx hq
    rcases play_board_some hsrc hx with ⟨_, hq'⟩ | ⟨hk, side, hside, _, hq'⟩ | ⟨_, _, hx'⟩
    · have hpc : piece.color = c := by rw [← hq, hq', placed_color]
      have hpk : piece.kind = .king := h.lone _ _ hsrc hpc
      rw [hq', placed_of_promotion_none (legalMove_promotion_none hm hsrc (by rw [hpk]; decide))]
      exact hpk
    · have hpc : piece.color = c := by rw [← hq, hq']
      have hrook := legalMove_castling_rook hm hsrc hk hside
      have := h.lone _ _ hrook hpc
      cases this
    · exact h.lone _ _ hx' hq
  · intro d s t hs ht
    rcases play_board_king hm hsrc hs with ⟨hsd, hps⟩ | ⟨hss, _, hs'⟩ <;>
      rcases play_board_king hm hsrc ht with ⟨htd, hpt⟩ | ⟨hts, _, ht'⟩
    · exact hsd.trans htd.symm
    · exact absurd (h.oneKing d _ _ (hps ▸ hsrc) ht') (Ne.symm hts)
    · exact absurd (h.oneKing d _ _ (hpt ▸ hsrc) hs') (Ne.symm hss)
    · exact h.oneKing d _ _ hs' ht'
  · intro s t hs ht hatt
    have hsafe := legalMove_safe hm
    rcases Color.eq_or_eq_other p.toMove c with htm | htm
    · rw [htm] at hsafe
      have := Board.kingIsAttacked_of_attacks hs ht
        (by rw [Board.attacks_king ht]; exact decide_eq_true (kingAttacks_symmetric.mp hatt))
      exact Bool.false_ne_true (hsafe.symm.trans this)
    · rw [htm] at hsafe
      have := Board.kingIsAttacked_of_attacks ht (by rw [Color.other_other]; exact hs)
        (by rw [Board.attacks_king hs]; exact decide_eq_true hatt)
      exact Bool.false_ne_true (hsafe.symm.trans this)

theorem LoneShape.of_reachable {c : Color} {p q : Position} (h : LoneShape c p)
    (hr : Reachable p q) : LoneShape c q := by
  induction hr with
  | refl => exact h
  | step m _ hleg ih => exact ih.of_play hleg

/-! ### Bishops on squares of one color -/

theorem Board.bishopAttacks_of_attacks {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .bishop }) (hatt : b.attacks s t = true) :
    BishopAttacks s t := by
  unfold Board.attacks at hatt
  rw [h] at hatt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hatt
  exact hatt.1

/-- A piece is determined by its color and kind. -/
theorem Piece.eq_mk {q : Piece} {c : Color} {k : PieceKind} (hc : q.color = c) (hk : q.kind = k) :
    q = { color := c, kind := k } := by
  cases q
  simp only at hc hk
  rw [hc, hk]

/-- The property is preserved by every legal move: a bishop keeps the color
of its square, nothing is promoted, and no rook castles. -/
theorem OnlyBishopsOn.of_play {s χ : Color} {p : Position} {m : Move}
    (h : OnlyBishopsOn s χ p) (hm : LegalMove p m) : OnlyBishopsOn s χ (p.play m) := by
  obtain ⟨piece, hsrc, _, _, _, _⟩ := legalMove_spec hm
  intro x q hx hq hnk
  rcases play_board_some hsrc hx with ⟨hxd, hq'⟩ | ⟨hk, side, hside, _, hq'⟩ | ⟨_, _, hx'⟩
  · have hpc : piece.color = s := by rw [← hq, hq', placed_color]
    have hpk : piece.kind ≠ .pawn := by
      intro hp
      by_cases hk : piece.kind = .king
      · rw [hk] at hp
        cases hp
      · have := (h _ _ hsrc hpc hk).1
        rw [hp] at this
        cases this
    rw [placed_of_promotion_none (legalMove_promotion_none hm hsrc hpk)] at hq'
    subst hq'
    obtain ⟨hb, hsχ⟩ := h _ _ hsrc hpc hnk
    refine ⟨hb, ?_⟩
    have hatt := legalMove_attacks hm hsrc hpk (by rw [hb]; decide)
    rw [Piece.eq_mk hpc hb] at hsrc
    have hgeo := Board.bishopAttacks_of_attacks hsrc hatt
    rw [hxd, ← bishopAttacks_same_color hgeo]
    exact hsχ
  · have hpc : piece.color = s := by rw [← hq, hq']
    have := (h _ _ (legalMove_castling_rook hm hsrc hk hside) hpc (by simp)).1
    cases this
  · exact h _ _ hx' hq hnk

theorem OnlyBishopsOn.of_reachable {s χ : Color} {p q : Position} (h : OnlyBishopsOn s χ p)
    (hr : Reachable p q) : OnlyBishopsOn s χ q := by
  induction hr with
  | refl => exact h
  | step m _ hleg ih => exact ih.of_play hleg

/-- A piece of the strong side attacking a square is its king, adjacent to
the square, or a bishop, in which case the square has color `χ`. -/
theorem OnlyBishopsOn.attacker {c χ : Color} {p : Position} (hb : OnlyBishopsOn c.other χ p)
    {b : Board} {s t : Square} {q : Piece} (hs : p.board s = some q) (hs' : b s = some q)
    (hq : q.color = c.other) (hatt : b.attacks s t = true) :
    (q = { color := c.other, kind := .king } ∧ KingAttacks s t) ∨ t.color = χ := by
  by_cases hk : q.kind = .king
  · rw [Piece.eq_mk hq hk] at hs'
    rw [Board.attacks_king hs'] at hatt
    exact Or.inl ⟨Piece.eq_mk hq hk, of_decide_eq_true hatt⟩
  · obtain ⟨hbish, hsχ⟩ := hb _ _ hs hq hk
    rw [Piece.eq_mk hq hbish] at hs'
    exact Or.inr ((bishopAttacks_same_color (Board.bishopAttacks_of_attacks hs' hatt)).symm.trans
      hsχ)

/-- The strong side is never in check: the lone king is not adjacent to
its king. -/
theorem LoneShape.strong_not_inCheck {c : Color} {p : Position} (hs : LoneShape c p)
    (htm : p.toMove = c.other) : p.inCheck = false := by
  unfold inCheck
  rw [htm]
  cases hatt : p.board.kingIsAttacked c.other with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨t, s, q, ht, hsq, hqc, hatt'⟩ := Board.exists_of_kingIsAttacked hatt
    rw [Color.other_other] at hqc
    rw [Piece.eq_mk hqc (hs.lone _ _ hsq hqc)] at hsq
    rw [Board.attacks_king hsq] at hatt'
    exact hs.noAdj s t hsq ht (of_decide_eq_true hatt')

/-- The lone king on `k`, a square of the bishops' color, may step to an
orthogonal neighbor `e` that the strong king does not attack. -/
theorem LoneShape.escape_legal {c χ : Color} {p : Position} (hs : LoneShape c p)
    (hb : OnlyBishopsOn c.other χ p) (htm : p.toMove = c) {k e : Square}
    (hk : p.board k = some { color := c, kind := .king })
    (hkχ : k.color = χ) (ho : OrthogonalAdjacent k e)
    (hne : ∀ w, p.board w = some { color := c.other, kind := .king } → ¬ KingAttacks w e) :
    LegalMove p (Move.std k e) := by
  have heχ : e.color = χ.other := by rw [orthoAdj_color ho, hkχ]
  have hke : k ≠ e := orthoAdj_ne ho
  have hempty : p.board e = none := by
    cases hq : p.board e with
    | none => rfl
    | some q =>
      exfalso
      rcases Color.eq_or_eq_other q.color c with hqc | hqc
      · exact hke (hs.oneKing c _ _ hk (by rw [hq, Piece.eq_mk hqc (hs.lone _ _ hq hqc)]))
      · by_cases hqk : q.kind = .king
        · exact hs.noAdj k e hk (by rw [hq, Piece.eq_mk hqc hqk]) (orthoAdj_kingAttacks ho)
        · exact Color.other_ne χ ((hb _ _ hq hqc hqk).2.symm.trans heχ).symm
  have hside : (Move.std k e).castlingSide? c = none := castlingSide_none_of_ortho c ho
  have hboard :
      (p.play (Move.std k e)).board = p.board.relocate k e { color := c, kind := .king } := by
    rw [play_of_some p _ hk]
    exact boardAfter_king_no_castle p _ hside rfl
  have hsafe : (p.play (Move.std k e)).board.kingIsAttacked c = false := by
    rw [hboard]
    cases hatt : (p.board.relocate k e { color := c, kind := .king }).kingIsAttacked c with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨t, s, q, ht, hsq, hqc, hatt'⟩ := Board.exists_of_kingIsAttacked hatt
      have hte : t = e := by
        by_contra hte
        have htk : t ≠ k := by
          intro htk
          subst htk
          simp [Board.relocate, hte] at ht
        have ht' : p.board t = some { color := c, kind := .king } := by
          simpa [Board.relocate, hte, htk] using ht
        exact htk (hs.oneKing c _ _ ht' hk)
      subst hte
      have hse : s ≠ t := by
        intro hst
        subst hst
        simp only [Board.relocate, if_true, Option.some.injEq] at hsq
        rw [← hsq] at hqc
        exact Color.other_ne c hqc.symm
      have hsk : s ≠ k := by
        intro hsk
        subst hsk
        simp only [Board.relocate, hse, if_false, if_true] at hsq
        cases hsq
      have hsq' : p.board s = some q := by
        simpa [Board.relocate, hse, hsk] using hsq
      rcases hb.attacker hsq' hsq hqc hatt' with ⟨hqk, hatt''⟩ | htχ
      · rw [hqk] at hsq'
        exact hne s hsq' hatt''
      · exact Color.other_ne χ (heχ.symm.trans htχ)
  have hdest : p.destOk (Move.std k e) = true := by
    unfold destOk
    have : p.board (Move.std k e).dst = none := hempty
    rw [this]
  have hgeo : p.board.attacks k e = true := by
    rw [Board.attacks_king hk]
    exact decide_eq_true (orthoAdj_kingAttacks ho)
  unfold LegalMove isLegalMove
  simp only [Move.std] at hdest hside hsafe ⊢
  rw [hk, htm]
  simp [hdest, hside, hgeo, hsafe]

/-- The player to move is never checkmated. -/
theorem LoneShape.not_InCheckmate_of_onlyBishopsOn {c χ : Color} {p : Position}
    (hs : LoneShape c p) (hb : OnlyBishopsOn c.other χ p) : ¬ InCheckmate p := by
  rcases Color.eq_or_eq_other p.toMove c with htm | htm
  · cases hchk : p.inCheck with
    | false =>
      intro hm
      exact Bool.false_ne_true ((not_inCheck_not_inCheckmate hchk).symm.trans
        ((inCheckmate_eq_true_iff p).mpr hm))
    | true =>
      unfold inCheck at hchk
      rw [htm] at hchk
      obtain ⟨k, s, q, hk, hsq, hqc, hatt⟩ := Board.exists_of_kingIsAttacked hchk
      have hkχ : k.color = χ := by
        rcases hb.attacker hsq hsq hqc hatt with ⟨hqk, hatt'⟩ | hkχ
        · rw [hqk] at hsq
          exact (hs.noAdj k s hk hsq (kingAttacks_symmetric.mp hatt')).elim
        · exact hkχ
      have hleg : ∃ e, LegalMove p (Move.std k e) := by
        by_cases hw : ∃ w, p.board w = some { color := c.other, kind := .king }
        · obtain ⟨w, hw⟩ := hw
          refine ⟨kingOrthoEscape k w, hs.escape_legal hb htm hk hkχ (kingOrthoEscape_ortho k w)
            fun w' hw' => ?_⟩
          rw [hs.oneKing _ _ _ hw' hw]
          refine kingOrthoEscape_not_kingAttacks k w ?_ fun hatt' =>
            hs.noAdj k w hk hw (kingAttacks_symmetric.mp hatt')
          intro hwk
          rw [hwk, hk, Option.some.injEq] at hw
          exact Color.other_ne c (congrArg Piece.color hw).symm
        · exact ⟨horizNeighbor k, hs.escape_legal hb htm hk hkχ (horizNeighbor_ortho k)
            fun w' hw' => (hw ⟨w', hw'⟩).elim⟩
      obtain ⟨e, hleg⟩ := hleg
      intro hm
      exact ((InCheckmate_iff_forall_not_LegalMove p).mp hm).2 _ hleg
  · intro hm
    exact Bool.false_ne_true ((not_inCheck_not_inCheckmate (hs.strong_not_inCheck htm)).symm.trans
      ((inCheckmate_eq_true_iff p).mpr hm))

/-- A bare king cannot be checkmated by a king and bishops all standing on
squares of one color: every position reached is not checkmate. -/
theorem LoneShape.deadPosition_of_onlyBishopsOn {c χ : Color} {p : Position}
    (hs : LoneShape c p) (hb : OnlyBishopsOn c.other χ p) : DeadPosition p := by
  intro q hr
  exact (hs.of_reachable hr).not_InCheckmate_of_onlyBishopsOn (hb.of_reachable hr)

end Position

end Chess
