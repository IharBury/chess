import Chess.EndsGame

/-!
# 180° board rotation

A 180° rotation of the board, together with a color swap, is the
involution used to reduce a black-piece three-piece ending to the
corresponding white-piece frame.
-/

namespace Chess

namespace Square

/-- 180° rotation of the board: `a1` maps to `h8`. -/
def rot180 (s : Square) : Square :=
  ⟨⟨7 - s.file.val, by
      have := Nat.le_of_lt_succ s.file.isLt
      omega⟩,
    ⟨7 - s.rank.val, by
      have := Nat.le_of_lt_succ s.rank.isLt
      omega⟩⟩

@[simp] theorem rot180_involutive (s : Square) : s.rot180.rot180 = s := by
  rcases s with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [rot180]
  constructor <;> omega

theorem kingAttacks_rot180 (s t : Square) :
    KingAttacks s t ↔ KingAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem rookAttacks_rot180 (s t : Square) :
    RookAttacks s t ↔ RookAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem between_rot180 (s t u : Square) :
    Between s t u ↔ Between s.rot180 t.rot180 u.rot180 := by
  revert s t u
  native_decide

theorem bishopAttacks_rot180 (s t : Square) :
    BishopAttacks s t ↔ BishopAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem knightAttacks_rot180 (s t : Square) :
    KnightAttacks s t ↔ KnightAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem queenAttacks_rot180 (s t : Square) :
    QueenAttacks s t ↔ QueenAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem pawnAttacks_rot180 (c : Color) (s t : Square) :
    PawnAttacks c s t ↔ PawnAttacks c.other s.rot180 t.rot180 := by
  revert c s t
  native_decide

end Square

namespace Piece

/-- Swap the owner of a piece, keeping its kind. -/
def flip (p : Piece) : Piece :=
  { color := p.color.other, kind := p.kind }

@[simp] theorem flip_flip (p : Piece) : p.flip.flip = p := by
  rcases p with ⟨c, k⟩
  cases c <;> rfl

@[simp] theorem flip_color (p : Piece) : p.flip.color = p.color.other := rfl

@[simp] theorem flip_kind (p : Piece) : p.flip.kind = p.kind := rfl

end Piece

namespace Board

/-- Rotate the board 180° and swap colors. -/
def rot180 (b : Board) : Board :=
  fun s => (b s.rot180).map Piece.flip

theorem rot180_eq_iff {s t : Square} : s.rot180 = t ↔ s = t.rot180 := by
  constructor
  · intro h
    rw [← Square.rot180_involutive s, h]
  · intro h
    rw [h, Square.rot180_involutive]

theorem rot180_injective {s t : Square} (h : s.rot180 = t.rot180) : s = t := by
  rw [← Square.rot180_involutive s, h, Square.rot180_involutive]

theorem board_rot180_involutive (b : Board) : b.rot180.rot180 = b := by
  funext s
  unfold rot180
  rw [Square.rot180_involutive]
  cases h : b s with
  | none => simp
  | some p => simp [Piece.flip_flip]

theorem relocate_rot180 (b : Board) (src dst : Square) (p : Piece) :
    (b.relocate src dst p).rot180 =
      b.rot180.relocate src.rot180 dst.rot180 p.flip := by
  funext x
  have hiff : src = dst ↔ src.rot180 = dst.rot180 :=
    ⟨fun h => h ▸ rfl, rot180_injective⟩
  unfold relocate rot180
  by_cases h1 : x.rot180 = dst
  · have hx : x = dst.rot180 := rot180_eq_iff.mp h1
    simp [hx]
  · by_cases h2 : x.rot180 = src
    · have hx : x = src.rot180 := rot180_eq_iff.mp h2
      have hxdst : x ≠ dst.rot180 := fun h => h1 (rot180_eq_iff.mpr h)
      simp [hx, hiff]
    · have hxdst : x ≠ dst.rot180 := fun h => h1 (rot180_eq_iff.mpr h)
      have hxsrc : x ≠ src.rot180 := fun h => h2 (rot180_eq_iff.mpr h)
      simp [h1, h2, hxdst, hxsrc]

theorem between_isSome_rot180 (b : Board) (s t : Square) :
    (∃ u, Between s t u ∧ (b u).isSome = true) ↔
      (∃ u, Between s.rot180 t.rot180 u ∧ (b.rot180 u).isSome = true) := by
  constructor
  · intro ⟨u, hu, ho⟩
    refine ⟨u.rot180, (Square.between_rot180 s t u).mp hu, ?_⟩
    simpa [rot180] using ho
  · intro ⟨u, hu, ho⟩
    refine ⟨u.rot180, ?_, ?_⟩
    · have : Between s.rot180 t.rot180 (u.rot180.rot180) := by
        rwa [Square.rot180_involutive]
      exact (Square.between_rot180 s t u.rot180).mpr this
    · simpa [rot180, Square.rot180_involutive] using ho

theorem geoAttacks_rot180 (p : Piece) (s t : Square) :
    (match p.kind with
      | .pawn => decide (PawnAttacks p.color s t)
      | .knight => decide (KnightAttacks s t)
      | .king => decide (KingAttacks s t)
      | .bishop => decide (BishopAttacks s t)
      | .rook => decide (RookAttacks s t)
      | .queen => decide (QueenAttacks s t)) =
    (match p.flip.kind with
      | .pawn => decide (PawnAttacks p.flip.color s.rot180 t.rot180)
      | .knight => decide (KnightAttacks s.rot180 t.rot180)
      | .king => decide (KingAttacks s.rot180 t.rot180)
      | .bishop => decide (BishopAttacks s.rot180 t.rot180)
      | .rook => decide (RookAttacks s.rot180 t.rot180)
      | .queen => decide (QueenAttacks s.rot180 t.rot180)) := by
  revert p s t
  native_decide

theorem attacks_rot180 (b : Board) (s t : Square) :
    b.attacks s t = b.rot180.attacks s.rot180 t.rot180 := by
  cases hp : b s with
  | none =>
    have : b.rot180 s.rot180 = none := by
      simp only [rot180, hp, Square.rot180_involutive, Option.map_none]
    simp [attacks, hp, this]
  | some p =>
    have hpR : b.rot180 s.rot180 = some p.flip := by
      simp only [rot180, hp, Square.rot180_involutive, Option.map_some]
    simp only [attacks, hp, hpR]
    apply congrArg₂ (· && ·)
    · exact geoAttacks_rot180 p s t
    · apply congrArg not
      apply congrArg₂ (· && ·)
      · simp [Piece.flip]
      · rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
        exact between_isSome_rot180 b s t

theorem mem_kingSquares_rot180 (b : Board) (c : Color) (s : Square) :
    s ∈ b.kingSquares c ↔ s.rot180 ∈ b.rot180.kingSquares c.other := by
  simp only [mem_kingSquares, rot180, Square.rot180_involutive]
  cases h : b s with
  | none => simp
  | some p =>
    rcases p with ⟨pc, pk⟩
    cases pc <;> cases c <;> cases pk <;> simp [Piece.flip]

theorem kingIsAttacked_rot180 (b : Board) (c : Color) :
    b.kingIsAttacked c = b.rot180.kingIsAttacked c.other := by
  rw [Bool.eq_iff_iff, kingIsAttacked_iff_mem_attackers,
    kingIsAttacked_iff_mem_attackers]
  constructor
  · intro ⟨t, ht, s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    refine ⟨t.rot180, (mem_kingSquares_rot180 b c t).mp ht, s.rot180, ?_⟩
    rw [mem_attackers]
    constructor
    · cases hb : b s with
      | none => simp [hb] at hcol
      | some p =>
        have hpc : p.color = c.other := by simpa [hb] using hcol
        simp [rot180, Square.rot180_involutive, hb, Piece.flip, hpc]
    · rw [← attacks_rot180, hatt]
  · intro ⟨t, ht, s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    refine ⟨t.rot180, ?_, s.rot180, ?_⟩
    · have ht' : t ∈ b.rot180.kingSquares c.other := ht
      have := (mem_kingSquares_rot180 b c t.rot180).mpr
      simpa [Square.rot180_involutive] using this (by
        simpa [Square.rot180_involutive] using ht')
    · rw [mem_attackers]
      constructor
      · cases hb : b s.rot180 with
        | none =>
          have : b.rot180 s = none := by simp [rot180, hb]
          simp [this] at hcol
        | some p =>
          have hlook : b.rot180 s = some p.flip := by simp [rot180, hb]
          have hpc : p.color.other = c := by simpa [hlook, Piece.flip] using hcol
          have hpc' : p.color = c.other := by
            rw [← Color.other_other p.color, hpc]
          simp [hpc']
      · have h := attacks_rot180 b s.rot180 t.rot180
        have : b.rot180.attacks s t = b.attacks s.rot180 t.rot180 := by
          simpa [Square.rot180_involutive] using h.symm
        rwa [this] at hatt

end Board

namespace Position

/-- 180° rotation of a position: pieces move with the board and swap
color, and the side to move is flipped. Castling rights and en passant
are cleared (they are already empty on these three-piece endings). -/
def rot180 (p : Position) : Position where
  board := p.board.rot180
  toMove := p.toMove.other
  castling := ∅
  enPassant := none

theorem rot180_board (p : Position) : p.rot180.board = p.board.rot180 := rfl

theorem rot180_toMove (p : Position) : p.rot180.toMove = p.toMove.other := rfl

theorem rot180_involutive {p : Position}
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    p.rot180.rot180 = p := by
  rcases p with ⟨b, tm, cst, ep⟩
  refine Position.ext ?_ ?_ ?_ ?_
  · simp [rot180, Board.board_rot180_involutive]
  · simp [rot180]
  · simpa [rot180] using hc.symm
  · simpa [rot180] using he.symm

theorem rot180_mk (b : Board) (tm : Color) (c : CastlingRights) (e : Option Square) :
    ({ board := b, toMove := tm, castling := c, enPassant := e } : Position).rot180 =
      { board := b.rot180, toMove := tm.other, castling := ∅, enPassant := none } :=
  rfl

end Position

namespace Move

/-- 180° rotation of a move. -/
def rot180 (m : Move) : Move :=
  ⟨m.src.rot180, m.dst.rot180, m.promotion⟩

@[simp] theorem rot180_src (m : Move) : m.rot180.src = m.src.rot180 := rfl

@[simp] theorem rot180_dst (m : Move) : m.rot180.dst = m.dst.rot180 := rfl

@[simp] theorem rot180_promotion (m : Move) : m.rot180.promotion = m.promotion := rfl

@[simp] theorem rot180_involutive (m : Move) : m.rot180.rot180 = m := by
  rcases m with ⟨s, d, pr⟩
  simp [rot180]

@[simp] theorem rot180_std (s t : Square) :
    (Move.std s t).rot180 = Move.std s.rot180 t.rot180 := rfl

end Move

namespace Position

theorem destOk_rot180 (p : Position) (m : Move) :
    p.destOk m = p.rot180.destOk m.rot180 := by
  simp only [destOk, Move.rot180_dst, rot180_board, rot180_toMove]
  cases h : p.board m.dst with
  | none => simp [Board.rot180, Square.rot180_involutive, h]
  | some q =>
    simp [Board.rot180, Square.rot180_involutive, h, Piece.flip]
    cases q.color <;> cases p.toMove <;> rfl

theorem inCheck_rot180 (p : Position) : p.inCheck = p.rot180.inCheck := by
  unfold inCheck rot180
  exact Board.kingIsAttacked_rot180 p.board p.toMove

theorem piece_of_kind_king (piece : Piece) (hk : piece.kind = .king) :
    piece = { color := piece.color, kind := .king } := by
  rcases piece with ⟨pc, pk⟩
  subst hk
  rfl

/-- If `a` is the unique element of `l` satisfying `p`, then `find?` returns it. -/
theorem find?_eq_some_of_unique {α} {p : α → Bool} {a : α} {l : List α}
    (hm : a ∈ l) (hp : p a = true) (hu : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => simp at hm
  | cons b l ih =>
    simp only [List.find?]
    split
    · next hb =>
      congr
      exact hu b (List.mem_cons_self ..) hb
    · next hb =>
      apply ih
      · simp only [List.mem_cons] at hm
        rcases hm with rfl | h
        · simp [hp] at hb
        · exact h
      · intro c hc hc'
        exact hu c (List.mem_cons_of_mem _ hc) hc'

end Position

end Chess
