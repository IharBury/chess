import Chess.Square

/-!
# Attack geometry

Relations describing which squares a piece could reach on an empty board.
These ignore blocking pieces, pins, check, and (for pawns) capturing versus
forward moves. They are the geometric substrate on which a later account of
the laws of chess can be built.

The board is finite, so several classic facts are proved by exhaustive
decision of the 64×64 pairs of squares.
-/

namespace Chess

/-- Empty-board bishop attack: a nonempty diagonal step. -/
def BishopAttacks (s t : Square) : Prop :=
  s ≠ t ∧ (Square.deltaFile s t).natAbs = (Square.deltaRank s t).natAbs

/-- Empty-board rook attack: a nonempty orthogonal step. -/
def RookAttacks (s t : Square) : Prop :=
  s ≠ t ∧ (s.file = t.file ∨ s.rank = t.rank)

/-- Empty-board queen attack: bishop or rook geometry. -/
def QueenAttacks (s t : Square) : Prop :=
  BishopAttacks s t ∨ RookAttacks s t

/-- Empty-board king attack: a step by at most one file and one rank, not staying put. -/
def KingAttacks (s t : Square) : Prop :=
  s ≠ t ∧ (Square.deltaFile s t).natAbs ≤ 1 ∧ (Square.deltaRank s t).natAbs ≤ 1

/-- Empty-board knight attack: a 2-by-1 leap. -/
def KnightAttacks (s t : Square) : Prop :=
  let df := (Square.deltaFile s t).natAbs
  let dr := (Square.deltaRank s t).natAbs
  (df = 1 ∧ dr = 2) ∨ (df = 2 ∧ dr = 1)

/-- Empty-board pawn capture: one file sideways and one rank forward
(White advances toward the eighth rank, Black toward the first). -/
def PawnAttacks (c : Color) (s t : Square) : Prop :=
  (Square.deltaFile s t).natAbs = 1 ∧
    Square.deltaRank s t =
      match c with
      | .white => 1
      | .black => -1

/-- Rank a pawn of color `c` passes over in a two-square first move.
White jumps from rank 2 to rank 4 over rank 3; Black from rank 7 to
rank 5 over rank 6. -/
def pawnJumpOverRank (c : Color) : Rank :=
  match c with
  | .white => 2
  | .black => 5

/-- Rank a pawn of color `c` occupies after a two-square first move.
White lands on rank 4; Black on rank 5. -/
def pawnJumpToRank (c : Color) : Rank :=
  match c with
  | .white => 3
  | .black => 4

/-- Rank on which a pawn of color `c` stands before any move.
White's pawns start on rank 2; Black's on rank 7. -/
def pawnStartRank (c : Color) : Rank :=
  match c with
  | .white => 1
  | .black => 6

/-- Rank on which a pawn of color `c` promotes.
White promotes on rank 8; Black on rank 1. -/
def pawnPromotionRank (c : Color) : Rank :=
  match c with
  | .white => 7
  | .black => 0

/-- Rank change of a one-square pawn advance: White `+1`, Black `-1`. -/
def pawnPushDelta (c : Color) : ℤ :=
  match c with
  | .white => 1
  | .black => -1

/-- Landing square of a two-square pawn advance that passed over `over`.
The file is that of `over`; the rank is `pawnJumpToRank c`. -/
def pawnJumpLanding (c : Color) (over : Square) : Square :=
  ⟨over.file, pawnJumpToRank c⟩

/-- Square `u` lies strictly between `s` and `t` on a bishop or rook ray. -/
def Between (s t u : Square) : Prop :=
  s ≠ u ∧ u ≠ t ∧
    (Square.deltaFile s u).natAbs + (Square.deltaFile u t).natAbs =
      (Square.deltaFile s t).natAbs ∧
    (Square.deltaRank s u).natAbs + (Square.deltaRank u t).natAbs =
      (Square.deltaRank s t).natAbs ∧
    ((RookAttacks s t ∧ RookAttacks s u) ∨
      (BishopAttacks s t ∧ BishopAttacks s u))

instance {s t : Square} : Decidable (BishopAttacks s t) := by
  unfold BishopAttacks
  infer_instance

instance {s t : Square} : Decidable (RookAttacks s t) := by
  unfold RookAttacks
  infer_instance

instance {s t : Square} : Decidable (QueenAttacks s t) := by
  unfold QueenAttacks
  infer_instance

instance {s t : Square} : Decidable (KingAttacks s t) := by
  unfold KingAttacks
  infer_instance

instance {s t : Square} : Decidable (KnightAttacks s t) := by
  unfold KnightAttacks
  infer_instance

instance {c : Color} {s t : Square} : Decidable (PawnAttacks c s t) := by
  unfold PawnAttacks
  infer_instance

instance {s t u : Square} : Decidable (Between s t u) := by
  unfold Between
  infer_instance

/-- Bishops stay on squares of one color. -/
theorem bishopAttacks_same_color {s t : Square} (h : BishopAttacks s t) :
    s.color = t.color := by
  revert s t
  native_decide

/-- Knights always move to a square of the opposite color. -/
theorem knightAttacks_other_color {s t : Square} (h : KnightAttacks s t) :
    t.color = s.color.other := by
  revert s t
  native_decide

/-- A knight on `a1` attacks `b3` and `c2`, and nothing else. -/
theorem knightAttacks_a1 :
    KnightAttacks Square.a1 Square.b3 ∧
      KnightAttacks Square.a1 Square.c2 ∧
      ∀ t, KnightAttacks Square.a1 t → t = Square.b3 ∨ t = Square.c2 := by
  native_decide

/-- A rook on `a1` attacks along the a-file and the first rank. -/
theorem rookAttacks_a1_h1 : RookAttacks Square.a1 Square.h1 := by
  decide

theorem rookAttacks_a1_a8 : RookAttacks Square.a1 Square.a8 := by
  decide

/-- Queens combine bishop and rook geometry: `a1` attacks `h8` and `a8`. -/
theorem queenAttacks_a1_h8 : QueenAttacks Square.a1 Square.h8 := by
  decide

theorem queenAttacks_a1_a8 : QueenAttacks Square.a1 Square.a8 := by
  decide

/-- Kings attack only neighboring squares: `e1` attacks `d1`, `d2`, `e2`, `f1`, `f2`. -/
theorem kingAttacks_e1_d2 : KingAttacks Square.e1 Square.d2 := by
  decide

theorem not_kingAttacks_e1_e8 : ¬ KingAttacks Square.e1 Square.e8 := by
  decide

/-- King attack is symmetric: adjacent kings attack each other. -/
theorem kingAttacks_symmetric {s t : Square} :
    KingAttacks s t ↔ KingAttacks t s := by
  revert s t
  native_decide

/-- White pawns capture one rank up; they do not capture backward or straight. -/
theorem pawnAttacks_white_d2_e3 : PawnAttacks .white Square.d2 Square.e3 := by
  decide

theorem not_pawnAttacks_white_d2_d4 : ¬ PawnAttacks .white Square.d2 Square.d4 := by
  decide

@[simp] theorem pawnJumpOverRank_white : pawnJumpOverRank .white = 2 := rfl
@[simp] theorem pawnJumpOverRank_black : pawnJumpOverRank .black = 5 := rfl
@[simp] theorem pawnJumpToRank_white : pawnJumpToRank .white = 3 := rfl
@[simp] theorem pawnJumpToRank_black : pawnJumpToRank .black = 4 := rfl
@[simp] theorem pawnStartRank_white : pawnStartRank .white = 1 := rfl
@[simp] theorem pawnStartRank_black : pawnStartRank .black = 6 := rfl
@[simp] theorem pawnPromotionRank_white : pawnPromotionRank .white = 7 := rfl
@[simp] theorem pawnPromotionRank_black : pawnPromotionRank .black = 0 := rfl
@[simp] theorem pawnPushDelta_white : pawnPushDelta .white = 1 := rfl
@[simp] theorem pawnPushDelta_black : pawnPushDelta .black = -1 := rfl

/-- White's double-step passes over rank 3 and lands on rank 4 of the same file. -/
theorem pawnJumpLanding_white_e3 :
    pawnJumpLanding .white Square.e3 = Square.e4 := rfl

/-- Black's double-step passes over rank 6 and lands on rank 5 of the same file. -/
theorem pawnJumpLanding_black_e6 :
    pawnJumpLanding .black Square.e6 = Square.e5 := rfl

/-- Squares strictly between `a1` and `a8` lie on the a-file. -/
theorem between_a1_a8 :
    Between Square.a1 Square.a8 ⟨0, 3⟩ ∧
      ¬ Between Square.a1 Square.a8 Square.h1 := by
  decide

/-- Bishop attack is symmetric. -/
theorem bishopAttacks_symmetric {s t : Square} :
    BishopAttacks s t ↔ BishopAttacks t s := by
  revert s t
  native_decide

/-- A bishop does not attack a square of the opposite color. -/
theorem not_bishopAttacks_of_color_ne {s t : Square}
    (h : s.color ≠ t.color) : ¬ BishopAttacks s t :=
  mt bishopAttacks_same_color h

/-- Orthogonal adjacency: one file or one rank away, not both. -/
def OrthogonalAdjacent (s t : Square) : Prop :=
  (s.file = t.file ∧ (Square.deltaRank s t).natAbs = 1) ∨
    (s.rank = t.rank ∧ (Square.deltaFile s t).natAbs = 1)

instance {s t : Square} : Decidable (OrthogonalAdjacent s t) := by
  unfold OrthogonalAdjacent
  infer_instance

/-- An orthogonal neighbor is a king-move. -/
theorem orthoAdj_kingAttacks {s t : Square} (h : OrthogonalAdjacent s t) :
    KingAttacks s t := by
  revert s t
  native_decide

/-- Orthogonal neighbors have opposite square-colors. -/
theorem orthoAdj_color {s t : Square} (h : OrthogonalAdjacent s t) :
    t.color = s.color.other := by
  revert s t
  native_decide

/-- A bishop that checks a square cannot attack an orthogonal neighbor of
that square: those neighbors have the opposite color. -/
theorem orthoAdj_not_bishopAttacks {k t b : Square}
    (ho : OrthogonalAdjacent k t) (hatt : BishopAttacks b k) :
    ¬ BishopAttacks b t := by
  intro hbt
  have hbk : b.color = k.color := bishopAttacks_same_color hatt
  have hbt' : b.color = t.color := bishopAttacks_same_color hbt
  have ht : t.color = k.color.other := orthoAdj_color ho
  rw [hbk, ht] at hbt'
  exact Color.other_ne k.color hbt'.symm

/-- Orthogonal adjacency is irreflexive. -/
theorem orthoAdj_ne {s t : Square} (h : OrthogonalAdjacent s t) : s ≠ t := by
  intro heq
  subst heq
  cases h with
  | inl hfr =>
    have : (Square.deltaRank s s).natAbs = 1 := hfr.2
    simp at this
  | inr hrf =>
    have : (Square.deltaFile s s).natAbs = 1 := hrf.2
    simp at this

/-- Orthogonal adjacency is symmetric. -/
theorem orthoAdj_symmetric {s t : Square} :
    OrthogonalAdjacent s t ↔ OrthogonalAdjacent t s := by
  revert s t
  native_decide

/-- Knight attack is symmetric. -/
theorem knightAttacks_symmetric {s t : Square} :
    KnightAttacks s t ↔ KnightAttacks t s := by
  revert s t
  native_decide

/-- A knight does not attack an orthogonal neighbor. -/
theorem not_knightAttacks_of_orthoAdj {s t : Square}
    (h : OrthogonalAdjacent s t) : ¬ KnightAttacks s t := by
  revert s t
  native_decide

/-- A knight that checks a square cannot attack an orthogonal neighbor of
that square: those neighbors have the same color as the knight. -/
theorem orthoAdj_not_knightAttacks {k t n : Square}
    (ho : OrthogonalAdjacent k t) (hatt : KnightAttacks n k) :
    ¬ KnightAttacks n t := by
  intro hnt
  have hk : k.color = n.color.other := knightAttacks_other_color hatt
  have ht : t.color = n.color.other := knightAttacks_other_color hnt
  have hto : t.color = k.color.other := orthoAdj_color ho
  rw [hk, Color.other_other] at hto
  exact Color.other_ne n.color (ht.symm.trans hto)

/-- The one-file neighbor of `s`: toward the h-file, or toward `g` on the
h-file. Every square has such a neighbor. -/
def horizNeighbor (s : Square) : Square :=
  if h : s.file.val < 7 then
    ⟨⟨s.file.val + 1, by omega⟩, s.rank⟩
  else
    ⟨⟨s.file.val - 1, by omega⟩, s.rank⟩

/-- The one-rank neighbor of `s`: toward the eighth rank, or toward the
seventh rank on the eighth. Every square has such a neighbor. -/
def vertNeighbor (s : Square) : Square :=
  if h : s.rank.val < 7 then
    ⟨s.file, ⟨s.rank.val + 1, by omega⟩⟩
  else
    ⟨s.file, ⟨s.rank.val - 1, by omega⟩⟩

theorem horizNeighbor_ortho (s : Square) :
    OrthogonalAdjacent s (horizNeighbor s) := by
  revert s
  native_decide

theorem vertNeighbor_ortho (s : Square) :
    OrthogonalAdjacent s (vertNeighbor s) := by
  revert s
  native_decide

theorem horizNeighbor_ne_vertNeighbor (s : Square) :
    horizNeighbor s ≠ vertNeighbor s := by
  revert s
  native_decide

/-- A king-step onto an orthogonal neighbor of `k` that is not attacked
by the king on `w`. Prefer the horizontal neighbor; if that is attacked,
use the vertical neighbor. -/
def kingOrthoEscape (k w : Square) : Square :=
  if KingAttacks w (horizNeighbor k) then vertNeighbor k else horizNeighbor k

theorem kingOrthoEscape_ortho (k w : Square) :
    OrthogonalAdjacent k (kingOrthoEscape k w) := by
  revert k w
  native_decide

/-- If the other king is not adjacent, it cannot cover both the
horizontal and the vertical neighbor of `k`. -/
theorem kingOrthoEscape_not_kingAttacks (k w : Square) :
    w ≠ k → ¬ KingAttacks w k → ¬ KingAttacks w (kingOrthoEscape k w) := by
  revert k w
  native_decide

theorem kingOrthoEscape_ne_self (k w : Square) :
    kingOrthoEscape k w ≠ k :=
  (orthoAdj_ne (kingOrthoEscape_ortho k w)).symm

theorem kingOrthoEscape_ne_other (k w : Square) :
    ¬ KingAttacks w k → kingOrthoEscape k w ≠ w := by
  intro hna heq
  have : KingAttacks k w := by
    rw [← heq]
    exact orthoAdj_kingAttacks (kingOrthoEscape_ortho k w)
  exact hna (kingAttacks_symmetric.mp this)

end Chess
