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

end Chess
