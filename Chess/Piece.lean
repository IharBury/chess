import Chess.Color
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Pieces

Piece kinds and colored pieces. A `Piece` is a kind together with the color
of the player that owns it.
-/

namespace Chess

/-- The six kinds of chess piece. -/
inductive PieceKind where
  | pawn
  | knight
  | bishop
  | rook
  | queen
  | king
deriving DecidableEq, Repr, Inhabited

namespace PieceKind

instance : Fintype PieceKind where
  elems := {pawn, knight, bishop, rook, queen, king}
  complete k := by cases k <;> simp

/-- There are six kinds of piece. -/
theorem card : Fintype.card PieceKind = 6 :=
  rfl

/-- Whether this kind moves any number of squares along a ray. -/
def isSlider : PieceKind → Bool
  | bishop | rook | queen => true
  | pawn | knight | king => false

@[simp] theorem bishop_isSlider : isSlider bishop = true := rfl
@[simp] theorem rook_isSlider : isSlider rook = true := rfl
@[simp] theorem queen_isSlider : isSlider queen = true := rfl
@[simp] theorem knight_isSlider : isSlider knight = false := rfl

end PieceKind

/-- A piece of a given kind belonging to a given player. -/
structure Piece where
  /-- Owner of the piece. -/
  color : Color
  /-- Kind of the piece. -/
  kind : PieceKind
deriving DecidableEq, Repr, Inhabited

namespace Piece

/-- View a colored piece as a pair of color and kind. -/
def equivProd : Piece ≃ Color × PieceKind where
  toFun p := (p.color, p.kind)
  invFun q := ⟨q.1, q.2⟩
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro q
    cases q
    rfl

instance : Fintype Piece :=
  Fintype.ofEquiv (Color × PieceKind) equivProd.symm

/-- There are twelve distinct colored pieces (six kinds for each color). -/
theorem card : Fintype.card Piece = 12 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod]
  simp [Color.card, PieceKind.card]

end Piece

end Chess
