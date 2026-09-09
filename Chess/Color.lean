import Mathlib.Data.Fintype.Card

/-!
# Player colors

White and black as a two-element type, together with the involution that
swaps them.
-/

namespace Chess

/-- The two player colors. Also used for the color of a square (`a1` is black). -/
inductive Color where
  | white
  | black
deriving DecidableEq, Repr, Inhabited

namespace Color

instance : Fintype Color where
  elems := {white, black}
  complete c := by cases c <;> simp

/-- The opposite color. -/
def other : Color → Color
  | white => black
  | black => white

@[simp]
theorem other_white : other white = black := rfl

@[simp]
theorem other_black : other black = white := rfl

/-- Taking the opposite color twice is the identity. -/
@[simp]
theorem other_other (c : Color) : c.other.other = c := by
  cases c <;> rfl

/-- No color is its own opposite. -/
theorem other_ne (c : Color) : c.other ≠ c := by
  cases c <;> decide

/-- `other` is injective. -/
theorem other_injective {a b : Color} (h : a.other = b.other) : a = b := by
  simpa using congrArg other h

/-- There are two colors. -/
theorem card : Fintype.card Color = 2 :=
  rfl

end Color

end Chess
