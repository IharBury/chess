import Chess.Color
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic

/-!
# Squares of the chessboard

Files `a`–`h` and ranks `1`–`8` are encoded as `Fin 8`. The square `a1` is
`(file := 0, rank := 0)` and is a black (dark) square, matching standard
chessboard coloring.
-/

namespace Chess

/-- A file on the board, with `0` for the a-file and `7` for the h-file. -/
abbrev File := Fin 8

/-- A rank on the board, with `0` for rank 1 and `7` for rank 8. -/
abbrev Rank := Fin 8

/-- A square of the 8×8 chessboard. -/
@[ext]
structure Square where
  /-- File of the square, `0` = a through `7` = h. -/
  file : File
  /-- Rank of the square, `0` = 1 through `7` = 8. -/
  rank : Rank
deriving DecidableEq, Repr, Inhabited

namespace Square

/-- Forget the structure, viewing a square as a pair of coordinates. -/
def equivProd : Square ≃ File × Rank where
  toFun s := (s.file, s.rank)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro p
    cases p
    rfl

instance : Fintype Square :=
  Fintype.ofEquiv (File × Rank) equivProd.symm

/-- There are exactly 64 squares. -/
theorem card : Fintype.card Square = 64 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod]
  simp

/-- Horizontal displacement from `s` to `t`, in files. -/
def deltaFile (s t : Square) : ℤ := (t.file : ℤ) - (s.file : ℤ)

/-- Vertical displacement from `s` to `t`, in ranks. -/
def deltaRank (s t : Square) : ℤ := (t.rank : ℤ) - (s.rank : ℤ)

@[simp]
theorem deltaFile_self (s : Square) : deltaFile s s = 0 := by
  simp [deltaFile]

@[simp]
theorem deltaRank_self (s : Square) : deltaRank s s = 0 := by
  simp [deltaRank]

/-- Color of a square. `a1` is black, as in standard chess. -/
def color (s : Square) : Color :=
  if (s.file.val + s.rank.val) % 2 = 0 then .black else .white

theorem color_black_iff (s : Square) :
    s.color = .black ↔ (s.file.val + s.rank.val) % 2 = 0 := by
  unfold color
  split_ifs with h
  · simp [h]
  · simp [h]

theorem color_white_iff (s : Square) :
    s.color = .white ↔ (s.file.val + s.rank.val) % 2 = 1 := by
  have hmod : (s.file.val + s.rank.val) % 2 = 0 ∨ (s.file.val + s.rank.val) % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  unfold color
  split_ifs with h
  · simp [h]
  · cases hmod with
    | inl h0 => contradiction
    | inr h1 => simp [h1]

/-- Two squares have the same color iff the sums of their coordinates have
the same parity. -/
theorem color_eq_iff (s t : Square) :
    s.color = t.color ↔
      (s.file.val + s.rank.val) % 2 = (t.file.val + t.rank.val) % 2 := by
  unfold color
  have hs := Nat.mod_two_eq_zero_or_one (s.file.val + s.rank.val)
  have ht := Nat.mod_two_eq_zero_or_one (t.file.val + t.rank.val)
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> simp [hs, ht]

/-- Named squares used in theorems. -/
def a1 : Square := ⟨0, 0⟩
def c2 : Square := ⟨2, 1⟩
def d1 : Square := ⟨3, 0⟩
def d2 : Square := ⟨3, 1⟩
def d4 : Square := ⟨3, 3⟩
def e1 : Square := ⟨4, 0⟩
def e2 : Square := ⟨4, 1⟩
def e3 : Square := ⟨4, 2⟩
def e4 : Square := ⟨4, 3⟩
def e8 : Square := ⟨4, 7⟩
def h1 : Square := ⟨7, 0⟩
def b3 : Square := ⟨1, 2⟩
def a8 : Square := ⟨0, 7⟩
def h8 : Square := ⟨7, 7⟩

@[simp] theorem a1_color : a1.color = .black := by decide
@[simp] theorem h1_color : h1.color = .white := by decide
@[simp] theorem a8_color : a8.color = .white := by decide
@[simp] theorem h8_color : h8.color = .black := by decide

/-- Opposite corners of the board have the same color. -/
theorem a1_color_eq_h8 : a1.color = h8.color := by simp

end Square

end Chess
