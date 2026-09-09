/-
Copyright (c) 2026 Ihar Bury.
Released under the Unlicense; see LICENSE.
Authors: Ihar Bury
-/
import Chess.Piece
import Chess.Square
import Mathlib.Data.Fintype.BigOperators

/-!
# Boards

A board is an assignment of at most one piece to each square. The standard
starting position is defined here, together with a few immediate facts
about it.
-/

namespace Chess

/-- A placement of pieces on the board. Empty squares are `none`. -/
def Board := Square → Option Piece

namespace Board

/-- The standard starting position. -/
def starting : Board := fun s =>
  match s.rank.val, s.file.val with
  | 1, _ => some { color := .white, kind := .pawn }
  | 6, _ => some { color := .black, kind := .pawn }
  | 0, 0 | 0, 7 => some { color := .white, kind := .rook }
  | 0, 1 | 0, 6 => some { color := .white, kind := .knight }
  | 0, 2 | 0, 5 => some { color := .white, kind := .bishop }
  | 0, 3 => some { color := .white, kind := .queen }
  | 0, 4 => some { color := .white, kind := .king }
  | 7, 0 | 7, 7 => some { color := .black, kind := .rook }
  | 7, 1 | 7, 6 => some { color := .black, kind := .knight }
  | 7, 2 | 7, 5 => some { color := .black, kind := .bishop }
  | 7, 3 => some { color := .black, kind := .queen }
  | 7, 4 => some { color := .black, kind := .king }
  | _, _ => none

@[simp] theorem starting_e1 : starting Square.e1 = some { color := .white, kind := .king } := rfl
@[simp] theorem starting_e8 : starting Square.e8 = some { color := .black, kind := .king } := rfl
@[simp] theorem starting_a1 : starting Square.a1 = some { color := .white, kind := .rook } := rfl
@[simp] theorem starting_h1 : starting Square.h1 = some { color := .white, kind := .rook } := rfl
@[simp] theorem starting_d1 : starting Square.d1 = some { color := .white, kind := .queen } := rfl
@[simp] theorem starting_d4 : starting Square.d4 = none := rfl

/-- Squares occupied by at least one piece. -/
def occupied (b : Board) : Finset Square :=
  Finset.univ.filter fun s => (b s).isSome

/-- Occupied squares of a given color. -/
def occupiedBy (b : Board) (c : Color) : Finset Square :=
  Finset.univ.filter fun s => (b s).map (·.color) = some c

/-- The starting position has 32 pieces. -/
theorem starting_occupied_card : starting.occupied.card = 32 := by
  native_decide

/-- Each side starts with 16 pieces. -/
theorem starting_occupiedBy_card (c : Color) : (starting.occupiedBy c).card = 16 := by
  cases c <;> native_decide

/-- Whether the starting position has a white king on this square. -/
def startingIsWhiteKing (s : Square) : Bool :=
  match starting s with
  | some p => (p.color == .white) && (p.kind == .king)
  | none => false

/-- Whether the starting position has a black king on this square. -/
def startingIsBlackKing (s : Square) : Bool :=
  match starting s with
  | some p => (p.color == .black) && (p.kind == .king)
  | none => false

/-- The starting position has a unique white king, on `e1`. -/
theorem starting_white_king_unique (s : Square)
    (h : starting s = some { color := .white, kind := .king }) : s = Square.e1 := by
  have hb : startingIsWhiteKing s = true := by
    unfold startingIsWhiteKing
    rw [h]
    rfl
  have hset :
      Finset.univ.filter (fun t => startingIsWhiteKing t = true) = {Square.e1} := by
    native_decide
  have : s ∈ ({Square.e1} : Finset Square) := by
    have : s ∈ Finset.univ.filter (fun t => startingIsWhiteKing t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

/-- The starting position has a unique black king, on `e8`. -/
theorem starting_black_king_unique (s : Square)
    (h : starting s = some { color := .black, kind := .king }) : s = Square.e8 := by
  have hb : startingIsBlackKing s = true := by
    unfold startingIsBlackKing
    rw [h]
    rfl
  have hset :
      Finset.univ.filter (fun t => startingIsBlackKing t = true) = {Square.e8} := by
    native_decide
  have : s ∈ ({Square.e8} : Finset Square) := by
    have : s ∈ Finset.univ.filter (fun t => startingIsBlackKing t = true) := by
      simp [hb]
    rwa [hset] at this
  simpa using this

end Board

end Chess
