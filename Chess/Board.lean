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

instance : Inhabited Board :=
  ⟨fun _ => none⟩

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
@[simp] theorem starting_a8 : starting Square.a8 = some { color := .black, kind := .rook } := rfl
@[simp] theorem starting_h8 : starting Square.h8 = some { color := .black, kind := .rook } := rfl
@[simp] theorem starting_d1 : starting Square.d1 = some { color := .white, kind := .queen } := rfl
@[simp] theorem starting_d4 : starting Square.d4 = none := rfl

/-- Squares occupied by at least one piece. -/
def occupied (b : Board) : Finset Square :=
  Finset.univ.filter fun s => (b s).isSome

/-- Occupied squares of a given color. -/
def occupiedBy (b : Board) (c : Color) : Finset Square :=
  Finset.univ.filter fun s => (b s).map (·.color) = some c

/-- Squares occupied by a king of the given color. -/
def kingSquares (b : Board) (c : Color) : Finset Square :=
  Finset.univ.filter fun s =>
    (b s).map (fun p => (p.color, p.kind)) = some (c, .king)

theorem mem_occupied (b : Board) (s : Square) :
    s ∈ b.occupied ↔ (b s).isSome = true := by
  simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_occupiedBy (b : Board) (c : Color) (s : Square) :
    s ∈ b.occupiedBy c ↔ (b s).map (·.color) = some c := by
  simp only [occupiedBy, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_kingSquares (b : Board) (c : Color) (s : Square) :
    s ∈ b.kingSquares c ↔ b s = some { color := c, kind := .king } := by
  unfold kingSquares
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : b s with
  | none => simp
  | some p =>
    rcases p with ⟨pc, pk⟩
    simp

theorem kingSquares_subset_occupiedBy (b : Board) (c : Color) :
    b.kingSquares c ⊆ b.occupiedBy c := by
  intro s hs
  rw [mem_kingSquares] at hs
  simp only [mem_occupiedBy, hs, Option.map_some]

theorem occupiedBy_disjoint (b : Board) :
    Disjoint (b.occupiedBy .white) (b.occupiedBy .black) := by
  rw [Finset.disjoint_left]
  intro s hsW hsB
  simp only [mem_occupiedBy] at hsW hsB
  cases h : b s with
  | none =>
    rw [h] at hsW
    simp at hsW
  | some p =>
    rw [h] at hsW hsB
    simp only [Option.map_some, Option.some.injEq] at hsW hsB
    cases hsW.symm.trans hsB

theorem occupied_eq_union (b : Board) :
    b.occupied = b.occupiedBy .white ∪ b.occupiedBy .black := by
  ext s
  simp only [mem_occupied, Finset.mem_union, mem_occupiedBy]
  cases h : b s with
  | none => simp
  | some p =>
    cases hp : p.color <;> simp [hp]

theorem occupied_card_eq_sum (b : Board) :
    b.occupied.card =
      (b.occupiedBy .white).card + (b.occupiedBy .black).card := by
  rw [occupied_eq_union, Finset.card_union_of_disjoint (occupiedBy_disjoint b)]

/-- Place `p` on `s`, replacing whatever stood there. -/
def place (b : Board) (s : Square) (p : Piece) : Board :=
  fun x => if x = s then some p else b x

/-- Vacate `s`. -/
def clear (b : Board) (s : Square) : Board :=
  fun x => if x = s then none else b x

/-- Move the piece `p` from `src` to `dst`, leaving `src` empty. -/
def relocate (b : Board) (src dst : Square) (p : Piece) : Board :=
  fun x =>
    if x = dst then some p
    else if x = src then none
    else b x

/-- A board places at most one piece on each square: the value at a
square is a single optional piece. -/
theorem at_most_one_piece_per_square (b : Board) (s : Square) {p q : Piece}
    (hp : b s = some p) (hq : b s = some q) : p = q :=
  Option.some.inj (hp.symm.trans hq)

/-- The starting position has 32 pieces. -/
theorem starting_occupied_card : starting.occupied.card = 32 := by
  native_decide

/-- Each side starts with 16 pieces. -/
theorem starting_occupiedBy_card (c : Color) : (starting.occupiedBy c).card = 16 := by
  cases c <;> native_decide

/-- The starting position has a unique white king, on `e1`. -/
theorem starting_kingSquares_white : starting.kingSquares .white = {Square.e1} := by
  native_decide

/-- The starting position has a unique black king, on `e8`. -/
theorem starting_kingSquares_black : starting.kingSquares .black = {Square.e8} := by
  native_decide

/-- Each side starts with exactly one king. -/
theorem starting_kingSquares_card (c : Color) : (starting.kingSquares c).card = 1 := by
  cases c with
  | .white => simp [starting_kingSquares_white]
  | .black => simp [starting_kingSquares_black]

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
