import Chess.Board
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Positions

A position is the information that identifies a chess position for the
purposes of repetition (FIDE Laws of Chess, Article 9.2): the placement of
pieces, the player to move, the remaining castling rights, and whether an
en passant capture is possible.

The half-move clock and full-move number are omitted: they are game-history
counters, not part of the position itself.
-/

namespace Chess

/-- The two directions in which a player may castle. -/
inductive CastlingSide where
  | kingside
  | queenside
deriving DecidableEq, Repr, Inhabited

namespace CastlingSide

instance : Fintype CastlingSide where
  elems := {kingside, queenside}
  complete s := by cases s <;> simp

/-- There are two castling sides. -/
theorem card : Fintype.card CastlingSide = 2 :=
  rfl

end CastlingSide

/-- A single remaining castling privilege: a player, and a side. -/
structure CastlingRight where
  /-- The player who may still castle. -/
  color : Color
  /-- The side on which that player may still castle. -/
  side : CastlingSide
deriving DecidableEq, Repr, Inhabited

namespace CastlingRight

/-- Forget the structure, viewing a castling right as a pair. -/
def equivProd : CastlingRight ≃ Color × CastlingSide where
  toFun r := (r.color, r.side)
  invFun q := ⟨q.1, q.2⟩
  left_inv := by
    intro r
    cases r
    rfl
  right_inv := by
    intro q
    cases q
    rfl

instance : Fintype CastlingRight :=
  Fintype.ofEquiv (Color × CastlingSide) equivProd.symm

/-- There are four distinct castling privileges. -/
theorem card : Fintype.card CastlingRight = 4 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod]
  simp [Color.card, CastlingSide.card]

/-- White's kingside castling privilege. -/
def whiteKingside : CastlingRight := ⟨.white, .kingside⟩

/-- White's queenside castling privilege. -/
def whiteQueenside : CastlingRight := ⟨.white, .queenside⟩

/-- Black's kingside castling privilege. -/
def blackKingside : CastlingRight := ⟨.black, .kingside⟩

/-- Black's queenside castling privilege. -/
def blackQueenside : CastlingRight := ⟨.black, .queenside⟩

end CastlingRight

/-- Remaining castling privileges of both players.

A privilege is present when the king and the corresponding rook have not
yet moved. Whether castling is legal on the current move (the king is not
in check, the squares it crosses are empty and not attacked, ...) is a
separate question. -/
abbrev CastlingRights := Finset CastlingRight

namespace CastlingRights

/-- Every castling privilege is still available. -/
def all : CastlingRights := Finset.univ

/-- No remaining castling privileges. -/
def empty : CastlingRights := ∅

/-- Whether `c` may still castle on `side`. -/
def allows (r : CastlingRights) (c : Color) (side : CastlingSide) : Bool :=
  decide ({ color := c, side := side } ∈ r)

@[simp] theorem all_allows (c : Color) (side : CastlingSide) :
    all.allows c side = true := by
  simp [all, allows]

@[simp] theorem empty_allows (c : Color) (side : CastlingSide) :
    empty.allows c side = false := by
  simp [empty, allows]

end CastlingRights

/-- A chess position: piece placement, side to move, remaining castling
rights, and the current possibility of an en passant capture. -/
@[ext]
structure Position where
  /-- Placement of pieces. Empty squares are `none`. -/
  board : Board
  /-- The player whose turn it is to move. -/
  toMove : Color
  /-- Remaining castling privileges of both players. -/
  castling : CastlingRights
  /-- Target square of a possible en passant capture, if any.

  This is the square a capturing pawn would occupy — the square passed
  over by a pawn that has just advanced two squares (FIDE 3.7.4.1). It is
  `none` when no such advance has just occurred. -/
  enPassant : Option Square
deriving Inhabited

namespace Position

/-- The standard starting position: the initial placement, White to move,
all four castling rights, and no en passant capture. -/
def starting : Position where
  board := Board.starting
  toMove := .white
  castling := CastlingRights.all
  enPassant := none

@[simp] theorem starting_board : starting.board = Board.starting := rfl
@[simp] theorem starting_toMove : starting.toMove = .white := rfl
@[simp] theorem starting_castling : starting.castling = CastlingRights.all := rfl
@[simp] theorem starting_enPassant : starting.enPassant = none := rfl

/-- All four castling privileges are available at the start. -/
theorem starting_castling_card : starting.castling.card = 4 := by
  rw [starting_castling, CastlingRights.all, Finset.card_univ, CastlingRight.card]

@[simp] theorem starting_allows (c : Color) (side : CastlingSide) :
    starting.castling.allows c side = true := by
  simp

/-- The same placement with Black to move is a different position. -/
theorem starting_ne_blackToMove :
    { starting with toMove := .black } ≠ starting := by
  intro h
  have := congrArg Position.toMove h
  simp at this

/-- Losing all castling rights yields a different position. -/
theorem starting_ne_emptyCastling :
    { starting with castling := CastlingRights.empty } ≠ starting := by
  intro h
  have := congrArg (fun p => CastlingRight.whiteKingside ∈ p.castling) h
  simp [CastlingRights.empty, CastlingRights.all] at this

/-- Recording an en passant target square yields a different position. -/
theorem starting_ne_enPassant :
    { starting with enPassant := some Square.e3 } ≠ starting := by
  intro h
  have := congrArg Position.enPassant h
  simp at this

end Position

end Chess
