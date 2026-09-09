import Chess.Position
import Chess.Valid
import Chess.PositionValid

/-!
# Check

A position is in check when the king of the player to move occupies a
square attacked by a piece of the opposite color (FIDE Laws of Chess,
Article 3.9.1). Occupied-board attacks (`Board.attacks`) respect blocking
pieces on sliding rays; pins on the attacking piece are ignored, matching
the Laws.
-/

namespace Chess

namespace Position

/-- Whether the player to move is in check. -/
def inCheck (p : Position) : Bool :=
  p.board.kingIsAttacked p.toMove

/-- The player to move is in check: their king occupies a square attacked
by at least one opposing piece. -/
def InCheck (p : Position) : Prop :=
  p.board.kingIsAttacked p.toMove = true

instance {p : Position} : Decidable (InCheck p) :=
  inferInstanceAs (Decidable (_ = true))

theorem inCheck_eq_true_iff (p : Position) :
    p.inCheck = true ↔ InCheck p :=
  Iff.rfl

/-- Check is exactly an attack on the king of the player to move. -/
theorem inCheck_iff_kingIsAttacked (p : Position) :
    p.inCheck = p.board.kingIsAttacked p.toMove :=
  rfl

/-- On a valid position, the opponent of the player to move is never in
check, so at most one side is in check. -/
theorem valid_opponent_not_attacked {p : Position} (h : Valid p) :
    p.board.kingIsAttacked p.toMove.other = false :=
  h.2.1

/-- The standard starting position is not in check. -/
theorem starting_not_inCheck : starting.inCheck = false :=
  Board.starting_kings_not_attacked .white

theorem starting_not_InCheck : ¬ InCheck starting := by
  simp [InCheck, starting_not_inCheck]

/-- Black to move, with a white rook attacking the black king: in check. -/
theorem currentPlayerInCheck_inCheck :
    currentPlayerInCheck.inCheck = true := by
  native_decide

/-- White to move on the same placement is not in check: White's king is
safe, even though Black's king is attacked. -/
theorem opponentInCheck_not_inCheck :
    opponentInCheck.inCheck = false := by
  native_decide

/-! ### Checks by each kind of piece -/

/-- A black knight on `c2` checks the white king on `e1`. -/
def knightCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c2 then some { color := .black, kind := .knight }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem knightCheck_inCheck : knightCheck.inCheck = true := by
  native_decide

/-- A black pawn on `d2` checks the white king on `e1`. -/
def pawnCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.d2 then some { color := .black, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem pawnCheck_inCheck : pawnCheck.inCheck = true := by
  native_decide

/-- A black bishop on `c3` checks the white king on `e1`. -/
def bishopCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c3 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem bishopCheck_inCheck : bishopCheck.inCheck = true := by
  native_decide

/-- A white queen on `e4` checks the black king on `e8`. -/
def queenCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e4 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenCheck_inCheck : queenCheck.inCheck = true := by
  native_decide

/-- Adjacent kings: White to move is in check from the black king. -/
def kingCheck : Position where
  board := Board.adjacentKings
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingCheck_inCheck : kingCheck.inCheck = true := by
  native_decide

/-- A black rook on `e8` does not check the white king on `e1` while a
pawn occupies `e2`. -/
def blockedRook : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .rook }
    else if s = Square.e2 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem blockedRook_not_inCheck : blockedRook.inCheck = false := by
  native_decide

/-- With the e-file vacant, that rook does check the white king. -/
def clearFileRook : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .rook }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem clearFileRook_inCheck : clearFileRook.inCheck = true := by
  native_decide

end Position

end Chess
