import Chess.Position
import Chess.Valid
import Chess.PositionValid

/-!
# Check

A position is in check when the king of the player to move occupies a
square attacked by a piece of the opposite color (FIDE Laws of Chess,
Article 3.9.1). It is in double check when that king occupies a square
attacked by two or more opposing pieces. Occupied-board attacks
(`Board.attacks`) respect blocking pieces on sliding rays; pins on the
attacking piece are ignored, matching the Laws.
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

/-- Whether the player to move is in double check. -/
def inDoubleCheck (p : Position) : Bool :=
  p.board.kingIsDoubleAttacked p.toMove

/-- The player to move is in double check: their king occupies a square
attacked by two or more opposing pieces. -/
def InDoubleCheck (p : Position) : Prop :=
  p.board.kingIsDoubleAttacked p.toMove = true

instance {p : Position} : Decidable (InDoubleCheck p) :=
  inferInstanceAs (Decidable (_ = true))

theorem inDoubleCheck_eq_true_iff (p : Position) :
    p.inDoubleCheck = true ↔ InDoubleCheck p :=
  Iff.rfl

/-- Double check is exactly a double attack on the king of the player to
move. -/
theorem inDoubleCheck_iff_kingIsDoubleAttacked (p : Position) :
    p.inDoubleCheck = p.board.kingIsDoubleAttacked p.toMove :=
  rfl

/-- Double check is a special case of check. -/
theorem inDoubleCheck_implies_inCheck {p : Position}
    (h : p.inDoubleCheck = true) : p.inCheck = true := by
  unfold inCheck inDoubleCheck at *
  exact Board.kingIsDoubleAttacked_implies_kingIsAttacked p.board p.toMove h

/-- A position that is not in check is not in double check. -/
theorem not_inCheck_not_inDoubleCheck {p : Position}
    (h : p.inCheck = false) : p.inDoubleCheck = false := by
  by_contra h'
  simp only [Bool.not_eq_false] at h'
  have := inDoubleCheck_implies_inCheck h'
  exact Bool.false_ne_true (h.symm.trans this)

/-- On a valid position, the opponent of the player to move is never in
check, so at most one side is in check. -/
theorem valid_opponent_not_attacked {p : Position} (h : Valid p) :
    p.board.kingIsAttacked p.toMove.other = false :=
  h.2.1

/-- The standard starting position is not in check. -/
theorem starting_not_inCheck : starting.inCheck = false := by
  unfold inCheck
  exact Board.starting_kings_not_attacked .white

theorem starting_not_InCheck : ¬ InCheck starting :=
  mt (inCheck_eq_true_iff starting).mpr
    (Eq.trans_ne starting_not_inCheck Bool.false_ne_true)

/-- The standard starting position is not in double check. -/
theorem starting_not_inDoubleCheck : starting.inDoubleCheck = false :=
  not_inCheck_not_inDoubleCheck starting_not_inCheck

/-- Black to move, with a white rook attacking the black king: in check. -/
theorem currentPlayerInCheck_inCheck :
    currentPlayerInCheck.inCheck = true := by
  native_decide

/-- A single rook check is not a double check. -/
theorem currentPlayerInCheck_not_inDoubleCheck :
    currentPlayerInCheck.inDoubleCheck = false := by
  native_decide

/-- White to move on the same placement is not in check: White's king is
safe, even though Black's king is attacked. -/
theorem opponentInCheck_not_inCheck :
    opponentInCheck.inCheck = false := by
  native_decide

theorem opponentInCheck_not_inDoubleCheck :
    opponentInCheck.inDoubleCheck = false :=
  not_inCheck_not_inDoubleCheck opponentInCheck_not_inCheck

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

theorem knightCheck_not_inDoubleCheck : knightCheck.inDoubleCheck = false := by
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

/-! ### Double check -/

/-- A rook on the e-file and a knight on `f6` both check the black king
on `e8`. -/
def rookKnightDoubleCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e4 then some { color := .white, kind := .rook }
    else if s = Square.f6 then some { color := .white, kind := .knight }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookKnightDoubleCheck_inDoubleCheck :
    rookKnightDoubleCheck.inDoubleCheck = true := by
  native_decide

theorem rookKnightDoubleCheck_inCheck :
    rookKnightDoubleCheck.inCheck = true :=
  inDoubleCheck_implies_inCheck rookKnightDoubleCheck_inDoubleCheck

/-- The same placement with White to move is not a double check: White's
king is safe. -/
def rookKnightDoubleCheckWhiteToMove : Position :=
  { rookKnightDoubleCheck with toMove := .white }

theorem rookKnightDoubleCheckWhiteToMove_not_inDoubleCheck :
    rookKnightDoubleCheckWhiteToMove.inDoubleCheck = false :=
  not_inCheck_not_inDoubleCheck
    (by native_decide : rookKnightDoubleCheckWhiteToMove.inCheck = false)

/-- A rook on `e1` and a bishop on `a4` both check the black king on `e8`. -/
def rookBishopDoubleCheck : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e1 then some { color := .white, kind := .rook }
    else if s = Square.a4 then some { color := .white, kind := .bishop }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookBishopDoubleCheck_inDoubleCheck :
    rookBishopDoubleCheck.inDoubleCheck = true := by
  native_decide

/-- A pawn on `e7` blocks the rook, leaving only the bishop check. -/
def rookBishopBlocked : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e1 then some { color := .white, kind := .rook }
    else if s = Square.a4 then some { color := .white, kind := .bishop }
    else if s = Square.e7 then some { color := .black, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookBishopBlocked_inCheck : rookBishopBlocked.inCheck = true := by
  native_decide

theorem rookBishopBlocked_not_inDoubleCheck :
    rookBishopBlocked.inDoubleCheck = false := by
  native_decide

/-- Three pieces attack the black king: still double check (`≥ 2`
attackers). -/
def tripleCheck : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e4 then some { color := .white, kind := .rook }
    else if s = Square.f6 then some { color := .white, kind := .knight }
    else if s = Square.a4 then some { color := .white, kind := .bishop }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem tripleCheck_inDoubleCheck : tripleCheck.inDoubleCheck = true := by
  native_decide

end Position

end Chess
