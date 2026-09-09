import Chess.Position
import Chess.Valid
import Chess.Geometry
import Mathlib.Data.Fintype.Basic

/-!
# Valid positions

A position is valid when the placement is a valid board, the king of
the player who is not to move is not under attack, every remaining
castling privilege has its king and rook on their starting squares, and
an en passant target (if any) is consistent with a two-square pawn
advance that the current player can capture.
-/

namespace Chess

namespace Position

/-- Whether every remaining castling privilege has the king and the
corresponding rook on their starting squares. -/
def castlingOk (p : Position) : Bool :=
  decide (∀ r ∈ p.castling,
    p.board r.kingSquare = some { color := r.color, kind := .king } ∧
      p.board r.rookSquare = some { color := r.color, kind := .rook })

/-- Whether square `s` holds a pawn of color `c`. -/
def hasPawn (b : Board) (c : Color) (s : Square) : Bool :=
  match b s with
  | some q => (q.color == c) && (q.kind == .pawn)
  | none => false

/-- Whether a pawn of color `c` occupies `s` and attacks `t`. -/
def pawnAttacksFrom (b : Board) (c : Color) (s t : Square) : Bool :=
  hasPawn b c s && decide (PawnAttacks c s t)

/-- Whether some pawn of color `c` attacks `t`. -/
def existsPawnAttacking (b : Board) (c : Color) (t : Square) : Bool :=
  decide (∃ s : Square, pawnAttacksFrom b c s t = true)

theorem hasPawn_eq_true_iff (b : Board) (c : Color) (s : Square) :
    hasPawn b c s = true ↔ b s = some { color := c, kind := .pawn } := by
  unfold hasPawn
  cases h : b s with
  | none => simp
  | some q =>
    cases q
    simp

theorem existsPawnAttacking_iff (b : Board) (c : Color) (t : Square) :
    existsPawnAttacking b c t = true ↔
      ∃ s : Square, hasPawn b c s = true ∧ PawnAttacks c s t := by
  simp [existsPawnAttacking, pawnAttacksFrom, Bool.and_eq_true, decide_eq_true_eq]

/-- Consistency of the en passant field with a two-square advance.

`none` is always consistent. A target square `ep` is consistent when it
is the square a pawn of the opponent could pass over, that pawn occupies
the landing square of the jump, and a pawn of the player to move
attacks `ep`. -/
def enPassantOk (p : Position) : Bool :=
  match p.enPassant with
  | none => true
  | some ep =>
    (ep.rank == pawnJumpOverRank p.toMove.other) &&
    hasPawn p.board p.toMove.other (pawnJumpLanding p.toMove.other ep) &&
    existsPawnAttacking p.board p.toMove ep

/-- Whether `p` is a valid position.

* the placement is a valid board
* the king of the opponent of the player to move is not under attack
* for each castling right, the king and rook stand on their starting squares
* if there is an en passant target, it is a square a pawn of the opponent
  could jump over, that pawn occupies the landing square of the jump, and
  a pawn of the player to move can capture on the target square -/
def isValid (p : Position) : Bool :=
  p.board.isValid &&
  !p.board.kingIsAttacked p.toMove.other &&
  p.castlingOk &&
  p.enPassantOk

/-- A position that satisfies the structural constraints of a legal
chess snapshot. -/
def Valid (p : Position) : Prop :=
  Board.Valid p.board ∧
  p.board.kingIsAttacked p.toMove.other = false ∧
  (∀ r ∈ p.castling,
    p.board r.kingSquare = some { color := r.color, kind := .king } ∧
      p.board r.rookSquare = some { color := r.color, kind := .rook }) ∧
  p.enPassantOk = true

theorem castlingOk_iff (p : Position) :
    p.castlingOk = true ↔
      ∀ r ∈ p.castling,
        p.board r.kingSquare = some { color := r.color, kind := .king } ∧
          p.board r.rookSquare = some { color := r.color, kind := .rook } := by
  simp [castlingOk]

theorem enPassantOk_none (p : Position) (h : p.enPassant = none) :
    p.enPassantOk = true := by
  simp [enPassantOk, h]

theorem enPassantOk_some (p : Position) (ep : Square) (h : p.enPassant = some ep) :
    p.enPassantOk = true ↔
      ep.rank = pawnJumpOverRank p.toMove.other ∧
        hasPawn p.board p.toMove.other (pawnJumpLanding p.toMove.other ep) = true ∧
        existsPawnAttacking p.board p.toMove ep = true := by
  simp [enPassantOk, h, Bool.and_eq_true, and_assoc]

instance {p : Position} : Decidable (Valid p) := by
  unfold Valid
  infer_instance

theorem isValid_eq_true_iff (p : Position) : isValid p = true ↔ Valid p := by
  constructor
  · intro h
    simp only [isValid, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hb, hchk⟩, hc⟩, hep⟩ := h
    exact ⟨(Board.isValid_eq_true_iff p.board).mp hb, hchk,
      (castlingOk_iff p).mp hc, hep⟩
  · intro ⟨hb, hchk, hc, hep⟩
    simp only [isValid, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨⟨(Board.isValid_eq_true_iff p.board).mpr hb, hchk⟩,
      (castlingOk_iff p).mpr hc⟩, hep⟩

/-- The en passant field of a valid position is either empty or a square
a pawn of the opponent just jumped over, with that pawn on the landing
square and a capturing pawn of the player to move. -/
theorem valid_enPassant (p : Position) (h : Valid p) :
    match p.enPassant with
    | none => True
    | some ep =>
      ep.rank = pawnJumpOverRank p.toMove.other ∧
        p.board (pawnJumpLanding p.toMove.other ep) =
          some { color := p.toMove.other, kind := .pawn } ∧
        ∃ s : Square,
          p.board s = some { color := p.toMove, kind := .pawn } ∧
            PawnAttacks p.toMove s ep := by
  cases hep : p.enPassant with
  | none => trivial
  | some ep =>
    obtain ⟨hrank, hpawn, hcap⟩ := (enPassantOk_some p ep hep).mp h.2.2.2
    refine ⟨hrank, (hasPawn_eq_true_iff _ _ _).mp hpawn, ?_⟩
    obtain ⟨s, hs⟩ := (existsPawnAttacking_iff _ _ _).mp hcap
    exact ⟨s, (hasPawn_eq_true_iff _ _ _).mp hs.1, hs.2⟩

/-- The opponent of the player to move is not in check at the start. -/
theorem starting_opponent_not_attacked :
    starting.board.kingIsAttacked starting.toMove.other = false :=
  Board.starting_kings_not_attacked .black

/-- All four starting castling privileges have king and rook at home. -/
theorem starting_castlingOk : starting.castlingOk = true := by
  native_decide

@[simp] theorem starting_enPassantOk : starting.enPassantOk = true :=
  rfl

/-- The standard starting position is valid. -/
theorem starting_valid : Valid starting :=
  ⟨Board.starting_valid,
    starting_opponent_not_attacked,
    (castlingOk_iff starting).mp starting_castlingOk,
    starting_enPassantOk⟩

theorem starting_isValid : isValid starting = true :=
  (isValid_eq_true_iff starting).mpr starting_valid

/-- The current player may be in check: Black to move, Black's king
attacked, White's king safe. This is still a valid position. -/
def currentPlayerInCheck : Position where
  board := Board.blackInCheck
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem currentPlayerInCheck_isValid : isValid currentPlayerInCheck = true := by
  native_decide

/-! ### Invalid examples -/

/-- An invalid board cannot be a valid position. -/
def invalidBoard : Position where
  board := Board.empty
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem invalidBoard_not_valid : isValid invalidBoard = false := by
  native_decide

/-- White to move while Black's king is in check: the opponent is under
attack. -/
def opponentInCheck : Position where
  board := Board.blackInCheck
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem opponentInCheck_not_valid : isValid opponentInCheck = false := by
  native_decide

/-- Queenside castling is claimed, but the a-file rook is missing. -/
def missingQueensideRook : Position where
  board := fun s => if s = Square.a1 then none else Board.starting s
  toMove := .white
  castling := {CastlingRight.whiteQueenside}
  enPassant := none

theorem missingQueensideRook_not_valid : isValid missingQueensideRook = false := by
  native_decide

/-- Kingside castling is claimed, but the king has left `e1`. -/
def kingOffHome : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .queen }
    else if s = Square.d1 then some { color := .white, kind := .king }
    else Board.starting s
  toMove := .white
  castling := {CastlingRight.whiteKingside}
  enPassant := none

theorem kingOffHome_not_valid : isValid kingOffHome = false := by
  native_decide

/-- A kingside-only right is valid when the king and h-file rook are home,
even if the queenside rook has been captured. -/
def kingsideOnly : Position where
  board := fun s => if s = Square.a1 then none else Board.starting s
  toMove := .white
  castling := {CastlingRight.whiteKingside, CastlingRight.blackKingside,
    CastlingRight.blackQueenside}
  enPassant := none

theorem kingsideOnly_isValid : isValid kingsideOnly = true := by
  native_decide

/-- Kings, a black pawn that has just jumped to `e5`, and a white pawn
that can capture en passant on `e6`. -/
def enPassantBoard : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else if s = Square.e5 then some { color := .black, kind := .pawn }
  else if s = Square.d5 then some { color := .white, kind := .pawn }
  else none

/-- A legal en passant capture for White on `e6`. -/
def withEnPassant : Position where
  board := enPassantBoard
  toMove := .white
  castling := CastlingRights.empty
  enPassant := some Square.e6

theorem withEnPassant_isValid : isValid withEnPassant = true := by
  native_decide

/-- En passant recorded on a square a black pawn could not have jumped
over. -/
def enPassantWrongRank : Position :=
  { withEnPassant with enPassant := some Square.e3 }

theorem enPassantWrongRank_not_valid : isValid enPassantWrongRank = false := by
  native_decide

/-- En passant target `e6`, but no opponent pawn on the landing square. -/
def enPassantNoJumpedPawn : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.d5 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := some Square.e6

theorem enPassantNoJumpedPawn_not_valid : isValid enPassantNoJumpedPawn = false := by
  native_decide

/-- En passant target `e6` with a jumped pawn, but no capturing pawn. -/
def enPassantNoCapture : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e5 then some { color := .black, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := some Square.e6

theorem enPassantNoCapture_not_valid : isValid enPassantNoCapture = false := by
  native_decide

/-- Black to move can capture en passant on `e3` after White's `e2–e4`. -/
def blackEnPassant : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e4 then some { color := .white, kind := .pawn }
    else if s = Square.d4 then some { color := .black, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := some Square.e3

theorem blackEnPassant_isValid : isValid blackEnPassant = true := by
  native_decide

end Position

end Chess
