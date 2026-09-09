import Chess.Check
import Chess.Move

/-!
# Checkmate

A position is checkmate when the player to move is in check and has no
legal move (FIDE Laws of Chess, Articles 1.4.1 and 5.1.1). Occupied-board
attacks and `Position.legalMoves` are the same as elsewhere in the
library: blocking pieces are respected, pins are handled by requiring
that the player's king is not under attack after the move, and promotions
to different pieces are distinct moves.
-/

namespace Chess

namespace Position

/-- Whether the player to move is checkmated: they are in check and have
no legal move. -/
def inCheckmate (p : Position) : Bool :=
  p.inCheck && p.legalMoves.card == 0

/-- The player to move is checkmated: they are in check and every candidate
move is illegal. -/
def InCheckmate (p : Position) : Prop :=
  InCheck p ∧ ∀ m : Move, ¬ LegalMove p m

instance {p : Position} : Decidable (InCheckmate p) := by
  unfold InCheckmate
  infer_instance

theorem inCheckmate_eq_true_iff (p : Position) :
    p.inCheckmate = true ↔ InCheckmate p := by
  simp only [inCheckmate, InCheckmate, Bool.and_eq_true, beq_iff_eq,
    Finset.card_eq_zero, inCheck_eq_true_iff]
  refine and_congr_right fun _ => ?_
  rw [Finset.eq_empty_iff_forall_notMem]
  simp [mem_legalMoves_iff_LegalMove]

/-- Checkmate is a special case of check. -/
theorem inCheckmate_implies_inCheck {p : Position}
    (h : p.inCheckmate = true) : p.inCheck = true := by
  simp only [inCheckmate, Bool.and_eq_true] at h
  exact h.1

/-- A checkmated player has no legal move. -/
theorem inCheckmate_legalMoves_eq_empty {p : Position}
    (h : p.inCheckmate = true) : p.legalMoves = ∅ := by
  simp only [inCheckmate, Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero] at h
  exact h.2

/-- A position that is not in check is not checkmate. -/
theorem not_inCheck_not_inCheckmate {p : Position}
    (h : p.inCheck = false) : p.inCheckmate = false := by
  simp [inCheckmate, h]

/-- A position with a legal move is not checkmate. -/
theorem not_inCheckmate_of_mem_legalMoves {p : Position} {m : Move}
    (h : m ∈ p.legalMoves) : p.inCheckmate = false := by
  have hne : p.legalMoves.card ≠ 0 :=
    Nat.ne_of_gt (Finset.card_pos.mpr ⟨m, h⟩)
  simp [inCheckmate, hne]

/-- The standard starting position is not checkmate. -/
theorem starting_not_inCheckmate : starting.inCheckmate = false :=
  not_inCheck_not_inCheckmate starting_not_inCheck

theorem starting_not_InCheckmate : ¬ InCheckmate starting :=
  mt (inCheckmate_eq_true_iff starting).mpr
    (Eq.trans_ne starting_not_inCheckmate Bool.false_ne_true)

/-- Black is in check from a rook but can step off the file: not mate. -/
theorem currentPlayerInCheck_not_inCheckmate :
    currentPlayerInCheck.inCheckmate = false :=
  not_inCheckmate_of_mem_legalMoves
    (by native_decide :
      Move.std Square.e8 Square.d8 ∈ currentPlayerInCheck.legalMoves)

/-! ### Checkmate examples -/

/-- White queen on `h7`, protected by the king on `g6`: Black on `h8` is
mated. -/
def queenMate : Position where
  board := fun s =>
    if s = Square.g6 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.h7 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenMate_isValid : isValid queenMate = true := by
  native_decide

theorem queenMate_inCheck : queenMate.inCheck = true := by
  native_decide

theorem queenMate_inCheckmate : queenMate.inCheckmate = true := by
  native_decide

/-- The same placement with White to move is not checkmate: White's king
is safe and White has legal moves. -/
def queenMateWhiteToMove : Position :=
  { queenMate with toMove := .white }

theorem queenMateWhiteToMove_not_inCheckmate :
    queenMateWhiteToMove.inCheckmate = false :=
  not_inCheck_not_inCheckmate
    (by native_decide : queenMateWhiteToMove.inCheck = false)

/-- Black rook on the first rank, White king boxed in by its own pawns. -/
def backRankMate : Position where
  board := fun s =>
    if s = Square.g1 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a1 then some { color := .black, kind := .rook }
    else if s = Square.f2 then some { color := .white, kind := .pawn }
    else if s = Square.g2 then some { color := .white, kind := .pawn }
    else if s = Square.h2 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem backRankMate_isValid : isValid backRankMate = true := by
  native_decide

theorem backRankMate_inCheckmate : backRankMate.inCheckmate = true := by
  native_decide

/-- Smothered mate: a knight on `f7` checks the black king on `h8`, which
is boxed in by its own rook and pawns. -/
def smotheredMate : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.f7 then some { color := .white, kind := .knight }
    else if s = Square.g8 then some { color := .black, kind := .rook }
    else if s = Square.g7 then some { color := .black, kind := .pawn }
    else if s = Square.h7 then some { color := .black, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem smotheredMate_isValid : isValid smotheredMate = true := by
  native_decide

theorem smotheredMate_inCheckmate : smotheredMate.inCheckmate = true := by
  native_decide

/-- Stalemate is not checkmate: Black has no legal move, but is not in
check (White king `a6`, pawn `a7`, Black king `a8`). -/
def stalemate : Position where
  board := fun s =>
    if s = Square.a6 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem stalemate_isValid : isValid stalemate = true := by
  native_decide

theorem stalemate_not_inCheck : stalemate.inCheck = false := by
  native_decide

theorem stalemate_legalMoves_empty : stalemate.legalMoves = ∅ := by
  native_decide

theorem stalemate_not_inCheckmate : stalemate.inCheckmate = false :=
  not_inCheck_not_inCheckmate stalemate_not_inCheck

end Position

end Chess
