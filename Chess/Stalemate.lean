import Chess.Checkmate

/-!
# Stalemate

A position is stalemate when the player to move is not in check and has
no legal move (FIDE Laws of Chess, Article 5.2.1). Occupied-board attacks
and `Position.legalMoves` are the same as elsewhere in the library:
blocking pieces are respected, pins are handled by requiring that the
player's king is not under attack after the move, and promotions to
different pieces are distinct moves.
-/

namespace Chess

namespace Position

/-- Whether the player to move is stalemated: they are not in check and
have no legal move. -/
def inStalemate (p : Position) : Bool :=
  !p.inCheck && p.legalMoves.card == 0

/-- The player to move is stalemated: they are not in check and have no
legal move. -/
def InStalemate (p : Position) : Prop :=
  ¬ InCheck p ∧ p.legalMoves = ∅

instance {p : Position} : Decidable (InStalemate p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem inStalemate_eq_true_iff (p : Position) :
    p.inStalemate = true ↔ InStalemate p := by
  simp only [inStalemate, InStalemate, Bool.and_eq_true, beq_iff_eq,
    Finset.card_eq_zero]
  rw [Bool.not_eq_true', ← inCheck_eq_true_iff, Bool.not_eq_true]

/-- Stalemate is the absence of check together with every candidate move
being illegal. -/
theorem InStalemate_iff_forall_not_LegalMove (p : Position) :
    InStalemate p ↔ ¬ InCheck p ∧ ∀ m : Move, ¬ LegalMove p m := by
  simp [InStalemate, Finset.eq_empty_iff_forall_notMem, mem_legalMoves_iff_LegalMove]

/-- A stalemated player is not in check. -/
theorem inStalemate_not_inCheck {p : Position}
    (h : p.inStalemate = true) : p.inCheck = false := by
  simp only [inStalemate, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1

/-- A stalemated player has no legal move. -/
theorem inStalemate_legalMoves_eq_empty {p : Position}
    (h : p.inStalemate = true) : p.legalMoves = ∅ := by
  simp only [inStalemate, Bool.and_eq_true, beq_iff_eq, Finset.card_eq_zero] at h
  exact h.2

/-- A position that is in check is not stalemate. -/
theorem inCheck_not_inStalemate {p : Position}
    (h : p.inCheck = true) : p.inStalemate = false := by
  simp [inStalemate, h]

/-- A position with a legal move is not stalemate. -/
theorem not_inStalemate_of_legalMoves_ne_empty {p : Position}
    (h : p.legalMoves ≠ ∅) : p.inStalemate = false := by
  have hc : (p.legalMoves.card == 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact mt Finset.card_eq_zero.mp h
  simp [inStalemate, hc]

/-- Checkmate is not stalemate: the player to move is in check. -/
theorem inCheckmate_not_inStalemate {p : Position}
    (h : p.inCheckmate = true) : p.inStalemate = false :=
  inCheck_not_inStalemate (inCheckmate_implies_inCheck h)

/-- Stalemate is not checkmate: the player to move is not in check. -/
theorem inStalemate_not_inCheckmate {p : Position}
    (h : p.inStalemate = true) : p.inCheckmate = false :=
  not_inCheck_not_inCheckmate (inStalemate_not_inCheck h)

/-- The standard starting position is not stalemate. -/
theorem starting_not_inStalemate : starting.inStalemate = false :=
  not_inStalemate_of_legalMoves_ne_empty (by
    have h : starting.legalMoves.card = 20 := starting_legalMoves_card
    intro he
    simp [he] at h)

theorem starting_not_InStalemate : ¬ InStalemate starting :=
  mt (inStalemate_eq_true_iff starting).mpr
    (Eq.trans_ne starting_not_inStalemate Bool.false_ne_true)

/-- Black is in check from a rook but can step off the file: not
stalemate. -/
theorem currentPlayerInCheck_not_inStalemate :
    currentPlayerInCheck.inStalemate = false :=
  inCheck_not_inStalemate currentPlayerInCheck_inCheck

/-! ### Stalemate examples -/

/-- The king-and-pawn corner position from `Checkmate` is stalemate. -/
theorem stalemate_InStalemate : InStalemate stalemate :=
  ⟨mt (inCheck_eq_true_iff stalemate).mpr
      (Eq.trans_ne stalemate_not_inCheck Bool.false_ne_true),
    stalemate_legalMoves_empty⟩

theorem stalemate_inStalemate : stalemate.inStalemate = true :=
  (inStalemate_eq_true_iff stalemate).mpr stalemate_InStalemate

/-- The same placement with White to move is not stalemate: White's king
is safe and White has legal moves. -/
def stalemateWhiteToMove : Position :=
  { stalemate with toMove := .white }

theorem stalemateWhiteToMove_not_inStalemate :
    stalemateWhiteToMove.inStalemate = false :=
  not_inStalemate_of_legalMoves_ne_empty
    (by native_decide : stalemateWhiteToMove.legalMoves ≠ ∅)

/-- Queen versus king in the corner: White queen on `f7` does not check
the black king on `h8`, but covers every flight square. -/
def queenStalemate : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.f7 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenStalemate_isValid : isValid queenStalemate = true := by
  native_decide

theorem queenStalemate_not_inCheck : queenStalemate.inCheck = false := by
  native_decide

theorem queenStalemate_inStalemate : queenStalemate.inStalemate = true := by
  native_decide

/-- The same queen, one file further away: Black can flee to `g8`. -/
def queenNotStalemate : Position where
  board := fun s =>
    if s = Square.a1 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.e7 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenNotStalemate_not_inStalemate :
    queenNotStalemate.inStalemate = false :=
  not_inStalemate_of_legalMoves_ne_empty
    (by native_decide : queenNotStalemate.legalMoves ≠ ∅)

/-- Rook versus king: the rook on `g7` is protected by the white king, so
Black cannot capture it and has no flight square, but is not in check. -/
def rookStalemate : Position where
  board := fun s =>
    if s = Square.f6 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.g7 then some { color := .white, kind := .rook }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookStalemate_isValid : isValid rookStalemate = true := by
  native_decide

theorem rookStalemate_inStalemate : rookStalemate.inStalemate = true := by
  native_decide

/-- Checkmate is not stalemate. -/
theorem queenMate_not_inStalemate : queenMate.inStalemate = false :=
  inCheckmate_not_inStalemate queenMate_inCheckmate

end Position

end Chess
