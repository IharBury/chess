import Chess.Board
import Chess.GameState
import Chess.Move

/-!
# Player actions

An action is one of the things the player to move may do in a game that
has not yet ended: play a legal move, optionally offering a draw or
claiming that the move produces a draw by threefold repetition or by the
fifty-move rule; claim such a draw in the position that already obtains;
resign; or accept a pending draw offer.

Whether an action is legal in a given game is `GameState.isLegalAction`.
`GameState.legalActions` enumerates every legal action.
-/

namespace Chess

/-- An action of the player to move, not yet checked for legality in a
particular game. -/
inductive Action where
  /-- Play a move. -/
  | move (m : Move)
  /-- Play a move and offer a draw (FIDE Article 9.1.2). -/
  | moveAndProposeDraw (m : Move)
  /-- Resign (FIDE Article 5.1.2). -/
  | surrender
  /-- Play a move and claim that the resulting position is a third
  occurrence (FIDE Article 9.2.1.1). -/
  | moveAndClaimRepetition (m : Move)
  /-- Claim that the current position is a third occurrence
  (FIDE Article 9.2.1.2). -/
  | claimRepetition
  /-- Play a move and claim that it completes fifty moves by each player
  without a pawn move or capture (FIDE Article 9.3.1). -/
  | moveAndClaimNoProgress (m : Move)
  /-- Claim that fifty moves by each player have already been completed
  without a pawn move or capture (FIDE Article 9.3.2). -/
  | claimNoProgress
  /-- Accept a pending draw offer (FIDE Article 9.1.2.3). -/
  | acceptDraw
deriving DecidableEq, Repr, Inhabited

namespace Action

/-- Playing a move is not the same action as playing it and offering a
draw. -/
theorem move_ne_moveAndProposeDraw (m₁ m₂ : Move) :
    move m₁ ≠ moveAndProposeDraw m₂ := by
  intro h
  cases h

/-- Playing a move is not resignation. -/
theorem move_ne_surrender (m : Move) : move m ≠ surrender := by
  intro h
  cases h

/-- A repetition claim is not a fifty-move claim. -/
theorem claimRepetition_ne_claimNoProgress :
    claimRepetition ≠ claimNoProgress := by
  intro h
  cases h

/-- Accepting a draw is not resignation. -/
theorem acceptDraw_ne_surrender : acceptDraw ≠ surrender := by
  intro h
  cases h

/-- Offering a draw with a move is not claiming repetition with that
move. -/
theorem moveAndProposeDraw_ne_moveAndClaimRepetition (m₁ m₂ : Move) :
    moveAndProposeDraw m₁ ≠ moveAndClaimRepetition m₂ := by
  intro h
  cases h

end Action

namespace Board

/-- Squares occupied by a pawn of color `c`. -/
def pawnSquares (b : Board) (c : Color) : Finset Square :=
  Finset.univ.filter fun s =>
    (b s).map (fun p => (p.color, p.kind)) = some (c, .pawn)

end Board

namespace GameState

/-- Fifty moves by each player: 100 half-moves (FIDE Article 9.3). -/
def noProgressPlies : Nat := 100

/-- All 64 squares, in a computable list. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f =>
    (List.finRange 8).map fun r => ⟨f, r⟩

/-- Whether two placements agree on every square. -/
def sameBoard (b₁ b₂ : Board) : Bool :=
  allSquares.all fun s =>
    match b₁ s, b₂ s with
    | none, none => true
    | some p₁, some p₂ => (p₁.color == p₂.color) && (p₁.kind == p₂.kind)
    | _, _ => false

/-- Whether remaining castling rights agree. -/
def sameCastling (c₁ c₂ : CastlingRights) : Bool :=
  (c₁.allows .white .kingside == c₂.allows .white .kingside) &&
    (c₁.allows .white .queenside == c₂.allows .white .queenside) &&
    (c₁.allows .black .kingside == c₂.allows .black .kingside) &&
    (c₁.allows .black .queenside == c₂.allows .black .queenside)

/-- Whether `p` and `q` are the same position for repetition
(FIDE Article 9.2): placement, side to move, castling rights, and en
passant. -/
def samePosition (p q : Position) : Bool :=
  sameBoard p.board q.board &&
    (p.toMove == q.toMove) &&
    sameCastling p.castling q.castling &&
    (p.enPassant == q.enPassant)


/-- How many times `p` occurs among the positions of `g`. -/
def occurrenceCount (g : GameState) (p : Position) : Nat :=
  g.positions.countP (samePosition p)

/-- Whether the player to move may claim a draw by threefold repetition
in the current position (FIDE Article 9.2.1.2). -/
def appearsThreefold (g : GameState) : Bool :=
  decide (3 ≤ g.occurrenceCount g.current)

/-- Whether playing `m` would produce a third occurrence of the
resulting position (FIDE Article 9.2.1.1). -/
def appearsThreefoldAfter (g : GameState) (m : Move) : Bool :=
  let p := g.current.play m
  decide (3 ≤ g.occurrenceCount p + 1)

/-- Whether the side that moved between `before` and `after` moved a
pawn or captured. -/
def pawnMoveOrCapture (before after : Position) : Bool :=
  !(before.board.occupied.card == after.board.occupied.card) ||
    !(before.board.pawnSquares before.toMove ==
        after.board.pawnSquares before.toMove)

/-- Consecutive positions of the game, oldest first, each pair a ply. -/
def transitions (g : GameState) : List (Position × Position) :=
  g.positions.zip g.positions.tail

/-- Half-moves since the last pawn move or capture, recovered from the
position history. -/
def pliesWithoutProgress (g : GameState) : Nat :=
  g.transitions.foldl
    (fun acc pq => if pawnMoveOrCapture pq.1 pq.2 then 0 else acc + 1) 0

/-- Whether fifty moves by each player have been completed without a
pawn move or capture (FIDE Article 9.3.2). -/
def noProgress (g : GameState) : Bool :=
  decide (noProgressPlies ≤ g.pliesWithoutProgress)

/-- Whether `m` is a pawn move or a capture, resetting the fifty-move
clock. En passant is a pawn move. -/
def moveIsPawnMoveOrCapture (p : Position) (m : Move) : Bool :=
  match p.board m.src with
  | none => false
  | some piece => (piece.kind == .pawn) || (p.board m.dst).isSome

/-- Whether playing `m` would complete fifty moves by each player
without a pawn move or capture (FIDE Article 9.3.1). -/
def leadsToNoProgress (g : GameState) (m : Move) : Bool :=
  !moveIsPawnMoveOrCapture g.current m &&
    decide (noProgressPlies ≤ g.pliesWithoutProgress + 1)

/-- Whether the opponent has already made at least one move.

A draw offer may accompany a move only in this case. -/
def opponentHasMoved (g : GameState) : Bool :=
  g.history.any (fun p => p.toMove == g.current.toMove.other)

/-- Whether `a` is a legal action in `g`, assuming the game has not
ended. -/
def isLegalAction (g : GameState) : Action → Bool
  | .move m => g.current.isLegalMove m
  | .moveAndProposeDraw m =>
      g.current.isLegalMove m && g.opponentHasMoved
  | .surrender => true
  | .moveAndClaimRepetition m =>
      g.current.isLegalMove m && g.appearsThreefoldAfter m
  | .claimRepetition => g.appearsThreefold
  | .moveAndClaimNoProgress m =>
      g.current.isLegalMove m && g.leadsToNoProgress m
  | .claimNoProgress => g.noProgress
  | .acceptDraw => g.drawProposed

/-- `a` is a legal action in `g`, assuming the game has not ended. -/
def LegalAction (g : GameState) (a : Action) : Prop :=
  isLegalAction g a = true

instance {g : GameState} {a : Action} : Decidable (LegalAction g a) :=
  inferInstanceAs (Decidable (isLegalAction g a = true))

/-- Every legal action of the player to move in `g`, assuming the game
has not ended. -/
def legalActions (g : GameState) : Finset Action :=
  g.current.legalMoves.biUnion (fun m =>
      {Action.move m} ∪
        (if g.opponentHasMoved then {Action.moveAndProposeDraw m} else ∅) ∪
        (if g.appearsThreefoldAfter m then
          {Action.moveAndClaimRepetition m} else ∅) ∪
        (if g.leadsToNoProgress m then
          {Action.moveAndClaimNoProgress m} else ∅)) ∪
    {Action.surrender} ∪
    (if g.appearsThreefold then {Action.claimRepetition} else ∅) ∪
    (if g.noProgress then {Action.claimNoProgress} else ∅) ∪
    (if g.drawProposed then {Action.acceptDraw} else ∅)

set_option linter.unusedDecidableInType false in
theorem mem_if_singleton {α} [DecidableEq α] {b : Bool} {x y : α} :
    y ∈ (if b then ({x} : Finset α) else ∅) ↔ b = true ∧ y = x := by
  cases b <;> simp

theorem mem_legalActions (g : GameState) (a : Action) :
    a ∈ g.legalActions ↔ g.isLegalAction a = true := by
  cases a with
  | move m =>
    simp [legalActions, isLegalAction, Position.mem_legalMoves, mem_if_singleton]
  | moveAndProposeDraw m =>
    simp [legalActions, isLegalAction, Position.mem_legalMoves, mem_if_singleton]
  | surrender =>
    simp [legalActions, isLegalAction, mem_if_singleton]
  | moveAndClaimRepetition m =>
    simp [legalActions, isLegalAction, Position.mem_legalMoves, mem_if_singleton]
  | claimRepetition =>
    simp [legalActions, isLegalAction, mem_if_singleton]
  | claimNoProgress =>
    simp [legalActions, isLegalAction, mem_if_singleton]
  | moveAndClaimNoProgress m =>
    simp [legalActions, isLegalAction, Position.mem_legalMoves, mem_if_singleton]
  | acceptDraw =>
    simp [legalActions, isLegalAction, mem_if_singleton]

theorem mem_legalActions_iff_LegalAction (g : GameState) (a : Action) :
    a ∈ g.legalActions ↔ LegalAction g a :=
  mem_legalActions g a

/-- Resignation is always legal in an unfinished game. -/
theorem surrender_mem (g : GameState) : Action.surrender ∈ g.legalActions := by
  simp [mem_legalActions, isLegalAction]

/-- A pending draw offer may be accepted; otherwise acceptance is not
legal. -/
theorem acceptDraw_mem (g : GameState) :
    Action.acceptDraw ∈ g.legalActions ↔ g.drawProposed = true := by
  simp [mem_legalActions, isLegalAction]

/-- Playing `m` is legal iff `m` is a legal move of the current
position. -/
theorem move_mem (g : GameState) (m : Move) :
    Action.move m ∈ g.legalActions ↔ g.current.isLegalMove m = true := by
  simp [mem_legalActions, isLegalAction]

/-- Offering a draw with `m` requires a legal move and that the opponent
has already moved. -/
theorem moveAndProposeDraw_mem (g : GameState) (m : Move) :
    Action.moveAndProposeDraw m ∈ g.legalActions ↔
      g.current.isLegalMove m = true ∧ g.opponentHasMoved = true := by
  simp [mem_legalActions, isLegalAction]

/-- At the start of the game the opponent has not moved, so a draw may
not be offered. -/
theorem starting_opponentHasMoved :
    starting.opponentHasMoved = false := rfl

/-- The starting game has no pending draw offer. -/
theorem starting_not_acceptDraw :
    Action.acceptDraw ∉ starting.legalActions := by
  simp [acceptDraw_mem]

/-- The starting position is not a third occurrence of itself. -/
theorem starting_not_claimRepetition :
    Action.claimRepetition ∉ starting.legalActions := by
  native_decide

/-- The starting game has no fifty quiet half-moves behind it. -/
theorem starting_not_claimNoProgress :
    Action.claimNoProgress ∉ starting.legalActions := by
  native_decide

/-- White's `e2–e4` is a legal action at the start. -/
theorem starting_e2e4_move_mem :
    Action.move (Move.std Square.e2 Square.e4) ∈ starting.legalActions := by
  rw [move_mem]
  exact Position.starting_e2e4_legal

/-- White may not offer a draw with the first move of the game. -/
theorem starting_e2e4_not_proposeDraw :
    Action.moveAndProposeDraw (Move.std Square.e2 Square.e4) ∉
      starting.legalActions := by
  simp [moveAndProposeDraw_mem, starting_opponentHasMoved]

/-- The starting game has 21 legal actions: the 20 legal moves, and
resignation. -/
theorem starting_legalActions_card : starting.legalActions.card = 21 := by
  native_decide

/-- After `1. e4`, Black may play and offer a draw: White has moved. -/
def afterE2e4 : GameState :=
  starting.advance (Position.starting.play (Move.std Square.e2 Square.e4))

theorem afterE2e4_opponentHasMoved : afterE2e4.opponentHasMoved = true := by
  native_decide

theorem afterE2e4_e7e5_proposeDraw_mem :
    Action.moveAndProposeDraw (Move.std Square.e7 Square.e5) ∈
      afterE2e4.legalActions := by
  native_decide

theorem afterE2e4_not_acceptDraw :
    Action.acceptDraw ∉ afterE2e4.legalActions := by
  simp [afterE2e4, acceptDraw_mem]

/-- After `1. e4 e5` with a draw offer, White may accept. -/
def afterE2e4e7e5Offer : GameState :=
  afterE2e4.advance
    (afterE2e4.current.play (Move.std Square.e7 Square.e5)) true

theorem afterE2e4e7e5Offer_acceptDraw_mem :
    Action.acceptDraw ∈ afterE2e4e7e5Offer.legalActions := by
  simp [afterE2e4e7e5Offer, acceptDraw_mem]

/-- A game whose current position has already occurred twice before. -/
def threefoldStarting : GameState where
  current := Position.starting
  history := [Position.starting, Position.starting]
  drawProposed := false

theorem threefoldStarting_claimRepetition_mem :
    Action.claimRepetition ∈ threefoldStarting.legalActions := by
  native_decide

/-- After `e2–e4` from a game that has already seen that position twice,
the move may be claimed as a third occurrence. -/
def threefoldBeforeE4 : GameState where
  current := Position.starting
  history :=
    let p := Position.starting.play (Move.std Square.e2 Square.e4)
    [p, p]
  drawProposed := false

theorem threefoldBeforeE4_moveAndClaim_mem :
    Action.moveAndClaimRepetition (Move.std Square.e2 Square.e4) ∈
      threefoldBeforeE4.legalActions := by
  native_decide

/-- Kings on `e1` and `e8`, White to move, no other pieces. -/
def kingsOnly : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else none
  toMove := .white
  castling := ∅
  enPassant := none

/-- A game that has repeated `p` for `n` plies (plus the current copy). -/
def repeated (p : Position) (n : Nat) : GameState where
  current := p
  history := List.replicate n p
  drawProposed := false

theorem pawnMoveOrCapture_self (p : Position) :
    pawnMoveOrCapture p p = false := by
  simp [pawnMoveOrCapture]

theorem zip_replicate_succ {α} (a : α) (n : Nat) :
    (List.replicate (n + 1) a).zip (List.replicate n a) =
      List.replicate n (a, a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc (List.replicate (n + 1 + 1) a).zip (List.replicate (n + 1) a)
        = (a :: List.replicate (n + 1) a).zip (a :: List.replicate n a) := by
            simp [List.replicate_succ]
      _ = (a, a) :: (List.replicate (n + 1) a).zip (List.replicate n a) := rfl
      _ = (a, a) :: List.replicate n (a, a) := by rw [ih]
      _ = List.replicate (n + 1) (a, a) := by simp [List.replicate_succ]

theorem replicate_concat {α} (a : α) (n : Nat) :
    List.replicate n a ++ [a] = List.replicate (n + 1) a := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem foldl_quiet_replicate_from (p : Position) (n acc : Nat)
    (hp : pawnMoveOrCapture p p = false) :
    (List.replicate n (p, p)).foldl
      (fun acc pq => if pawnMoveOrCapture pq.1 pq.2 then 0 else acc + 1) acc =
      acc + n := by
  induction n generalizing acc with
  | zero => simp
  | succ n ih =>
    simp [List.replicate_succ, List.foldl_cons, hp, ih]
    omega

theorem foldl_quiet_replicate (p : Position) (n : Nat)
    (hp : pawnMoveOrCapture p p = false) :
    (List.replicate n (p, p)).foldl
      (fun acc pq => if pawnMoveOrCapture pq.1 pq.2 then 0 else acc + 1) 0 =
      n := by
  simpa using foldl_quiet_replicate_from p n 0 hp

theorem pliesWithoutProgress_repeated (p : Position) (n : Nat) :
    (repeated p n).pliesWithoutProgress = n := by
  have hp : pawnMoveOrCapture p p = false := pawnMoveOrCapture_self p
  have hpos : (repeated p n).positions = List.replicate (n + 1) p := by
    simp [repeated, positions, replicate_concat]
  simp only [pliesWithoutProgress, transitions, hpos]
  have htail : (List.replicate (n + 1) p).tail = List.replicate n p := by
    simp [List.replicate_succ]
  rw [htail, zip_replicate_succ, foldl_quiet_replicate p n hp]

theorem repeated_noProgress (p : Position) {n : Nat}
    (h : noProgressPlies ≤ n) :
    (repeated p n).noProgress = true := by
  simpa [noProgress, pliesWithoutProgress_repeated] using decide_eq_true h

theorem repeated_not_noProgress (p : Position) {n : Nat}
    (h : n < noProgressPlies) :
    (repeated p n).noProgress = false := by
  simpa [noProgress, pliesWithoutProgress_repeated] using
    decide_eq_false (Nat.not_le_of_gt h)

/-- After 100 quiet plies, a fifty-move claim is legal. -/
theorem kingsOnly_100_claimNoProgress_mem :
    Action.claimNoProgress ∈ (repeated kingsOnly 100).legalActions := by
  rw [mem_legalActions, isLegalAction]
  exact repeated_noProgress kingsOnly (Nat.le_refl noProgressPlies)

/-- After 99 quiet plies the current position is not yet a fifty-move
draw, but a further quiet move may be claimed as completing it. -/
theorem kingsOnly_99_not_claimNoProgress :
    Action.claimNoProgress ∉ (repeated kingsOnly 99).legalActions := by
  simp [mem_legalActions, isLegalAction,
    repeated_not_noProgress kingsOnly (by decide : 99 < noProgressPlies)]

theorem kingsOnly_e1d1_legal :
    Position.isLegalMove kingsOnly (Move.std Square.e1 Square.d1) = true := by
  native_decide

theorem kingsOnly_e1d1_not_pawnOrCapture :
    moveIsPawnMoveOrCapture kingsOnly (Move.std Square.e1 Square.d1) =
      false := by
  native_decide

theorem kingsOnly_99_moveAndClaimNoProgress_mem :
    Action.moveAndClaimNoProgress (Move.std Square.e1 Square.d1) ∈
      (repeated kingsOnly 99).legalActions := by
  rw [mem_legalActions, isLegalAction, Bool.and_eq_true]
  refine ⟨kingsOnly_e1d1_legal, ?_⟩
  have hc : (repeated kingsOnly 99).current = kingsOnly := rfl
  have hclock : (repeated kingsOnly 99).pliesWithoutProgress = 99 :=
    pliesWithoutProgress_repeated kingsOnly 99
  simp [leadsToNoProgress, hc, kingsOnly_e1d1_not_pawnOrCapture, hclock,
    noProgressPlies]

end GameState

end Chess
