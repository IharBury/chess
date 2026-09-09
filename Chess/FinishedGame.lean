import Chess.GameState
import Mathlib.Data.Fintype.Card

/-!
# Finished games

A finished game records every position that occurred, whether a player
claimed a draw by threefold repetition (FIDE Article 9.2), resigned
(Article 5.1.2), or proposed or accepted a draw (Article 9.1), and the
outcome: a win for White, a win for Black, or a draw.

Legality of the play, and consistency of the outcome with the positions
and declarations (checkmate, stalemate, a well-founded repetition claim,
...), are not checked here.
-/

namespace Chess

/-- The result of a completed chess game: a win for one player, or a draw. -/
inductive GameOutcome where
  /-- The named player won. -/
  | win (winner : Color)
  /-- The game was drawn. -/
  | draw
deriving DecidableEq, Repr, Inhabited

namespace GameOutcome

instance : Fintype GameOutcome where
  elems := {win .white, win .black, draw}
  complete o := by
    cases o with
    | win c => cases c <;> simp
    | draw => simp

/-- There are three possible outcomes. -/
theorem card : Fintype.card GameOutcome = 3 :=
  rfl

/-- Whether this outcome is a draw. -/
def isDraw : GameOutcome → Bool
  | draw => true
  | win _ => false

/-- The winning player, if the game was not drawn. -/
def winner? : GameOutcome → Option Color
  | win c => some c
  | draw => none

@[simp] theorem isDraw_draw : isDraw draw = true := rfl
@[simp] theorem isDraw_win (c : Color) : isDraw (win c) = false := rfl
@[simp] theorem winner?_draw : winner? draw = none := rfl
@[simp] theorem winner?_win (c : Color) : winner? (win c) = some c := rfl

/-- A win is not a draw. -/
theorem win_ne_draw (c : Color) : win c ≠ draw := by
  intro h
  cases h

/-- White's win and Black's win are distinct. -/
theorem win_white_ne_win_black : win .white ≠ win .black := by
  intro h
  cases h

/-- The winner of a `win` outcome is the color stored in it. -/
theorem winner?_eq_some {o : GameOutcome} {c : Color} :
    o.winner? = some c ↔ o = win c := by
  cases o <;> simp

/-- An outcome is a draw iff it has no winner. -/
theorem isDraw_iff_winner?_none (o : GameOutcome) :
    o.isDraw = true ↔ o.winner? = none := by
  cases o <;> simp

end GameOutcome

/-- A completed chess game: the positions that occurred, player
declarations that can end the game, and the outcome. -/
@[ext]
structure FinishedGame where
  /-- Positions of the game, oldest first, including the terminal position. -/
  positions : List Position
  /-- Whether a player claimed a draw by threefold repetition
  (FIDE Article 9.2).

  Fivefold repetition (Article 9.6.1) is automatic and does not require
  a claim; this flag records only an explicit claim. -/
  claimedDrawByRepetition : Bool
  /-- Whether a player has resigned (FIDE Article 5.1.2). -/
  resigned : Bool
  /-- Whether a player has proposed a draw (FIDE Article 9.1.2). -/
  proposedDraw : Bool
  /-- Whether a player has accepted a draw offer (FIDE Article 9.1.2.3). -/
  acceptedDraw : Bool
  /-- Who won, or a draw. -/
  outcome : GameOutcome
deriving Inhabited

namespace FinishedGame

/-- Assemble a finished game from a game state, with no resignation,
repetition claim, or draw proposal/acceptance. The recorded positions
are `g.positions` (never empty). -/
def ofGameState (g : GameState) (outcome : GameOutcome) : FinishedGame where
  positions := g.positions
  claimedDrawByRepetition := false
  resigned := false
  proposedDraw := false
  acceptedDraw := false
  outcome := outcome

@[simp] theorem ofGameState_positions (g : GameState) (o : GameOutcome) :
    (ofGameState g o).positions = g.positions := rfl

@[simp] theorem ofGameState_claimedDrawByRepetition (g : GameState)
    (o : GameOutcome) :
    (ofGameState g o).claimedDrawByRepetition = false := rfl

@[simp] theorem ofGameState_resigned (g : GameState) (o : GameOutcome) :
    (ofGameState g o).resigned = false := rfl

@[simp] theorem ofGameState_proposedDraw (g : GameState) (o : GameOutcome) :
    (ofGameState g o).proposedDraw = false := rfl

@[simp] theorem ofGameState_acceptedDraw (g : GameState) (o : GameOutcome) :
    (ofGameState g o).acceptedDraw = false := rfl

@[simp] theorem ofGameState_outcome (g : GameState) (o : GameOutcome) :
    (ofGameState g o).outcome = o := rfl

/-- The positions of a finished game built from a game state are never
empty: they always include the terminal position. -/
theorem ofGameState_positions_ne_nil (g : GameState) (o : GameOutcome) :
    (ofGameState g o).positions ≠ [] := by
  simp [GameState.positions_ne_nil]

/-- The last recorded position of a finished game built from a game state
is that state's current position. -/
theorem ofGameState_getLast_positions (g : GameState) (o : GameOutcome) :
    (ofGameState g o).positions.getLast (ofGameState_positions_ne_nil g o) =
      g.current := by
  simp [ofGameState, GameState.getLast_positions]

/-- A drawn game that never left the starting position, with no player
declarations. -/
def startingDraw : FinishedGame :=
  ofGameState .starting .draw

@[simp] theorem startingDraw_positions :
    startingDraw.positions = [Position.starting] := rfl

@[simp] theorem startingDraw_claimedDrawByRepetition :
    startingDraw.claimedDrawByRepetition = false := rfl

@[simp] theorem startingDraw_resigned :
    startingDraw.resigned = false := rfl

@[simp] theorem startingDraw_proposedDraw :
    startingDraw.proposedDraw = false := rfl

@[simp] theorem startingDraw_acceptedDraw :
    startingDraw.acceptedDraw = false := rfl

@[simp] theorem startingDraw_outcome :
    startingDraw.outcome = .draw := rfl

/-- Two finished games that differ only in their outcome are distinct. -/
theorem ne_of_outcome_ne {g₁ g₂ : FinishedGame} (h : g₁.outcome ≠ g₂.outcome) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.outcome hg)

/-- Two finished games that differ only in whether a repetition draw was
claimed are distinct. -/
theorem ne_of_claimedDrawByRepetition_ne {g₁ g₂ : FinishedGame}
    (h : g₁.claimedDrawByRepetition ≠ g₂.claimedDrawByRepetition) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.claimedDrawByRepetition hg)

/-- Two finished games that differ only in whether a player resigned are
distinct. -/
theorem ne_of_resigned_ne {g₁ g₂ : FinishedGame}
    (h : g₁.resigned ≠ g₂.resigned) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.resigned hg)

/-- Two finished games that differ only in whether a draw was proposed
are distinct. -/
theorem ne_of_proposedDraw_ne {g₁ g₂ : FinishedGame}
    (h : g₁.proposedDraw ≠ g₂.proposedDraw) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.proposedDraw hg)

/-- Two finished games that differ only in whether a draw offer was
accepted are distinct. -/
theorem ne_of_acceptedDraw_ne {g₁ g₂ : FinishedGame}
    (h : g₁.acceptedDraw ≠ g₂.acceptedDraw) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.acceptedDraw hg)

/-- Two finished games that differ only in their positions are distinct. -/
theorem ne_of_positions_ne {g₁ g₂ : FinishedGame}
    (h : g₁.positions ≠ g₂.positions) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.positions hg)

/-- A win for White from the starting game is not a draw. -/
theorem starting_whiteWin_ne_draw :
    ofGameState .starting (.win .white) ≠ startingDraw :=
  ne_of_outcome_ne (GameOutcome.win_ne_draw _)

/-- A win for White is not a win for Black. -/
theorem starting_whiteWin_ne_blackWin :
    ofGameState .starting (.win .white) ≠
      ofGameState .starting (.win .black) :=
  ne_of_outcome_ne GameOutcome.win_white_ne_win_black

/-- Claiming a draw by repetition yields a different finished game from
one that records no such claim, even when the positions and outcome agree. -/
theorem starting_claimedRepetition_ne :
    { startingDraw with claimedDrawByRepetition := true } ≠ startingDraw :=
  ne_of_claimedDrawByRepetition_ne (by decide)

/-- A resignation yields a different finished game from one that records
no resignation, even when the positions and outcome agree. -/
theorem starting_resigned_ne :
    { ofGameState .starting (.win .white) with resigned := true } ≠
      ofGameState .starting (.win .white) :=
  ne_of_resigned_ne (by decide)

/-- Proposing a draw yields a different finished game from one that
records no proposal, even when the positions and outcome agree. -/
theorem starting_proposedDraw_ne :
    { startingDraw with proposedDraw := true } ≠ startingDraw :=
  ne_of_proposedDraw_ne (by decide)

/-- Accepting a draw yields a different finished game from one that
records no acceptance, even when the positions and outcome agree. -/
theorem starting_acceptedDraw_ne :
    { startingDraw with acceptedDraw := true } ≠ startingDraw :=
  ne_of_acceptedDraw_ne (by decide)

/-- Advancing the underlying game yields a different finished game. -/
theorem ofGameState_advance_ne (p : Position) (o : GameOutcome) :
    ofGameState (GameState.starting.advance p) o ≠
      ofGameState .starting o :=
  ne_of_positions_ne (by simp [GameState.advance_positions])

end FinishedGame

end Chess
