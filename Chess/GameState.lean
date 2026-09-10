import Chess.Position

/-!
# Game states

A game state is the current position together with every position that
has already occurred, and whether a draw has just been proposed
(FIDE Article 9.1.2). FIDE Article 9.2 (threefold repetition) consults
this history; the half-move clock and full-move number can be recovered
from it later and are not stored separately.
-/

namespace Chess

/-- A game in progress: the position that now obtains, every earlier
position in chronological order, and whether a draw has just been
proposed. -/
@[ext]
structure GameState where
  /-- The current position. -/
  current : Position
  /-- Positions that have already occurred, oldest first.

  Does not include `current`. The starting game has an empty history. -/
  history : List Position
  /-- Whether the opponent has just offered a draw (FIDE Article 9.1.2).

  The offer remains until the player to move accepts it or declines it
  by making a move. -/
  drawProposed : Bool := false
deriving Inhabited

namespace GameState

/-- The standard starting game: the initial position, no prior
positions, and no pending draw offer. -/
def starting : GameState where
  current := Position.starting
  history := []
  drawProposed := false

@[simp] theorem starting_current : starting.current = Position.starting := rfl
@[simp] theorem starting_history : starting.history = [] := rfl
@[simp] theorem starting_drawProposed : starting.drawProposed = false := rfl

/-- Every position of the game, oldest first, including the current one. -/
def positions (g : GameState) : List Position :=
  g.history ++ [g.current]

@[simp] theorem starting_positions : starting.positions = [Position.starting] := rfl

/-- The number of plies already played: the length of the history. -/
def ply (g : GameState) : Nat :=
  g.history.length

@[simp] theorem starting_ply : starting.ply = 0 := rfl

/-- The positions of a game are never empty: they always include the
current position. -/
theorem positions_ne_nil (g : GameState) : g.positions ≠ [] := by
  simp [positions]

/-- The last recorded position is the current one. -/
theorem getLast_positions (g : GameState) :
    g.positions.getLast g.positions_ne_nil = g.current := by
  simp [positions]

/-- Advance the game to a new position, recording the previous current
position in the history. `proposeDraw` records an offer of a draw
together with this ply (FIDE Article 9.1.2). A plain move (`proposeDraw
= false`) declines any pending offer. Legality of the step is not
checked. -/
def advance (g : GameState) (p : Position) (proposeDraw : Bool := false) :
    GameState where
  current := p
  history := g.history ++ [g.current]
  drawProposed := proposeDraw

@[simp] theorem advance_current (g : GameState) (p : Position)
    (proposeDraw : Bool := false) :
    (g.advance p proposeDraw).current = p := rfl

@[simp] theorem advance_history (g : GameState) (p : Position)
    (proposeDraw : Bool := false) :
    (g.advance p proposeDraw).history = g.history ++ [g.current] := rfl

@[simp] theorem advance_drawProposed (g : GameState) (p : Position) :
    (g.advance p).drawProposed = false := rfl

@[simp] theorem advance_proposeDraw (g : GameState) (p : Position) :
    (g.advance p true).drawProposed = true := rfl

@[simp] theorem advance_positions (g : GameState) (p : Position)
    (proposeDraw : Bool := false) :
    (g.advance p proposeDraw).positions = g.positions ++ [p] := by
  simp [advance, positions]

@[simp] theorem advance_ply (g : GameState) (p : Position)
    (proposeDraw : Bool := false) :
    (g.advance p proposeDraw).ply = g.ply + 1 := by
  simp [advance, ply]

/-- Playing a ply yields a different game: the history is no longer empty
when starting from the initial game. -/
theorem starting_advance_ne (p : Position) :
    starting.advance p ≠ starting := by
  intro h
  have := congrArg GameState.history h
  simp at this

/-- Two games that differ only in their history are distinct. -/
theorem ne_of_history_ne {g₁ g₂ : GameState} (h : g₁.history ≠ g₂.history) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg GameState.history hg)

/-- Two games that differ only in whether a draw has just been proposed
are distinct. -/
theorem ne_of_drawProposed_ne {g₁ g₂ : GameState}
    (h : g₁.drawProposed ≠ g₂.drawProposed) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg GameState.drawProposed hg)

/-- Recording a pending draw offer yields a different game from the
starting game. -/
theorem starting_drawProposed_ne :
    { starting with drawProposed := true } ≠ starting :=
  ne_of_drawProposed_ne (by decide)

end GameState

end Chess
