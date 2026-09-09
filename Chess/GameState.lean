import Chess.Position

/-!
# Game states

A game state is the current position together with every position that
has already occurred. FIDE Article 9.2 (threefold repetition) consults
this history; the half-move clock and full-move number can be recovered
from it later and are not stored separately.
-/

namespace Chess

/-- A game in progress: the position that now obtains, and every earlier
position in chronological order. -/
@[ext]
structure GameState where
  /-- The current position. -/
  current : Position
  /-- Positions that have already occurred, oldest first.

  Does not include `current`. The starting game has an empty history. -/
  history : List Position
deriving Inhabited

namespace GameState

/-- The standard starting game: the initial position and no prior
positions. -/
def starting : GameState where
  current := Position.starting
  history := []

@[simp] theorem starting_current : starting.current = Position.starting := rfl
@[simp] theorem starting_history : starting.history = [] := rfl

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
position in the history. Legality of the step is not checked. -/
def advance (g : GameState) (p : Position) : GameState where
  current := p
  history := g.history ++ [g.current]

@[simp] theorem advance_current (g : GameState) (p : Position) :
    (g.advance p).current = p := rfl

@[simp] theorem advance_history (g : GameState) (p : Position) :
    (g.advance p).history = g.history ++ [g.current] := rfl

@[simp] theorem advance_positions (g : GameState) (p : Position) :
    (g.advance p).positions = g.positions ++ [p] := by
  simp [advance, positions]

@[simp] theorem advance_ply (g : GameState) (p : Position) :
    (g.advance p).ply = g.ply + 1 := by
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

end GameState

end Chess
