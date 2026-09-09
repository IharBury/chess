import Chess.GameState
import Mathlib.Data.Fintype.Card

/-!
# Finished games

A finished game records every position that occurred, whether a player
claimed a draw by threefold repetition (FIDE Article 9.2), resigned
(Article 5.1.2), or proposed or accepted a draw (Article 9.1), whether
the game ended for technical reasons including expiry of a player's time
(Article 6.9), and the outcome: a win for White, a win for Black, or a
draw.

Each draw proposal records who offered and on which turn. If an offer is
not accepted, further proposals may be recorded, including by the other
player.

Legality of the play, and consistency of the outcome with the positions
and declarations (checkmate, stalemate, a well-founded repetition claim,
flag fall, ...), are not checked here.
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

/-- A technical reason a game may end without checkmate, stalemate,
resignation, or an agreed or claimed draw. -/
inductive TechnicalReason where
  /-- A player's time expired (FIDE Article 6.9).

  The player who overstepped loses, except that the game is drawn if the
  opponent cannot checkmate by any possible series of legal moves. -/
  | timer
  /-- Any other technical termination: default, an arbiter's decision,
  or similar. -/
  | other
deriving DecidableEq, Repr, Inhabited

namespace TechnicalReason

instance : Fintype TechnicalReason where
  elems := {timer, other}
  complete r := by cases r <;> simp

/-- There are two distinguished technical reasons. -/
theorem card : Fintype.card TechnicalReason = 2 :=
  rfl

/-- Timer expiry is not a generic "other" technical reason. -/
theorem timer_ne_other : timer ≠ other := by
  intro h
  cases h

end TechnicalReason

/-- An offer of a draw (FIDE Article 9.1.2).

If the opponent declines (by making a move without accepting), further
offers may be made, including by the other player. Each offer records
who proposed and on which turn. -/
@[ext]
structure DrawProposal where
  /-- The player who offered the draw. -/
  proposer : Color
  /-- The turn on which the offer was made: the number of half-moves
  already played, matching `GameState.ply`. -/
  turn : Nat
deriving DecidableEq, Repr, Inhabited

namespace DrawProposal

/-- Two proposals that differ only in who offered are distinct. -/
theorem ne_of_proposer_ne {p₁ p₂ : DrawProposal}
    (h : p₁.proposer ≠ p₂.proposer) : p₁ ≠ p₂ := by
  intro hp
  exact h (congrArg DrawProposal.proposer hp)

/-- Two proposals that differ only in the turn are distinct. -/
theorem ne_of_turn_ne {p₁ p₂ : DrawProposal}
    (h : p₁.turn ≠ p₂.turn) : p₁ ≠ p₂ := by
  intro hp
  exact h (congrArg DrawProposal.turn hp)

/-- White offering on a given turn is not Black offering on that turn. -/
theorem white_ne_black (t : Nat) :
    ({ proposer := .white, turn := t } : DrawProposal) ≠
      { proposer := .black, turn := t } :=
  ne_of_proposer_ne (Color.other_ne .black)

end DrawProposal

/-- A completed chess game: the positions that occurred, player
declarations that can end the game, an optional technical termination,
and the outcome. -/
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
  /-- Draw offers, oldest first (FIDE Article 9.1.2).

  Each records who proposed and on which turn. If an offer is declined,
  later offers may appear, possibly from the other player. -/
  drawProposals : List DrawProposal
  /-- Whether the last recorded draw offer was accepted
  (FIDE Article 9.1.2.3). -/
  acceptedDraw : Bool
  /-- Technical termination, if any.

  `some .timer` is expiry of a player's time; `some .other` covers
  remaining technical reasons; `none` means the game did not end
  technically. -/
  technical : Option TechnicalReason
  /-- Who won, or a draw. -/
  outcome : GameOutcome
deriving Inhabited

namespace FinishedGame

/-- Assemble a finished game from a game state, with no resignation,
repetition claim, draw proposals, acceptance, or technical termination.
The recorded positions are `g.positions` (never empty). -/
def ofGameState (g : GameState) (outcome : GameOutcome) : FinishedGame where
  positions := g.positions
  claimedDrawByRepetition := false
  resigned := false
  drawProposals := []
  acceptedDraw := false
  technical := none
  outcome := outcome

@[simp] theorem ofGameState_positions (g : GameState) (o : GameOutcome) :
    (ofGameState g o).positions = g.positions := rfl

@[simp] theorem ofGameState_claimedDrawByRepetition (g : GameState)
    (o : GameOutcome) :
    (ofGameState g o).claimedDrawByRepetition = false := rfl

@[simp] theorem ofGameState_resigned (g : GameState) (o : GameOutcome) :
    (ofGameState g o).resigned = false := rfl

@[simp] theorem ofGameState_drawProposals (g : GameState) (o : GameOutcome) :
    (ofGameState g o).drawProposals = [] := rfl

@[simp] theorem ofGameState_acceptedDraw (g : GameState) (o : GameOutcome) :
    (ofGameState g o).acceptedDraw = false := rfl

@[simp] theorem ofGameState_technical (g : GameState) (o : GameOutcome) :
    (ofGameState g o).technical = none := rfl

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

@[simp] theorem startingDraw_drawProposals :
    startingDraw.drawProposals = [] := rfl

@[simp] theorem startingDraw_acceptedDraw :
    startingDraw.acceptedDraw = false := rfl

@[simp] theorem startingDraw_technical :
    startingDraw.technical = none := rfl

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

/-- Two finished games that differ only in their draw proposals are
distinct. -/
theorem ne_of_drawProposals_ne {g₁ g₂ : FinishedGame}
    (h : g₁.drawProposals ≠ g₂.drawProposals) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.drawProposals hg)

/-- Two finished games that differ only in whether a draw offer was
accepted are distinct. -/
theorem ne_of_acceptedDraw_ne {g₁ g₂ : FinishedGame}
    (h : g₁.acceptedDraw ≠ g₂.acceptedDraw) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.acceptedDraw hg)

/-- Two finished games that differ only in their technical termination
are distinct. -/
theorem ne_of_technical_ne {g₁ g₂ : FinishedGame}
    (h : g₁.technical ≠ g₂.technical) :
    g₁ ≠ g₂ := by
  intro hg
  exact h (congrArg FinishedGame.technical hg)

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

/-- Record a draw proposal. Earlier declined proposals are kept, so a
player — including the opponent — may propose again on a later turn. -/
def proposeDraw (g : FinishedGame) (p : DrawProposal) : FinishedGame :=
  { g with drawProposals := g.drawProposals ++ [p] }

@[simp] theorem proposeDraw_drawProposals (g : FinishedGame) (p : DrawProposal) :
    (g.proposeDraw p).drawProposals = g.drawProposals ++ [p] := rfl

@[simp] theorem proposeDraw_acceptedDraw (g : FinishedGame) (p : DrawProposal) :
    (g.proposeDraw p).acceptedDraw = g.acceptedDraw := rfl

/-- Appending a proposal yields a different finished game. -/
theorem proposeDraw_ne (g : FinishedGame) (p : DrawProposal) :
    g.proposeDraw p ≠ g := by
  intro h
  have := congrArg FinishedGame.drawProposals h
  simp at this

/-- Two successive proposals are recorded in order. -/
theorem proposeDraw_proposeDraw (g : FinishedGame) (p₁ p₂ : DrawProposal) :
    ((g.proposeDraw p₁).proposeDraw p₂).drawProposals =
      g.drawProposals ++ [p₁, p₂] := by
  simp [proposeDraw]

/-- Proposing a draw yields a different finished game from one that
records no proposal, even when the positions and outcome agree. -/
theorem starting_proposeDraw_ne (p : DrawProposal) :
    startingDraw.proposeDraw p ≠ startingDraw :=
  proposeDraw_ne _ _

/-- Who proposed is part of the identity of a draw offer. -/
theorem starting_proposeDraw_proposer_ne (t : Nat) :
    startingDraw.proposeDraw { proposer := .white, turn := t } ≠
      startingDraw.proposeDraw { proposer := .black, turn := t } := by
  apply ne_of_drawProposals_ne
  simp

/-- The turn of a proposal is part of its identity. -/
theorem starting_proposeDraw_turn_ne (c : Color) {t₁ t₂ : Nat} (h : t₁ ≠ t₂) :
    startingDraw.proposeDraw { proposer := c, turn := t₁ } ≠
      startingDraw.proposeDraw { proposer := c, turn := t₂ } := by
  apply ne_of_drawProposals_ne
  simpa using h

/-- If a draw is not accepted, a further proposal — possibly by the other
player, on a later turn — is a different finished game. -/
theorem starting_proposeDraw_again_ne (p₁ p₂ : DrawProposal) :
    (startingDraw.proposeDraw p₁).proposeDraw p₂ ≠
      startingDraw.proposeDraw p₁ :=
  proposeDraw_ne _ _

/-- Accepting a draw yields a different finished game from one that
records no acceptance, even when the positions and outcome agree. -/
theorem starting_acceptedDraw_ne :
    { startingDraw with acceptedDraw := true } ≠ startingDraw :=
  ne_of_acceptedDraw_ne (by decide)

/-- Flag fall yields a different finished game from one that did not end
technically, even when the positions and outcome agree. -/
theorem starting_timer_ne :
    { ofGameState .starting (.win .white) with technical := some .timer } ≠
      ofGameState .starting (.win .white) :=
  ne_of_technical_ne (by decide)

/-- Another technical finish is likewise distinct from no technical
termination. -/
theorem starting_other_technical_ne :
    { ofGameState .starting (.win .white) with technical := some .other } ≠
      ofGameState .starting (.win .white) :=
  ne_of_technical_ne (by decide)

/-- A non-timer technical finish is distinct from flag fall. -/
theorem starting_timer_ne_other :
    { ofGameState .starting (.win .white) with technical := some .timer } ≠
      { ofGameState .starting (.win .white) with technical := some .other } :=
  ne_of_technical_ne (by decide)

/-- Advancing the underlying game yields a different finished game. -/
theorem ofGameState_advance_ne (p : Position) (o : GameOutcome) :
    ofGameState (GameState.starting.advance p) o ≠
      ofGameState .starting o :=
  ne_of_positions_ne (by simp [GameState.advance_positions])

end FinishedGame

end Chess
