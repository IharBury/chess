import Chess.EndsGameTheorems
import Chess.FinishedGame

/-!
# Playing an action

Carrying out a legal action in a valid unfinished game either produces
the next game state, or finishes the game. `GameState.after` is that
transition: a move that does not end play is recorded with
`GameState.advance` (and a draw offer, if the action proposes one); an
ending action is recorded as `FinishedGame.ofAction`. The game is
assumed valid and the action legal, so `EndsGame` is decidable.
-/

namespace Chess

/-- The result of carrying out an action in an unfinished game: either
the next game state, or a completed game. -/
inductive AfterAction where
  /-- The action did not end the game; play continues from `g`. -/
  | continuing (g : GameState)
  /-- The action ended the game. -/
  | finished (fg : FinishedGame)
deriving Inhabited

namespace AfterAction

/-- A continuing game is not a finished one. -/
theorem continuing_ne_finished (g : GameState) (fg : FinishedGame) :
    continuing g ≠ finished fg := by
  intro h
  cases h

/-- Whether this result is an unfinished game. -/
def isContinuing : AfterAction → Bool
  | continuing _ => true
  | finished _ => false

/-- Whether this result is a completed game. -/
def isFinished : AfterAction → Bool
  | finished _ => true
  | continuing _ => false

@[simp] theorem isContinuing_continuing (g : GameState) :
    isContinuing (continuing g) = true := rfl

@[simp] theorem isContinuing_finished (fg : FinishedGame) :
    isContinuing (finished fg) = false := rfl

@[simp] theorem isFinished_finished (fg : FinishedGame) :
    isFinished (finished fg) = true := rfl

@[simp] theorem isFinished_continuing (g : GameState) :
    isFinished (continuing g) = false := rfl

/-- The unfinished game, if play continues. -/
def gameState? : AfterAction → Option GameState
  | continuing g => some g
  | finished _ => none

/-- The completed game, if the action ended play. -/
def finishedGame? : AfterAction → Option FinishedGame
  | finished fg => some fg
  | continuing _ => none

@[simp] theorem gameState?_continuing (g : GameState) :
    (continuing g).gameState? = some g := rfl

@[simp] theorem gameState?_finished (fg : FinishedGame) :
    (finished fg).gameState? = none := rfl

@[simp] theorem finishedGame?_finished (fg : FinishedGame) :
    (finished fg).finishedGame? = some fg := rfl

@[simp] theorem finishedGame?_continuing (g : GameState) :
    (continuing g).finishedGame? = none := rfl

end AfterAction

namespace GameState

open FinishedGame
open Position hiding kingsOnly starting

/-- The next unfinished game after carrying out `a`.

A played move is appended with `advance`; a draw offer is recorded
when `a` proposes one. Actions that play no move leave `g` unchanged
(those actions always end the game, so `after` does not use this
branch). -/
def continueAfter (g : GameState) (a : Action) : GameState :=
  match a.move? with
  | some m => g.advance (g.current.play m) a.proposesDraw
  | none => g

@[simp] theorem continueAfter_move (g : GameState) (m : Move) :
    continueAfter g (.move m) = g.advance (g.current.play m) :=
  rfl

@[simp] theorem continueAfter_moveAndProposeDraw (g : GameState) (m : Move) :
    continueAfter g (.moveAndProposeDraw m) =
      g.advance (g.current.play m) true :=
  rfl

@[simp] theorem continueAfter_surrender (g : GameState) :
    continueAfter g .surrender = g :=
  rfl

@[simp] theorem continueAfter_acceptDraw (g : GameState) :
    continueAfter g .acceptDraw = g :=
  rfl

@[simp] theorem continueAfter_claimRepetition (g : GameState) :
    continueAfter g .claimRepetition = g :=
  rfl

@[simp] theorem continueAfter_claimNoProgress (g : GameState) :
    continueAfter g .claimNoProgress = g :=
  rfl

@[simp] theorem continueAfter_moveAndClaimRepetition (g : GameState) (m : Move) :
    continueAfter g (.moveAndClaimRepetition m) =
      g.advance (g.current.play m) :=
  rfl

@[simp] theorem continueAfter_moveAndClaimNoProgress (g : GameState) (m : Move) :
    continueAfter g (.moveAndClaimNoProgress m) =
      g.advance (g.current.play m) :=
  rfl

/-- If `a` plays `m`, continuing after `a` is advancing to the position
after `m`, recording a draw offer exactly when `a` proposes one. -/
theorem continueAfter_of_plays (g : GameState) {a : Action} {m : Move}
    (hp : a.Plays m) :
    continueAfter g a = g.advance (g.current.play m) a.proposesDraw := by
  simp [Action.Plays] at hp
  simp [continueAfter, hp]

/-- Carry out legal action `a` in the unfinished valid game `g`.

If `a` ends the game, the result is `FinishedGame.ofAction g a`.
Otherwise it is the next unfinished state `continueAfter g a`. -/
def after (g : GameState) (a : Action)
    (hg : Valid g.current) (ha : LegalAction g a) : AfterAction :=
  match endsGameDecidable g a hg ha with
  | .isTrue h => .finished (ofAction g a h)
  | .isFalse _ => .continuing (continueAfter g a)

/-- An ending action produces `ofAction`. -/
theorem after_eq_finished (g : GameState) (a : Action)
    (h : EndsGame g a) (hg : Valid g.current) (ha : LegalAction g a) :
    after g a hg ha = .finished (ofAction g a h) := by
  unfold after
  cases endsGameDecidable g a hg ha with
  | isTrue _ => rfl
  | isFalse hn => exact (hn h).elim

/-- A non-ending action produces the next unfinished game. -/
theorem after_eq_continuing (g : GameState) (a : Action)
    (h : ¬ EndsGame g a) (hg : Valid g.current) (ha : LegalAction g a) :
    after g a hg ha = .continuing (continueAfter g a) := by
  unfold after
  cases endsGameDecidable g a hg ha with
  | isTrue ht => exact (h ht).elim
  | isFalse _ => rfl

/-- An action that does not end the game plays a move: resignation,
acceptance, and draw claims always end play. -/
theorem exists_plays_of_not_EndsGame {g : GameState} {a : Action}
    (h : ¬ EndsGame g a) : ∃ m, a.Plays m := by
  cases a with
  | move m => exact ⟨m, Action.plays_move m⟩
  | moveAndProposeDraw m => exact ⟨m, Action.plays_moveAndProposeDraw m⟩
  | surrender => exact (h (surrender_endsGame g)).elim
  | acceptDraw => exact (h (acceptDraw_endsGame g)).elim
  | claimRepetition => exact (h (claimRepetition_endsGame g)).elim
  | claimNoProgress => exact (h (claimNoProgress_endsGame g)).elim
  | moveAndClaimRepetition m =>
    exact (h (moveAndClaimRepetition_endsGame g m)).elim
  | moveAndClaimNoProgress m =>
    exact (h (moveAndClaimNoProgress_endsGame g m)).elim

/-- `after` finishes the game exactly when `EndsGame` holds. -/
theorem after_isFinished_iff (g : GameState) (a : Action)
    (hg : Valid g.current) (ha : LegalAction g a) :
    (after g a hg ha).isFinished = true ↔ EndsGame g a := by
  unfold after
  cases endsGameDecidable g a hg ha with
  | isTrue h => simp [h]
  | isFalse h => simp [h]

/-! ### Examples -/

/-- White's `e2–e4` at the start continues the game: the next state is
the position after that pawn move, with no pending draw offer. -/
theorem after_starting_e2e4 :
    after starting (Action.move (Move.std Square.e2 Square.e4))
        starting_current_valid starting_e2e4_legalAction =
      .continuing afterE2e4 := by
  rw [after_eq_continuing _ _ starting_e2e4_not_endsGame]
  simp [afterE2e4]

/-- Resigning at the start finishes the game as a win for Black. -/
theorem after_starting_surrender :
    after starting .surrender starting_current_valid (surrender_legal _) =
      .finished (ofAction starting .surrender starting_surrender_endsGame) :=
  after_eq_finished _ _ starting_surrender_endsGame starting_current_valid
    (surrender_legal _)

theorem after_starting_surrender_isFinished :
    (after starting .surrender starting_current_valid (surrender_legal _)).isFinished =
      true := by
  simp [after_starting_surrender]

theorem after_starting_e2e4_isContinuing :
    (after starting (Action.move (Move.std Square.e2 Square.e4))
      starting_current_valid starting_e2e4_legalAction).isContinuing = true := by
  simp [after_starting_e2e4]

/-- Playing `e2–e4` and resigning from the start are different results:
one continues, the other finishes. -/
theorem after_starting_e2e4_ne_surrender :
    after starting (Action.move (Move.std Square.e2 Square.e4))
        starting_current_valid starting_e2e4_legalAction ≠
      after starting .surrender starting_current_valid (surrender_legal _) := by
  rw [after_starting_e2e4, after_starting_surrender]
  exact AfterAction.continuing_ne_finished _ _

/-- Accepting a pending draw after `1. e4 e5` finishes as a drawn game. -/
theorem after_afterE2e4e7e5Offer_acceptDraw :
    after afterE2e4e7e5Offer .acceptDraw afterE2e4e7e5Offer_valid
        afterE2e4e7e5Offer_acceptDraw_legal =
      .finished (ofAction afterE2e4e7e5Offer .acceptDraw
        afterE2e4e7e5Offer_acceptDraw_endsGame) :=
  after_eq_finished _ _ afterE2e4e7e5Offer_acceptDraw_endsGame
    afterE2e4e7e5Offer_valid afterE2e4e7e5Offer_acceptDraw_legal

/-- Claiming threefold repetition finishes as a draw. -/
theorem after_threefoldStarting_claimRepetition :
    after threefoldStarting .claimRepetition threefoldStarting_valid
        threefoldStarting_claimRepetition_legal =
      .finished (ofAction threefoldStarting .claimRepetition
        (claimRepetition_endsGame _)) :=
  after_eq_finished _ _ (claimRepetition_endsGame _)
    threefoldStarting_valid threefoldStarting_claimRepetition_legal

theorem kingsOnly_100_claimNoProgress_legal :
    LegalAction (repeated kingsOnly 100) .claimNoProgress := by
  unfold LegalAction isLegalAction
  exact repeated_noProgress kingsOnly (Nat.le_refl noProgressPlies)

/-- A fifty-move claim in a quiet two-king game finishes as a draw. -/
theorem after_kingsOnly_100_claimNoProgress :
    after (repeated kingsOnly 100) .claimNoProgress kingsOnly_valid
        kingsOnly_100_claimNoProgress_legal =
      .finished (ofAction (repeated kingsOnly 100) .claimNoProgress
        (claimNoProgress_endsGame _)) :=
  after_eq_finished _ _ (claimNoProgress_endsGame _) kingsOnly_valid
    kingsOnly_100_claimNoProgress_legal

/-- Playing `Qh7` from `beforeQueenMate` finishes as a win for White. -/
theorem after_beforeQueenMate_qh7 :
    after beforeQueenMateGame (Action.move (Move.std Square.e7 Square.h7))
        beforeQueenMate_valid beforeQueenMate_qh7_legalAction =
      .finished (ofAction beforeQueenMateGame
        (Action.move (Move.std Square.e7 Square.h7))
        beforeQueenMate_qh7_endsGame) :=
  after_eq_finished _ _ beforeQueenMate_qh7_endsGame
    beforeQueenMate_valid beforeQueenMate_qh7_legalAction

/-- Playing `a6–a7` from `beforeStalemate` finishes as a draw. -/
theorem after_beforeStalemate_a7 :
    after beforeStalemateGame (Action.move (Move.std Square.a6 Square.a7))
        beforeStalemate_valid beforeStalemate_a7_legalAction =
      .finished (ofAction beforeStalemateGame
        (Action.move (Move.std Square.a6 Square.a7))
        beforeStalemate_a7_endsGame) :=
  after_eq_finished _ _ beforeStalemate_a7_endsGame
    beforeStalemate_valid beforeStalemate_a7_legalAction

/-- A king move with only two kings finishes: the resulting position is
dead. -/
theorem after_kingsOnly_e1d1 :
    after kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_valid (kingsOnly_e1d1_legalAction 0) =
      .finished (ofAction kingsOnlyGame
        (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_e1d1_endsGame) :=
  after_eq_finished _ _ kingsOnly_e1d1_endsGame
    kingsOnly_valid (kingsOnly_e1d1_legalAction 0)

/-- Playing `e2–e4` into a fifth occurrence finishes as a draw. -/
theorem after_fivefoldBeforeE4 :
    after fivefoldBeforeE4 (Action.move (Move.std Square.e2 Square.e4))
        fivefoldBeforeE4_valid fivefoldBeforeE4_e2e4_legalAction =
      .finished (ofAction fivefoldBeforeE4
        (Action.move (Move.std Square.e2 Square.e4))
        fivefoldBeforeE4_endsGame) :=
  after_eq_finished _ _ fivefoldBeforeE4_endsGame
    fivefoldBeforeE4_valid fivefoldBeforeE4_e2e4_legalAction

/-- A quiet king move after 149 quiet plies finishes by the 75-move
rule. -/
theorem after_kingsOnly_149_e1d1 :
    after (repeated kingsOnly 149) (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_valid (kingsOnly_e1d1_legalAction 149) =
      .finished (ofAction (repeated kingsOnly 149)
        (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_149_e1d1_endsGame) :=
  after_eq_finished _ _ kingsOnly_149_e1d1_endsGame
    kingsOnly_valid (kingsOnly_e1d1_legalAction 149)

/-! ### Offering a draw with a move that does not end the game -/

/-- Black's `e7–e5` after `1. e4` does not checkmate. -/
theorem afterE2e4_e7e5_not_inCheckmate :
    ¬ InCheckmate (afterE2e4.current.play (Move.std Square.e7 Square.e5)) := by
  native_decide

/-- Black's `e7–e5` after `1. e4` does not stalemate. -/
theorem afterE2e4_e7e5_not_inStalemate :
    ¬ InStalemate (afterE2e4.current.play (Move.std Square.e7 Square.e5)) := by
  native_decide

/-- Black's `e7–e5` after `1. e4` is not a fifth occurrence. -/
theorem afterE2e4_e7e5_not_fivefold :
    ¬ AppearsFivefoldAfter afterE2e4 (Move.std Square.e7 Square.e5) := by
  native_decide

/-- Black's `e7–e5` after `1. e4` is a pawn move, so it does not complete
75 quiet moves. -/
theorem afterE2e4_e7e5_not_seventyFive :
    ¬ LeadsToSeventyFiveMove afterE2e4 (Move.std Square.e7 Square.e5) := by
  native_decide

/-- The rest of Scholar's mate after `1. e4 e5`. -/
def scholarsMateAfterE4e5 : List Move :=
  scholarsMateAfterE4.tail

theorem scholarsMateAfterE4e5_legal :
    LegalSeq (afterE2e4.current.play (Move.std Square.e7 Square.e5))
      scholarsMateAfterE4e5 :=
  scholarsMateAfterE4_legal.2

theorem scholarsMateAfterE4e5_inCheckmate :
    InCheckmate
      (playSeq (afterE2e4.current.play (Move.std Square.e7 Square.e5))
        scholarsMateAfterE4e5) :=
  scholarsMateAfterE4_inCheckmate

/-- After `1. e4 e5` the position is not dead: Scholar's mate is still
reachable. -/
theorem afterE2e4_e7e5_not_deadPosition :
    ¬ DeadPosition (afterE2e4.current.play (Move.std Square.e7 Square.e5)) :=
  not_deadPosition_of_legalSeq scholarsMateAfterE4e5_legal
    scholarsMateAfterE4e5_inCheckmate

/-- Black's `e7–e5` with a draw offer after `1. e4` does not end the
game. -/
theorem afterE2e4_e7e5_proposeDraw_not_endsGame :
    ¬ EndsGame afterE2e4
        (Action.moveAndProposeDraw (Move.std Square.e7 Square.e5)) := by
  intro h
  have hiff :=
    EndsGame_moveAndProposeDraw_iff afterE2e4 (Move.std Square.e7 Square.e5)
  rcases hiff.mp h with hc | hs | hf | h75 | hd
  · exact afterE2e4_e7e5_not_inCheckmate hc
  · exact afterE2e4_e7e5_not_inStalemate hs
  · exact afterE2e4_e7e5_not_fivefold hf
  · exact afterE2e4_e7e5_not_seventyFive h75
  · exact afterE2e4_e7e5_not_deadPosition hd

theorem afterE2e4_e7e5_proposeDraw_legal :
    LegalAction afterE2e4
      (Action.moveAndProposeDraw (Move.std Square.e7 Square.e5)) := by
  native_decide

/-- After `1. e4`, Black playing `e7–e5` and offering a draw continues
the game with that offer pending. -/
theorem after_afterE2e4_e7e5_proposeDraw :
    after afterE2e4
        (Action.moveAndProposeDraw (Move.std Square.e7 Square.e5))
        afterE2e4_valid afterE2e4_e7e5_proposeDraw_legal =
      .continuing afterE2e4e7e5Offer := by
  rw [after_eq_continuing _ _ afterE2e4_e7e5_proposeDraw_not_endsGame]
  simp [afterE2e4e7e5Offer, afterE2e4]

end GameState

end Chess
