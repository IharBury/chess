import Chess.EndsGameTheorems
import Chess.FinishedGame

/-!
# Playing an action

Carrying out an action in an unfinished game either produces the next
game state, or finishes the game. `GameState.after` is that transition:
a move that does not end play is recorded with `GameState.advance`
(and a draw offer, if the action proposes one); an ending action is
recorded as `FinishedGame.ofActionRecord`.
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

/-- Carry out `a` in the unfinished game `g`.

If `a` ends the game (`endsGame`), the result is the completed game
`FinishedGame.ofActionRecord g a`. Otherwise it is the next unfinished
state `continueAfter g a`. Legality of `a` is not checked. -/
def after (g : GameState) (a : Action) : AfterAction :=
  if endsGame g a then
    .finished (ofActionRecord g a)
  else
    .continuing (continueAfter g a)

theorem after_eq_finished (g : GameState) (a : Action)
    (h : endsGame g a = true) :
    after g a = .finished (ofActionRecord g a) := by
  simp [after, h]

theorem after_eq_continuing (g : GameState) (a : Action)
    (h : endsGame g a = false) :
    after g a = .continuing (continueAfter g a) := by
  simp [after, h]

/-- When `EndsGame` is decidable from `endsGameHyp`, an ending action
produces `ofAction`. -/
theorem after_eq_finished_ofAction (g : GameState) (a : Action)
    (h : EndsGame g a) (hv : endsGameHyp g a) :
    after g a = .finished (ofAction g a h) := by
  have ht : endsGame g a = true := (endsGame_eq_true_iff g a hv).mpr h
  simp [after_eq_finished g a ht, ofAction_eq_ofActionRecord]

/-- When `EndsGame` is decidable from `endsGameHyp`, a non-ending action
produces the next unfinished game. -/
theorem after_eq_continuing_of_not_EndsGame (g : GameState) (a : Action)
    (h : ¬ EndsGame g a) (hv : endsGameHyp g a) :
    after g a = .continuing (continueAfter g a) := by
  have hf : endsGame g a = false :=
    Bool.eq_false_iff.mpr (mt (endsGame_eq_true_iff g a hv).mp h)
  exact after_eq_continuing g a hf

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

/-- `after` finishes the game exactly when `endsGame` is true. -/
theorem after_isFinished_iff (g : GameState) (a : Action) :
    (after g a).isFinished = true ↔ endsGame g a = true := by
  unfold after
  cases endsGame g a <;> simp

/-- When the resulting position of a played move is valid, `after`
finishes the game exactly when `EndsGame` holds. -/
theorem after_isFinished_iff_EndsGame (g : GameState) (a : Action)
    (hv : endsGameHyp g a) :
    (after g a).isFinished = true ↔ EndsGame g a := by
  rw [after_isFinished_iff, endsGame_eq_true_iff g a hv]

/-! ### Examples -/

/-- White's `e2–e4` at the start continues the game: the next state is
the position after that pawn move, with no pending draw offer. -/
theorem after_starting_e2e4 :
    after starting (Action.move (Move.std Square.e2 Square.e4)) =
      .continuing afterE2e4 := by
  rw [after_eq_continuing _ _ starting_e2e4_endsGame_eq]
  simp [afterE2e4]

/-- Resigning at the start finishes the game as a win for Black. -/
theorem after_starting_surrender :
    after starting .surrender =
      .finished (ofAction starting .surrender starting_surrender_endsGame) :=
  after_eq_finished_ofAction _ _ starting_surrender_endsGame trivial

theorem after_starting_surrender_isFinished :
    (after starting .surrender).isFinished = true :=
  rfl

theorem after_starting_e2e4_isContinuing :
    (after starting (Action.move (Move.std Square.e2 Square.e4))).isContinuing =
      true := by
  simp [after_starting_e2e4]

/-- Playing `e2–e4` and resigning from the start are different results:
one continues, the other finishes. -/
theorem after_starting_e2e4_ne_surrender :
    after starting (Action.move (Move.std Square.e2 Square.e4)) ≠
      after starting .surrender := by
  rw [after_starting_e2e4, after_starting_surrender]
  exact AfterAction.continuing_ne_finished _ _

/-- Accepting a pending draw after `1. e4 e5` finishes as a drawn game. -/
theorem after_afterE2e4e7e5Offer_acceptDraw :
    after afterE2e4e7e5Offer .acceptDraw =
      .finished (ofAction afterE2e4e7e5Offer .acceptDraw
        afterE2e4e7e5Offer_acceptDraw_endsGame) :=
  after_eq_finished_ofAction _ _ afterE2e4e7e5Offer_acceptDraw_endsGame trivial

/-- Claiming threefold repetition finishes as a draw. -/
theorem after_threefoldStarting_claimRepetition :
    after threefoldStarting .claimRepetition =
      .finished (ofAction threefoldStarting .claimRepetition
        (claimRepetition_endsGame _)) :=
  after_eq_finished_ofAction _ _ (claimRepetition_endsGame _) trivial

/-- A fifty-move claim in a quiet two-king game finishes as a draw. -/
theorem after_kingsOnly_100_claimNoProgress :
    after (repeated kingsOnly 100) .claimNoProgress =
      .finished (ofAction (repeated kingsOnly 100) .claimNoProgress
        (claimNoProgress_endsGame _)) :=
  after_eq_finished_ofAction _ _ (claimNoProgress_endsGame _) trivial

/-- Playing `Qh7` from `beforeQueenMate` finishes as a win for White. -/
theorem after_beforeQueenMate_qh7 :
    after beforeQueenMateGame (Action.move (Move.std Square.h4 Square.h7)) =
      .finished (ofAction beforeQueenMateGame
        (Action.move (Move.std Square.h4 Square.h7))
        beforeQueenMate_qh7_endsGame) :=
  after_eq_finished_ofAction _ _ beforeQueenMate_qh7_endsGame
    ((isValid_eq_true_iff _).mp beforeQueenMate_qh7_play_isValid)

/-- Playing `a6–a7` from `beforeStalemate` finishes as a draw. -/
theorem after_beforeStalemate_a7 :
    after beforeStalemateGame (Action.move (Move.std Square.a6 Square.a7)) =
      .finished (ofAction beforeStalemateGame
        (Action.move (Move.std Square.a6 Square.a7))
        beforeStalemate_a7_endsGame) :=
  after_eq_finished_ofAction _ _ beforeStalemate_a7_endsGame
    ((isValid_eq_true_iff _).mp beforeStalemate_a7_play_isValid)

/-- A king move with only two kings finishes: the resulting position is
dead. -/
theorem after_kingsOnly_e1d1 :
    after kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)) =
      .finished (ofAction kingsOnlyGame
        (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_e1d1_endsGame) :=
  after_eq_finished_ofAction _ _ kingsOnly_e1d1_endsGame
    ((isValid_eq_true_iff _).mp kingsOnly_e1d1_play_isValid)

/-- Playing `e2–e4` into a fifth occurrence finishes as a draw. -/
theorem after_fivefoldBeforeE4 :
    after fivefoldBeforeE4 (Action.move (Move.std Square.e2 Square.e4)) =
      .finished (ofAction fivefoldBeforeE4
        (Action.move (Move.std Square.e2 Square.e4))
        fivefoldBeforeE4_endsGame) :=
  after_eq_finished_ofAction _ _ fivefoldBeforeE4_endsGame
    ((isValid_eq_true_iff _).mp fivefoldBeforeE4_play_isValid)

/-- A quiet king move after 149 quiet plies finishes by the 75-move
rule. -/
theorem after_kingsOnly_149_e1d1 :
    after (repeated kingsOnly 149) (Action.move (Move.std Square.e1 Square.d1)) =
      .finished (ofAction (repeated kingsOnly 149)
        (Action.move (Move.std Square.e1 Square.d1))
        kingsOnly_149_e1d1_endsGame) :=
  after_eq_finished_ofAction _ _ kingsOnly_149_e1d1_endsGame
    ((isValid_eq_true_iff _).mp kingsOnly_e1d1_play_isValid)

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

theorem afterE2e4_e7e5_play_isValid :
    isValid (afterE2e4.current.play (Move.std Square.e7 Square.e5)) = true := by
  native_decide

theorem afterE2e4_e7e5_play_valid :
    Valid (afterE2e4.current.play (Move.std Square.e7 Square.e5)) :=
  (isValid_eq_true_iff _).mp afterE2e4_e7e5_play_isValid

theorem afterE2e4_e7e5_proposeDraw_endsGame_eq :
    endsGame afterE2e4
        (Action.moveAndProposeDraw (Move.std Square.e7 Square.e5)) =
      false :=
  Bool.eq_false_iff.mpr
    (mt (endsGame_eq_true_iff afterE2e4 _
        (endsGameHyp_moveAndProposeDraw _ _ afterE2e4_e7e5_play_valid)).mp
      afterE2e4_e7e5_proposeDraw_not_endsGame)

/-- After `1. e4`, Black playing `e7–e5` and offering a draw continues
the game with that offer pending. -/
theorem after_afterE2e4_e7e5_proposeDraw :
    after afterE2e4
        (Action.moveAndProposeDraw (Move.std Square.e7 Square.e5)) =
      .continuing afterE2e4e7e5Offer := by
  rw [after_eq_continuing _ _ afterE2e4_e7e5_proposeDraw_endsGame_eq]
  simp [afterE2e4e7e5Offer, afterE2e4]

end GameState

end Chess
