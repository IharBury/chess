import Chess.DecideTheorems

/-!
# Deciding whether an action ends the game

`GameState.endsGame` is a Boolean that matches `EndsGame` whenever every
move the action plays leads to a valid position
(`endsGame_eq_true_iff`). Resignation, accepting a draw, and draw
claims always end the game. A plain move or a move with a draw offer
ends the game when it checkmates, stalemates, produces a dead position,
fivefold repetition, or the 75-move rule; deadness is `checkmateVerdict`
on the resulting position. Together these give
`GameState.endsGameDecidable`.
-/

namespace Chess

namespace GameState

open Position hiding kingsOnly starting

/-- Whether playing `m` in `g` ends the game: checkmate, stalemate, a
dead position, fivefold repetition, or the 75-move rule. -/
def endsGameMove (g : GameState) (m : Move) : Bool :=
  let p := g.current.play m
  p.inCheckmate || p.inStalemate || appearsFivefoldAfter g m ||
    leadsToSeventyFiveMove g m || !checkmateVerdict p

/-- Whether `a` ends the unfinished game `g`. Claims, resignation, and
accepting a draw always do; a move is delegated to `endsGameMove`. -/
def endsGame (g : GameState) : Action → Bool
  | .move m | .moveAndProposeDraw m => endsGameMove g m
  | .surrender | .acceptDraw | .claimRepetition | .claimNoProgress
  | .moveAndClaimRepetition _ | .moveAndClaimNoProgress _ => true

/-- The hypothesis `endsGameDecidable` needs: a played move must leave a
valid position, so that `DeadPosition` is `checkmateVerdict`. -/
def endsGameHyp (g : GameState) : Action → Prop
  | .move m | .moveAndProposeDraw m => Valid (g.current.play m)
  | _ => True

theorem endsGameHyp_move (g : GameState) (m : Move)
    (hv : Valid (g.current.play m)) : endsGameHyp g (.move m) :=
  hv

theorem endsGameHyp_moveAndProposeDraw (g : GameState) (m : Move)
    (hv : Valid (g.current.play m)) : endsGameHyp g (.moveAndProposeDraw m) :=
  hv

theorem endsGameMove_eq_true_iff (g : GameState) (m : Move)
    (hv : Valid (g.current.play m)) :
    endsGameMove g m = true ↔
      InCheckmate (g.current.play m) ∨
      InStalemate (g.current.play m) ∨
      AppearsFivefoldAfter g m ∨
      LeadsToSeventyFiveMove g m ∨
      DeadPosition (g.current.play m) := by
  unfold endsGameMove
  simp only [Bool.or_eq_true, inCheckmate_eq_true_iff, inStalemate_eq_true_iff,
    appearsFivefoldAfter_eq_true_iff, leadsToSeventyFiveMove_eq_true_iff]
  rw [not_checkmateVerdict_iff_deadPosition hv]
  simp [or_assoc]

/-- `endsGame` agrees with `EndsGame` when every move `a` plays leaves a
valid position. -/
theorem endsGame_eq_true_iff (g : GameState) (a : Action)
    (hv : endsGameHyp g a) :
    endsGame g a = true ↔ EndsGame g a := by
  cases a with
  | move m =>
    unfold endsGame
    rw [endsGameMove_eq_true_iff g m hv, EndsGame_move_iff]
  | moveAndProposeDraw m =>
    unfold endsGame
    rw [endsGameMove_eq_true_iff g m hv, EndsGame_moveAndProposeDraw_iff]
  | surrender =>
    constructor
    · intro
      exact surrender_endsGame g
    · intro
      rfl
  | acceptDraw =>
    constructor
    · intro
      exact acceptDraw_endsGame g
    · intro
      rfl
  | claimRepetition =>
    constructor
    · intro
      exact claimRepetition_endsGame g
    · intro
      rfl
  | claimNoProgress =>
    constructor
    · intro
      exact claimNoProgress_endsGame g
    · intro
      rfl
  | moveAndClaimRepetition m =>
    constructor
    · intro
      exact moveAndClaimRepetition_endsGame g m
    · intro
      rfl
  | moveAndClaimNoProgress m =>
    constructor
    · intro
      exact moveAndClaimNoProgress_endsGame g m
    · intro
      rfl

/-- Decides whether `a` ends the game `g`. When `a` plays a move, the
resulting position must be valid. -/
def endsGameDecidable (g : GameState) (a : Action) (hv : endsGameHyp g a) :
    Decidable (EndsGame g a) :=
  decidable_of_iff (endsGame g a = true) (endsGame_eq_true_iff g a hv)

/-! ### Examples -/

theorem starting_e2e4_play_isValid :
    isValid (starting.current.play (Move.std Square.e2 Square.e4)) = true := by
  native_decide

theorem starting_e2e4_play_valid :
    Valid (starting.current.play (Move.std Square.e2 Square.e4)) :=
  (isValid_eq_true_iff _).mp starting_e2e4_play_isValid

/-- White's `e2–e4` at the start does not end the game: Scholar's mate is
reachable, so the position is not dead, and the move is not mate,
stalemate, fivefold, or the 75-move rule. -/
theorem starting_e2e4_endsGame_eq :
    endsGame starting (Action.move (Move.std Square.e2 Square.e4)) = false :=
  Bool.eq_false_iff.mpr
    (mt (endsGame_eq_true_iff starting _
        (endsGameHyp_move _ _ starting_e2e4_play_valid)).mp
      starting_e2e4_not_endsGame)

theorem starting_surrender_decide :
    @decide (EndsGame starting .surrender)
      (endsGameDecidable starting .surrender trivial) = true := by
  native_decide

theorem starting_claimRepetition_decide :
    @decide (EndsGame starting .claimRepetition)
      (endsGameDecidable starting .claimRepetition trivial) = true := by
  native_decide

theorem beforeQueenMate_qh7_play_isValid :
    isValid (beforeQueenMate.play (Move.std Square.e7 Square.h7)) = true := by
  native_decide

theorem beforeQueenMate_qh7_decide :
    @decide (EndsGame beforeQueenMateGame (Action.move (Move.std Square.e7 Square.h7)))
      (endsGameDecidable beforeQueenMateGame _
        ((isValid_eq_true_iff _).mp beforeQueenMate_qh7_play_isValid)) = true := by
  native_decide

theorem beforeQueenMate_qh7_proposeDraw_decide :
    @decide (EndsGame beforeQueenMateGame
        (Action.moveAndProposeDraw (Move.std Square.e7 Square.h7)))
      (endsGameDecidable beforeQueenMateGame _
        (endsGameHyp_moveAndProposeDraw _ _
          ((isValid_eq_true_iff _).mp beforeQueenMate_qh7_play_isValid))) = true := by
  native_decide

theorem beforeStalemate_a7_play_isValid :
    isValid (beforeStalemate.play (Move.std Square.a6 Square.a7)) = true := by
  native_decide

theorem beforeStalemate_a7_decide :
    @decide (EndsGame beforeStalemateGame (Action.move (Move.std Square.a6 Square.a7)))
      (endsGameDecidable beforeStalemateGame _
        ((isValid_eq_true_iff _).mp beforeStalemate_a7_play_isValid)) = true := by
  native_decide

theorem kingsOnly_e1d1_play_isValid :
    isValid (kingsOnly.play (Move.std Square.e1 Square.d1)) = true := by
  native_decide

theorem kingsOnly_e1d1_decide :
    @decide (EndsGame kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)))
      (endsGameDecidable kingsOnlyGame _
        ((isValid_eq_true_iff _).mp kingsOnly_e1d1_play_isValid)) = true := by
  native_decide

theorem fivefoldBeforeE4_play_isValid :
    isValid (fivefoldBeforeE4.current.play (Move.std Square.e2 Square.e4)) = true := by
  native_decide

theorem fivefoldBeforeE4_decide :
    @decide (EndsGame fivefoldBeforeE4 (Action.move (Move.std Square.e2 Square.e4)))
      (endsGameDecidable fivefoldBeforeE4 _
        ((isValid_eq_true_iff _).mp fivefoldBeforeE4_play_isValid)) = true := by
  native_decide

theorem kingsOnly_149_e1d1_decide :
    @decide (EndsGame (repeated kingsOnly 149)
        (Action.move (Move.std Square.e1 Square.d1)))
      (endsGameDecidable (repeated kingsOnly 149) _
        ((isValid_eq_true_iff _).mp kingsOnly_e1d1_play_isValid)) = true := by
  native_decide

theorem afterE2e4e7e5Offer_acceptDraw_decide :
    @decide (EndsGame afterE2e4e7e5Offer .acceptDraw)
      (endsGameDecidable afterE2e4e7e5Offer .acceptDraw trivial) = true := by
  native_decide

end GameState

end Chess
