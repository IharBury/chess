import Chess.DecideTheorems
import Chess.ValidPlay

/-!
# Deciding whether an action ends the game

`GameState.endsGame` is a Boolean that matches `EndsGame` for a legal
action in a valid game (`endsGame_eq_true_iff`). Resignation, accepting
a draw, and draw claims always end the game. A plain move or a move with
a draw offer ends the game when it checkmates, stalemates, produces a
dead position, fivefold repetition, or the 75-move rule; deadness is
`checkmateVerdict` on the resulting position, which is valid by
`Position.valid_play`. Together these give `GameState.endsGameDecidable`.
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

/-- A legal action that plays `m` from a valid game leaves a valid
position. -/
theorem valid_play_of_LegalAction {g : GameState} {a : Action} {m : Move}
    (hg : Valid g.current) (ha : LegalAction g a) (hp : a.Plays m) :
    Valid (g.current.play m) := by
  cases a with
  | move m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    exact valid_play hg ha
  | moveAndProposeDraw m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    unfold LegalAction isLegalAction at ha
    exact valid_play hg (Bool.and_eq_true_iff.mp ha).1
  | moveAndClaimRepetition m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    unfold LegalAction isLegalAction at ha
    exact valid_play hg (Bool.and_eq_true_iff.mp ha).1
  | moveAndClaimNoProgress m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    unfold LegalAction isLegalAction at ha
    exact valid_play hg (Bool.and_eq_true_iff.mp ha).1
  | surrender | acceptDraw | claimRepetition | claimNoProgress =>
    cases hp

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

/-- `endsGame` agrees with `EndsGame` for a legal action in a valid
game. -/
theorem endsGame_eq_true_iff (g : GameState) (a : Action)
    (hg : Valid g.current) (ha : LegalAction g a) :
    endsGame g a = true ↔ EndsGame g a := by
  cases a with
  | move m =>
    unfold endsGame
    rw [endsGameMove_eq_true_iff g m
        (valid_play_of_LegalAction hg ha (Action.plays_move m)),
      EndsGame_move_iff]
  | moveAndProposeDraw m =>
    unfold endsGame
    rw [endsGameMove_eq_true_iff g m
        (valid_play_of_LegalAction hg ha (Action.plays_moveAndProposeDraw m)),
      EndsGame_moveAndProposeDraw_iff]
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

/-- Decides whether legal action `a` ends the valid unfinished game `g`. -/
def endsGameDecidable (g : GameState) (a : Action)
    (hg : Valid g.current) (ha : LegalAction g a) :
    Decidable (EndsGame g a) :=
  decidable_of_iff (endsGame g a = true) (endsGame_eq_true_iff g a hg ha)

/-! ### Examples -/

theorem starting_current_valid : Valid starting.current :=
  starting_current ▸ Position.starting_valid

theorem starting_e2e4_legalAction :
    LegalAction starting (Action.move (Move.std Square.e2 Square.e4)) :=
  starting_e2e4_legal

theorem starting_e2e4_play_valid :
    Valid (starting.current.play (Move.std Square.e2 Square.e4)) :=
  valid_play starting_current_valid starting_e2e4_legalAction

/-- White's `e2–e4` at the start does not end the game: Scholar's mate is
reachable, so the position is not dead, and the move is not mate,
stalemate, fivefold, or the 75-move rule. -/
theorem starting_e2e4_endsGame_eq :
    endsGame starting (Action.move (Move.std Square.e2 Square.e4)) = false :=
  Bool.eq_false_iff.mpr
    (mt (endsGame_eq_true_iff starting _
        starting_current_valid starting_e2e4_legalAction).mp
      starting_e2e4_not_endsGame)

theorem starting_surrender_decide :
    @decide (EndsGame starting .surrender)
      (endsGameDecidable starting .surrender starting_current_valid
        (surrender_legal _)) = true := by
  native_decide

theorem threefoldStarting_valid : Valid threefoldStarting.current :=
  starting_current_valid

theorem threefoldStarting_claimRepetition_legal :
    LegalAction threefoldStarting .claimRepetition := by
  native_decide

theorem threefoldStarting_claimRepetition_decide :
    @decide (EndsGame threefoldStarting .claimRepetition)
      (endsGameDecidable threefoldStarting .claimRepetition
        threefoldStarting_valid threefoldStarting_claimRepetition_legal) =
      true := by
  native_decide

theorem beforeQueenMate_valid : Valid beforeQueenMateGame.current := by
  native_decide

theorem beforeQueenMate_qh7_legalAction :
    LegalAction beforeQueenMateGame
      (Action.move (Move.std Square.e7 Square.h7)) := by
  native_decide

theorem beforeQueenMate_qh7_decide :
    @decide (EndsGame beforeQueenMateGame
        (Action.move (Move.std Square.e7 Square.h7)))
      (endsGameDecidable beforeQueenMateGame _
        beforeQueenMate_valid beforeQueenMate_qh7_legalAction) = true := by
  native_decide

theorem beforeStalemate_valid : Valid beforeStalemateGame.current := by
  native_decide

theorem beforeStalemate_a7_legalAction :
    LegalAction beforeStalemateGame
      (Action.move (Move.std Square.a6 Square.a7)) := by
  native_decide

theorem beforeStalemate_a7_decide :
    @decide (EndsGame beforeStalemateGame (Action.move (Move.std Square.a6 Square.a7)))
      (endsGameDecidable beforeStalemateGame _
        beforeStalemate_valid beforeStalemate_a7_legalAction) = true := by
  native_decide

theorem kingsOnly_valid : Valid kingsOnly := by
  native_decide

theorem kingsOnly_e1d1_legalAction (n : Nat) :
    LegalAction (repeated kingsOnly n)
      (Action.move (Move.std Square.e1 Square.d1)) :=
  kingsOnly_e1d1_legal

theorem kingsOnly_e1d1_decide :
    @decide (EndsGame kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)))
      (endsGameDecidable kingsOnlyGame _
        kingsOnly_valid (kingsOnly_e1d1_legalAction 0)) = true := by
  native_decide

theorem fivefoldBeforeE4_valid : Valid fivefoldBeforeE4.current :=
  starting_current_valid

theorem fivefoldBeforeE4_e2e4_legalAction :
    LegalAction fivefoldBeforeE4 (Action.move (Move.std Square.e2 Square.e4)) :=
  starting_e2e4_legal

theorem fivefoldBeforeE4_decide :
    @decide (EndsGame fivefoldBeforeE4 (Action.move (Move.std Square.e2 Square.e4)))
      (endsGameDecidable fivefoldBeforeE4 _
        fivefoldBeforeE4_valid fivefoldBeforeE4_e2e4_legalAction) = true := by
  native_decide

theorem kingsOnly_149_e1d1_decide :
    @decide (EndsGame (repeated kingsOnly 149)
        (Action.move (Move.std Square.e1 Square.d1)))
      (endsGameDecidable (repeated kingsOnly 149) _
        kingsOnly_valid (kingsOnly_e1d1_legalAction 149)) = true := by
  native_decide

theorem afterE2e4_valid : Valid afterE2e4.current :=
  starting_e2e4_play_valid

theorem afterE2e4e7e5Offer_valid : Valid afterE2e4e7e5Offer.current := by
  native_decide

theorem afterE2e4e7e5Offer_acceptDraw_legal :
    LegalAction afterE2e4e7e5Offer .acceptDraw :=
  rfl

theorem afterE2e4e7e5Offer_acceptDraw_decide :
    @decide (EndsGame afterE2e4e7e5Offer .acceptDraw)
      (endsGameDecidable afterE2e4e7e5Offer .acceptDraw
        afterE2e4e7e5Offer_valid afterE2e4e7e5Offer_acceptDraw_legal) = true := by
  native_decide

end GameState

end Chess
