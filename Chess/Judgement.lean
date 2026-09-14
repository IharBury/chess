import Chess.Play

/-!
# Judgement of a game state

The judgement of an unfinished game under optimal play is one of three
outcomes: White is winning, nobody is winning (a draw), or Black is
winning. Both players always choose a legal action that is best for
them: White prefers a win for White, then a draw, then a win for Black,
and Black the reverse.

A player `c` can force a win when they have a legal action that either
ends the game as a win for `c`, or continues to a state from which `c`
can still force a win; and when it is the opponent's turn, every legal
action still leaves `c` able to force a win. Nobody is winning when
neither player can force a win.

In a valid game, a good action is a legal action that preserves that
judgement: it continues to a game with the same judgement, or finishes
with a matching outcome.
-/

namespace Chess

namespace GameState

open FinishedGame
open Position hiding kingsOnly starting

/-- Player `c` can force a win from the unfinished game `g`, assuming
both players always choose a legal action that is best for them. -/
inductive CanForceWin : Color → GameState → Prop
  /-- It is `c`'s turn, and they have a legal action that ends the game
  as a win for `c`. -/
  | chooseFinish {c : Color} {g : GameState} {a : Action} :
      g.current.toMove = c →
      LegalAction g a →
      EndsGame g a →
      endingOutcome g a = .win c →
      CanForceWin c g
  /-- It is `c`'s turn, and they have a legal action that continues the
  game to a state from which `c` can still force a win. -/
  | chooseProceed {c : Color} {g : GameState} {a : Action} :
      g.current.toMove = c →
      LegalAction g a →
      ¬ EndsGame g a →
      CanForceWin c (continueAfter g a) →
      CanForceWin c g
  /-- It is the opponent's turn. Every legal action that ends the game
  is a win for `c`, and every legal action that continues still lets `c`
  force a win. -/
  | respond {c : Color} {g : GameState} :
      g.current.toMove = c.other →
      (∀ a, LegalAction g a → EndsGame g a → endingOutcome g a = .win c) →
      (∀ a, LegalAction g a → ¬ EndsGame g a →
        CanForceWin c (continueAfter g a)) →
      CanForceWin c g

/-- White can force a win from `g`. -/
def WhiteWinning (g : GameState) : Prop :=
  CanForceWin .white g

/-- Black can force a win from `g`. -/
def BlackWinning (g : GameState) : Prop :=
  CanForceWin .black g

/-- Neither player can force a win from `g`: with best play the game is
a draw. -/
def NobodyWinning (g : GameState) : Prop :=
  ¬ WhiteWinning g ∧ ¬ BlackWinning g

/-- The judgement of `g` under optimal play: a win for White, a draw
(nobody is winning), or a win for Black. -/
def Judgement (g : GameState) : GameOutcome → Prop
  | .win .white => WhiteWinning g
  | .win .black => BlackWinning g
  | .draw => NobodyWinning g

theorem Judgement_win_white (g : GameState) :
    Judgement g (.win .white) ↔ WhiteWinning g :=
  Iff.rfl

theorem Judgement_win_black (g : GameState) :
    Judgement g (.win .black) ↔ BlackWinning g :=
  Iff.rfl

theorem Judgement_draw (g : GameState) :
    Judgement g .draw ↔ NobodyWinning g :=
  Iff.rfl

/-! ### Good actions -/

/-- An action `a` is good in `g` when it is legal and either continues
to a game with the same judgement or finishes with an outcome matching
that judgement. -/
def GoodAction (g : GameState) (a : Action) : Prop :=
  LegalAction g a ∧
    ((¬ EndsGame g a ∧ ∀ o, Judgement g o → Judgement (continueAfter g a) o) ∨
      (EndsGame g a ∧ Judgement g (endingOutcome g a)))

/-- A good action is legal. -/
theorem GoodAction.legal {g : GameState} {a : Action}
    (h : GoodAction g a) : LegalAction g a :=
  h.1

/-- A legal action that does not end the game, and whose next state has
the same judgement. -/
theorem GoodAction.proceed {g : GameState} {a : Action}
    (ha : LegalAction g a) (h : ¬ EndsGame g a)
    (hj : ∀ o, Judgement g o → Judgement (continueAfter g a) o) :
    GoodAction g a :=
  ⟨ha, Or.inl ⟨h, hj⟩⟩

/-- A legal action that ends the game with an outcome matching the
judgement of `g`. -/
theorem GoodAction.finish {g : GameState} {a : Action}
    (ha : LegalAction g a) (h : EndsGame g a)
    (hj : Judgement g (endingOutcome g a)) :
    GoodAction g a :=
  ⟨ha, Or.inr ⟨h, hj⟩⟩

/-- The result of playing an action in `g` preserves `g`'s judgement
when a continuing game has that judgement, or a finished game has a
matching outcome. -/
def PreservesJudgement (g : GameState) : AfterAction → Prop
  | .continuing g' => ∀ o, Judgement g o → Judgement g' o
  | .finished fg => Judgement g fg.outcome

/-- In a valid game, a legal action is good iff playing it with `after`
preserves the judgement. -/
theorem GoodAction_iff_preserves {g : GameState} {a : Action}
    (hg : Valid g.current) (ha : LegalAction g a) :
    GoodAction g a ↔ PreservesJudgement g (after g a hg ha) := by
  constructor
  · intro ⟨_, h⟩
    rcases h with ⟨hcont, hj⟩ | ⟨hend, hj⟩
    · rw [after_eq_continuing g a hcont hg ha]
      exact hj
    · rw [after_eq_finished g a hend hg ha]
      change Judgement g (ofAction g a hend).outcome
      rwa [ofAction_outcome]
  · intro hp
    have : Decidable (EndsGame g a) := endsGameDecidable g a hg ha
    by_cases hend : EndsGame g a
    · refine GoodAction.finish ha hend ?_
      rw [after_eq_finished g a hend hg ha] at hp
      change Judgement g (ofAction g a hend).outcome at hp
      rwa [ofAction_outcome] at hp
    · refine GoodAction.proceed ha hend ?_
      rwa [after_eq_continuing g a hend hg ha] at hp

/-- A mating move is a win for the player who moved. -/
theorem endingOutcome_move_of_inCheckmate (g : GameState) (m : Move)
    (h : InCheckmate (g.current.play m)) :
    endingOutcome g (.move m) = .win g.current.toMove := by
  simp only [endingOutcome]
  rw [(inCheckmate_eq_true_iff _).mpr h]
  rfl

/-- A non-mating move that ends the game is a draw. -/
theorem endingOutcome_move_of_not_inCheckmate (g : GameState) (m : Move)
    (h : ¬ InCheckmate (g.current.play m)) :
    endingOutcome g (.move m) = .draw := by
  simp only [endingOutcome]
  rw [Bool.eq_false_iff.mpr (mt (inCheckmate_eq_true_iff _).mp h)]
  rfl

theorem endingOutcome_moveAndProposeDraw_of_not_inCheckmate (g : GameState)
    (m : Move) (h : ¬ InCheckmate (g.current.play m)) :
    endingOutcome g (.moveAndProposeDraw m) = .draw := by
  simp only [endingOutcome]
  rw [Bool.eq_false_iff.mpr (mt (inCheckmate_eq_true_iff _).mp h)]
  rfl

/-- The player to move can force a win by ending the game with a legal
action whose outcome is their win. -/
theorem CanForceWin.of_ending {g : GameState} {a : Action}
    (hleg : LegalAction g a) (hend : EndsGame g a)
    (hwin : endingOutcome g a = .win g.current.toMove) :
    CanForceWin g.current.toMove g :=
  .chooseFinish rfl hleg hend hwin

/-- A legal mating move forces a win for the player who just moved. -/
theorem CanForceWin.of_checkmate {g : GameState} {m : Move}
    (hleg : LegalAction g (.move m))
    (hm : InCheckmate (g.current.play m)) :
    CanForceWin g.current.toMove g :=
  of_ending hleg (endsGame_of_checkmate (Action.plays_move m) hm)
    (endingOutcome_move_of_inCheckmate g m hm)

/-- The move played by a legal `move` or `moveAndProposeDraw` action. -/
theorem legalMove_of_LegalAction_plays {g : GameState} {a : Action}
    {m : Move} (hleg : LegalAction g a) (hp : a.Plays m) :
    LegalMove g.current m := by
  cases a with
  | move m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    exact hleg
  | moveAndProposeDraw m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    have hand : g.current.isLegalMove m = true ∧ g.opponentHasMoved = true := by
      rw [← Bool.and_eq_true]
      exact hleg
    exact hand.1
  | moveAndClaimRepetition m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    have hand : g.current.isLegalMove m = true ∧ g.appearsThreefoldAfter m = true := by
      rw [← Bool.and_eq_true]
      exact hleg
    exact hand.1
  | moveAndClaimNoProgress m' =>
    simp only [Action.Plays, Action.move?] at hp
    cases hp
    have hand : g.current.isLegalMove m = true ∧ g.leadsToNoProgress m = true := by
      rw [← Bool.and_eq_true]
      exact hleg
    exact hand.1
  | surrender | acceptDraw | claimRepetition | claimNoProgress =>
    exact (Action.not_plays_of_move?_none (by rfl) hp).elim

/-! ### Two kings: every legal action ends, and nobody is winning -/

/-- A legal move from a two-king position leaves another two-king
position, which is dead, so the action ends the game. -/
theorem EndsGame_move_of_isTwoKings {g : GameState} {m : Move}
    (h : IsTwoKings g.current) (hm : LegalMove g.current m) :
    EndsGame g (.move m) :=
  .deadPosition m (Action.plays_move m)
    (deadPosition_of_isTwoKings (h.of_play hm))

theorem EndsGame_moveAndProposeDraw_of_isTwoKings {g : GameState} {m : Move}
    (h : IsTwoKings g.current) (hm : LegalMove g.current m) :
    EndsGame g (.moveAndProposeDraw m) :=
  .deadPosition m (Action.plays_moveAndProposeDraw m)
    (deadPosition_of_isTwoKings (h.of_play hm))

/-- Every legal action from a two-king game ends play: resignation,
claims, and accepting a draw always do, and every legal move leaves a
dead position. -/
theorem EndsGame_of_isTwoKings {g : GameState} {a : Action}
    (h : IsTwoKings g.current) (hleg : LegalAction g a) :
    EndsGame g a := by
  cases a with
  | surrender => exact surrender_endsGame g
  | acceptDraw => exact acceptDraw_endsGame g
  | claimRepetition => exact claimRepetition_endsGame g
  | claimNoProgress => exact claimNoProgress_endsGame g
  | moveAndClaimRepetition m => exact moveAndClaimRepetition_endsGame g m
  | moveAndClaimNoProgress m => exact moveAndClaimNoProgress_endsGame g m
  | move m =>
    exact EndsGame_move_of_isTwoKings h hleg
  | moveAndProposeDraw m =>
    exact EndsGame_moveAndProposeDraw_of_isTwoKings h
      (legalMove_of_LegalAction_plays hleg (Action.plays_moveAndProposeDraw m))

/-- From a two-king game, no legal action is a win for the player to
move: they can only resign (a loss) or reach a draw. -/
theorem endingOutcome_ne_win_toMove_of_isTwoKings {g : GameState}
    {a : Action} (h : IsTwoKings g.current) (hleg : LegalAction g a) :
    endingOutcome g a ≠ .win g.current.toMove := by
  cases a with
  | surrender =>
    exact fun heq => Color.other_ne g.current.toMove (GameOutcome.win.inj heq)
  | acceptDraw | claimRepetition | claimNoProgress
  | moveAndClaimRepetition _ | moveAndClaimNoProgress _ =>
    intro heq
    cases heq
  | move m =>
    rw [endingOutcome_move_of_not_inCheckmate g m
      (h.of_play hleg).not_InCheckmate]
    intro heq
    cases heq
  | moveAndProposeDraw m =>
    rw [endingOutcome_moveAndProposeDraw_of_not_inCheckmate g m
      (h.of_play (legalMove_of_LegalAction_plays hleg
        (Action.plays_moveAndProposeDraw m))).not_InCheckmate]
    intro heq
    cases heq

/-- The player to move cannot force a win from a two-king game. -/
theorem not_CanForceWin_toMove_of_isTwoKings {g : GameState}
    (h : IsTwoKings g.current) :
    ¬ CanForceWin g.current.toMove g := by
  intro hw
  cases hw with
  | chooseFinish _ hleg _ ho =>
    exact endingOutcome_ne_win_toMove_of_isTwoKings h hleg ho
  | chooseProceed _ hleg hcont _ =>
    exact hcont (EndsGame_of_isTwoKings h hleg)
  | respond turn _ _ =>
    exact Color.other_ne _ (turn.symm.trans rfl)

/-- The opponent cannot force a win from a two-king game if the player
to move has a legal drawing action. -/
theorem not_CanForceWin_other_of_isTwoKings {g : GameState} {a : Action}
    (h : IsTwoKings g.current) (hleg : LegalAction g a)
    (hdraw : endingOutcome g a = .draw) :
    ¬ CanForceWin g.current.toMove.other g := by
  intro hw
  cases hw with
  | chooseFinish turn _ _ _ =>
    exact Color.other_ne g.current.toMove turn.symm
  | chooseProceed turn _ _ _ =>
    exact Color.other_ne g.current.toMove turn.symm
  | respond _ hend _ =>
    have ho := hend a hleg (EndsGame_of_isTwoKings h hleg)
    rw [hdraw] at ho
    cases ho

/-- White's `Qh7` is a legal action from `beforeQueenMate`. -/
theorem beforeQueenMate_qh7_legal :
    LegalAction beforeQueenMateGame
      (Action.move (Move.std Square.e7 Square.h7)) := by
  native_decide

/-- From the queen-and-king mate in one, White is winning: `Qh7` mates. -/
theorem beforeQueenMate_whiteWinning :
    WhiteWinning beforeQueenMateGame := by
  simpa [WhiteWinning, beforeQueenMateGame, beforeQueenMate] using
    CanForceWin.of_checkmate beforeQueenMate_qh7_legal
      beforeQueenMate_qh7_inCheckmate

theorem beforeQueenMate_judgement :
    Judgement beforeQueenMateGame (.win .white) :=
  beforeQueenMate_whiteWinning

/-! ### Black mate in one -/

/-- Black to move, rook on `a2`, White king on `g1` boxed in by its
pawns: `Ra1` is mate. -/
def beforeBackRankMate : Position where
  board := fun s =>
    if s = Square.g1 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a2 then some { color := .black, kind := .rook }
    else if s = Square.f2 then some { color := .white, kind := .pawn }
    else if s = Square.g2 then some { color := .white, kind := .pawn }
    else if s = Square.h2 then some { color := .white, kind := .pawn }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

def beforeBackRankMateGame : GameState where
  current := beforeBackRankMate
  history := []
  drawProposed := false

theorem beforeBackRankMate_ra1_inCheckmate :
    InCheckmate (beforeBackRankMate.play (Move.std Square.a2 Square.a1)) := by
  native_decide

theorem beforeBackRankMate_ra1_legal :
    LegalAction beforeBackRankMateGame
      (Action.move (Move.std Square.a2 Square.a1)) := by
  native_decide

/-- From the back-rank mate in one, Black is winning: `Ra1` mates. -/
theorem beforeBackRankMate_blackWinning :
    BlackWinning beforeBackRankMateGame := by
  simpa [BlackWinning, beforeBackRankMateGame, beforeBackRankMate] using
    CanForceWin.of_checkmate beforeBackRankMate_ra1_legal
      beforeBackRankMate_ra1_inCheckmate

theorem beforeBackRankMate_judgement :
    Judgement beforeBackRankMateGame (.win .black) :=
  beforeBackRankMate_blackWinning

/-- A king move on `e1–d1` is legal in the two-king game. -/
theorem kingsOnly_e1d1_LegalAction :
    LegalAction kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)) := by
  native_decide

theorem kingsOnly_e1d1_endingOutcome :
    endingOutcome kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)) =
      .draw :=
  endingOutcome_move_of_not_inCheckmate _ _
    (kingsOnly_isTwoKings.of_play kingsOnly_e1d1_legal).not_InCheckmate

/-- With only two kings, White cannot force a win. -/
theorem kingsOnly_not_whiteWinning : ¬ WhiteWinning kingsOnlyGame :=
  not_CanForceWin_toMove_of_isTwoKings (g := kingsOnlyGame) kingsOnly_isTwoKings

/-- With only two kings, Black cannot force a win: White can play a
king move that draws by dead position rather than resign. -/
theorem kingsOnly_not_blackWinning : ¬ BlackWinning kingsOnlyGame :=
  not_CanForceWin_other_of_isTwoKings (g := kingsOnlyGame) kingsOnly_isTwoKings
    kingsOnly_e1d1_LegalAction kingsOnly_e1d1_endingOutcome

/-- With only two kings, nobody is winning. -/
theorem kingsOnly_nobodyWinning : NobodyWinning kingsOnlyGame :=
  ⟨kingsOnly_not_whiteWinning, kingsOnly_not_blackWinning⟩

theorem kingsOnly_judgement : Judgement kingsOnlyGame .draw :=
  kingsOnly_nobodyWinning

/-! ### Good-action examples -/

/-- Playing `Qh7` from `beforeQueenMate` is good: it mates, matching
White's winning judgement. -/
theorem beforeQueenMate_qh7_endingOutcome :
    endingOutcome beforeQueenMateGame
      (Action.move (Move.std Square.e7 Square.h7)) = .win .white :=
  endingOutcome_move_of_inCheckmate _ _ beforeQueenMate_qh7_inCheckmate

theorem beforeQueenMate_qh7_goodAction :
    GoodAction beforeQueenMateGame
      (Action.move (Move.std Square.e7 Square.h7)) := by
  refine GoodAction.finish beforeQueenMate_qh7_legal
    beforeQueenMate_qh7_endsGame ?_
  rw [beforeQueenMate_qh7_endingOutcome]
  exact beforeQueenMate_judgement

theorem beforeBackRankMate_ra1_endsGame :
    EndsGame beforeBackRankMateGame
      (Action.move (Move.std Square.a2 Square.a1)) :=
  .checkmate _ (Action.plays_move _) beforeBackRankMate_ra1_inCheckmate

theorem beforeBackRankMate_ra1_endingOutcome :
    endingOutcome beforeBackRankMateGame
      (Action.move (Move.std Square.a2 Square.a1)) = .win .black :=
  endingOutcome_move_of_inCheckmate _ _ beforeBackRankMate_ra1_inCheckmate

/-- Playing `Ra1` from the back-rank mate in one is good: it mates,
matching Black's winning judgement. -/
theorem beforeBackRankMate_ra1_goodAction :
    GoodAction beforeBackRankMateGame
      (Action.move (Move.std Square.a2 Square.a1)) := by
  refine GoodAction.finish beforeBackRankMate_ra1_legal
    beforeBackRankMate_ra1_endsGame ?_
  rw [beforeBackRankMate_ra1_endingOutcome]
  exact beforeBackRankMate_judgement

/-- A king move with only two kings is good: it draws by a dead
position, matching that nobody is winning. -/
theorem kingsOnly_e1d1_goodAction :
    GoodAction kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)) := by
  refine GoodAction.finish kingsOnly_e1d1_LegalAction kingsOnly_e1d1_endsGame ?_
  rw [kingsOnly_e1d1_endingOutcome]
  exact kingsOnly_judgement

end GameState

end Chess
