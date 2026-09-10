import Chess.Action
import Chess.Stalemate
import Chess.TwoKings

/-!
# Ending the game

An action of the player to move ends the game when it produces checkmate
or stalemate, accepts a draw, resigns, claims a draw by threefold
repetition or the fifty-move rule, or automatically terminates play: a
dead position (FIDE Article 5.2.2), fivefold repetition (Article 9.6.1),
or seventy-five moves by each player without a pawn move or capture
(Article 9.6.2).

Whether the action is legal in the game is `GameState.LegalAction`; this
module records only that the action, if carried out, would end the game.
-/

namespace Chess

namespace Position

/-- Neither player can checkmate by any series of legal moves
(FIDE Article 5.2.2). -/
def DeadPosition (p : Position) : Prop :=
  ∀ q, Reachable p q → ¬ InCheckmate q

/-- A position is dead exactly when checkmate is not reachable from it. -/
theorem DeadPosition_iff_not_CheckmateReachable (p : Position) :
    DeadPosition p ↔ ¬ CheckmateReachable p := by
  constructor
  · intro hd ⟨q, hr, hm⟩
    exact hd q hr hm
  · intro h q hr hm
    exact h ⟨q, hr, hm⟩

/-- If checkmate is reachable, the position is not dead. -/
theorem not_deadPosition_of_checkmateReachable {p : Position}
    (h : CheckmateReachable p) : ¬ DeadPosition p :=
  fun hd => (DeadPosition_iff_not_CheckmateReachable p).mp hd h

/-- If every move is illegal in `start`, the only reachable position is
`start` itself. -/
theorem reachable_eq_of_forall_not_LegalMove {start q : Position}
    (hempty : ∀ m : Move, ¬ LegalMove start m) (hr : Reachable start q) :
    q = start := by
  refine Reachable.rec (motive := fun q' _ => q' = start) rfl ?_ hr
  intro r m _hr hm ih
  exact (hempty m (ih ▸ hm)).elim

/-- A stalemate cannot reach checkmate: there are no legal moves, so the
only reachable position is the stalemate itself, which is not
checkmate. -/
theorem not_CheckmateReachable_of_InStalemate {p : Position}
    (h : InStalemate p) : ¬ CheckmateReachable p := by
  intro ⟨q, hr, hm⟩
  have hq : q = p :=
    reachable_eq_of_forall_not_LegalMove
      ((InStalemate_iff_forall_not_LegalMove p).mp h).2 hr
  subst hq
  exact h.1 hm.1

/-- A checkmate position is not dead: checkmate has already been
reached. -/
theorem not_deadPosition_of_inCheckmate {p : Position} (h : InCheckmate p) :
    ¬ DeadPosition p :=
  fun hd => hd p Reachable.refl h

/-- From a two-king position no sequence of legal moves is checkmate. -/
theorem deadPosition_of_isTwoKings {p : Position} (h : IsTwoKings p) :
    DeadPosition p :=
  fun _ hr => (h.of_reachable hr).not_InCheckmate

/-- If a legal sequence from `p` is checkmate, then `p` is not dead. -/
theorem not_deadPosition_of_legalSeq {p : Position} {ms : List Move}
    (hms : LegalSeq p ms) (hm : InCheckmate (playSeq p ms)) :
    ¬ DeadPosition p :=
  fun hd => hd (playSeq p ms) (legalSeq_reachable hms) hm

end Position

namespace GameState

open Position hiding kingsOnly starting

/-- An action `a` in the unfinished game `g` ends the game: one of the
following holds.

* `a` plays a move resulting in checkmate (FIDE Articles 1.4.1, 5.1.1)
* `a` plays a move resulting in stalemate (Article 5.2.1)
* `a` accepts a draw proposal (Article 9.1.2.3)
* `a` is resignation (Article 5.1.2)
* `a` claims repetition, after a move or not (Article 9.2)
* `a` claims no progress, after a move or not (Article 9.3)
* `a` plays a move resulting in a dead position: no sequence of legal
  moves can lead to checkmate (Article 5.2.2)
* `a` plays a move leading to a position that has occurred five times
  (Article 9.6.1)
* `a` plays a move after which 75 moves have been made by each player
  without a pawn move or capture (Article 9.6.2)
-/
inductive EndsGame (g : GameState) : Action → Prop where
  /-- A move that checkmates. -/
  | checkmate {a : Action} (m : Move) :
      a.Plays m → InCheckmate (g.current.play m) → EndsGame g a
  /-- A move that stalemates. -/
  | stalemate {a : Action} (m : Move) :
      a.Plays m → InStalemate (g.current.play m) → EndsGame g a
  /-- Accepting a pending draw offer. -/
  | acceptDraw : EndsGame g .acceptDraw
  /-- Resignation. -/
  | surrender : EndsGame g .surrender
  /-- A threefold-repetition claim, after a move or in the current
  position. -/
  | claimRepetition {a : Action} :
      a.ClaimsRepetition → EndsGame g a
  /-- A fifty-move claim, after a move or in the current position. -/
  | claimNoProgress {a : Action} :
      a.ClaimsNoProgress → EndsGame g a
  /-- A move to a position from which no sequence of legal moves can
  lead to checkmate. -/
  | deadPosition {a : Action} (m : Move) :
      a.Plays m → DeadPosition (g.current.play m) → EndsGame g a
  /-- A move producing a fifth occurrence of a position. -/
  | fivefold {a : Action} (m : Move) :
      a.Plays m → AppearsFivefoldAfter g m → EndsGame g a
  /-- A move completing 75 moves by each player without a pawn move or
  capture. -/
  | seventyFive {a : Action} (m : Move) :
      a.Plays m → LeadsToSeventyFiveMove g m → EndsGame g a

/-- Resignation always ends the game. -/
theorem surrender_endsGame (g : GameState) : EndsGame g .surrender :=
  .surrender

/-- Accepting a draw always ends the game. -/
theorem acceptDraw_endsGame (g : GameState) : EndsGame g .acceptDraw :=
  .acceptDraw

/-- Claiming threefold repetition in the current position ends the game. -/
theorem claimRepetition_endsGame (g : GameState) :
    EndsGame g .claimRepetition :=
  .claimRepetition Action.claimsRepetition_claimRepetition

/-- Claiming threefold repetition after a move ends the game. -/
theorem moveAndClaimRepetition_endsGame (g : GameState) (m : Move) :
    EndsGame g (.moveAndClaimRepetition m) :=
  .claimRepetition (Action.claimsRepetition_moveAndClaim m)

/-- Claiming the fifty-move rule in the current position ends the game. -/
theorem claimNoProgress_endsGame (g : GameState) :
    EndsGame g .claimNoProgress :=
  .claimNoProgress Action.claimsNoProgress_claimNoProgress

/-- Claiming the fifty-move rule after a move ends the game. -/
theorem moveAndClaimNoProgress_endsGame (g : GameState) (m : Move) :
    EndsGame g (.moveAndClaimNoProgress m) :=
  .claimNoProgress (Action.claimsNoProgress_moveAndClaim m)

/-- Playing a move that checkmates ends the game. -/
theorem endsGame_of_checkmate {g : GameState} {a : Action} {m : Move}
    (hp : a.Plays m) (h : InCheckmate (g.current.play m)) :
    EndsGame g a :=
  .checkmate m hp h

/-- Playing a move that stalemates ends the game. -/
theorem endsGame_of_stalemate {g : GameState} {a : Action} {m : Move}
    (hp : a.Plays m) (h : InStalemate (g.current.play m)) :
    EndsGame g a :=
  .stalemate m hp h

/-- Playing a move to a dead position ends the game. -/
theorem endsGame_of_deadPosition {g : GameState} {a : Action} {m : Move}
    (hp : a.Plays m) (h : DeadPosition (g.current.play m)) :
    EndsGame g a :=
  .deadPosition m hp h

/-- Playing a move that produces a fifth occurrence ends the game. -/
theorem endsGame_of_fivefold {g : GameState} {a : Action} {m : Move}
    (hp : a.Plays m) (h : AppearsFivefoldAfter g m) :
    EndsGame g a :=
  .fivefold m hp h

/-- Playing a move that completes 75 quiet moves by each player ends the
game. -/
theorem endsGame_of_seventyFive {g : GameState} {a : Action} {m : Move}
    (hp : a.Plays m) (h : LeadsToSeventyFiveMove g m) :
    EndsGame g a :=
  .seventyFive m hp h

/-! ### Ordinary moves that do not end the game -/

/-- White's first move does not checkmate. -/
theorem starting_e2e4_not_inCheckmate :
    ¬ InCheckmate (starting.current.play (Move.std Square.e2 Square.e4)) := by
  native_decide

/-- White's first move does not stalemate. -/
theorem starting_e2e4_not_inStalemate :
    ¬ InStalemate (starting.current.play (Move.std Square.e2 Square.e4)) := by
  native_decide

/-- White's first move is not a fifth occurrence of the resulting
position. -/
theorem starting_e2e4_not_fivefold :
    ¬ AppearsFivefoldAfter starting (Move.std Square.e2 Square.e4) := by
  native_decide

/-- White's first move is a pawn move, so it does not complete 75 quiet
moves. -/
theorem starting_e2e4_not_seventyFive :
    ¬ LeadsToSeventyFiveMove starting (Move.std Square.e2 Square.e4) := by
  native_decide

/-- After `1. e4`, Scholar's mate is a legal sequence ending in
checkmate: `1... e5 2. Qh5 Nc6 3. Bc4 Nf6 4. Qxf7#`. -/
def scholarsMateAfterE4 : List Move :=
  [Move.std Square.e7 Square.e5,
    Move.std Square.d1 Square.h5,
    Move.std Square.b8 Square.c6,
    Move.std Square.f1 Square.c4,
    Move.std Square.g8 Square.f6,
    Move.std Square.h5 Square.f7]

theorem scholarsMateAfterE4_legal :
    LegalSeq (starting.current.play (Move.std Square.e2 Square.e4))
      scholarsMateAfterE4 := by
  native_decide

theorem scholarsMateAfterE4_inCheckmate :
    InCheckmate
      (playSeq (starting.current.play (Move.std Square.e2 Square.e4))
        scholarsMateAfterE4) := by
  native_decide

/-- After `1. e4` the position is not dead: Scholar's mate is reachable. -/
theorem starting_e2e4_not_deadPosition :
    ¬ DeadPosition (starting.current.play (Move.std Square.e2 Square.e4)) :=
  not_deadPosition_of_legalSeq scholarsMateAfterE4_legal
    scholarsMateAfterE4_inCheckmate

/-- White's `e2–e4` at the start does not end the game. -/
theorem starting_e2e4_not_endsGame :
    ¬ EndsGame starting (Action.move (Move.std Square.e2 Square.e4)) := by
  intro h
  cases h with
  | checkmate m hplay hc =>
    have hm : m = Move.std Square.e2 Square.e4 :=
      ((Action.plays_move_iff _ _).mp hplay).symm
    subst hm
    exact starting_e2e4_not_inCheckmate hc
  | stalemate m hplay hs =>
    have hm : m = Move.std Square.e2 Square.e4 :=
      ((Action.plays_move_iff _ _).mp hplay).symm
    subst hm
    exact starting_e2e4_not_inStalemate hs
  | claimRepetition hr =>
    exact Action.not_claimsRepetition_move _ hr
  | claimNoProgress hp =>
    exact Action.not_claimsNoProgress_move _ hp
  | deadPosition m hplay hd =>
    have hm : m = Move.std Square.e2 Square.e4 :=
      ((Action.plays_move_iff _ _).mp hplay).symm
    subst hm
    exact starting_e2e4_not_deadPosition hd
  | fivefold m hplay hf =>
    have hm : m = Move.std Square.e2 Square.e4 :=
      ((Action.plays_move_iff _ _).mp hplay).symm
    subst hm
    exact starting_e2e4_not_fivefold hf
  | seventyFive m hplay h75 =>
    have hm : m = Move.std Square.e2 Square.e4 :=
      ((Action.plays_move_iff _ _).mp hplay).symm
    subst hm
    exact starting_e2e4_not_seventyFive h75

/-- Resignation is an ending action at the start of the game. -/
theorem starting_surrender_endsGame : EndsGame starting .surrender :=
  surrender_endsGame _

/-! ### Checkmate -/

/-- White to move, queen on `h4`, king on `g6`, black king on `h8`:
`Qh7` is mate. -/
def beforeQueenMate : Position where
  board := fun s =>
    if s = Square.g6 then some { color := .white, kind := .king }
    else if s = Square.h8 then some { color := .black, kind := .king }
    else if s = Square.h4 then some { color := .white, kind := .queen }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

def beforeQueenMateGame : GameState where
  current := beforeQueenMate
  history := []
  drawProposed := false

theorem beforeQueenMate_qh7_inCheckmate :
    InCheckmate (beforeQueenMate.play (Move.std Square.h4 Square.h7)) := by
  native_decide

/-- Playing `Qh7` from `beforeQueenMate` ends the game by checkmate. -/
theorem beforeQueenMate_qh7_endsGame :
    EndsGame beforeQueenMateGame
      (Action.move (Move.std Square.h4 Square.h7)) :=
  .checkmate _ (by rfl) beforeQueenMate_qh7_inCheckmate

/-! ### Stalemate -/

/-- White to move, king on `b6`, pawn on `a6`, black king on `a8`:
`a7` stalemates. -/
def beforeStalemate : Position where
  board := fun s =>
    if s = Square.b6 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a6 then some { color := .white, kind := .pawn }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

def beforeStalemateGame : GameState where
  current := beforeStalemate
  history := []
  drawProposed := false

theorem beforeStalemate_a7_inStalemate :
    InStalemate (beforeStalemate.play (Move.std Square.a6 Square.a7)) := by
  native_decide

/-- Playing `a6–a7` from `beforeStalemate` ends the game by stalemate. -/
theorem beforeStalemate_a7_endsGame :
    EndsGame beforeStalemateGame
      (Action.move (Move.std Square.a6 Square.a7)) :=
  .stalemate _ (by rfl) beforeStalemate_a7_inStalemate

/-! ### Dead position -/

theorem kingsOnly_isTwoKings : IsTwoKings kingsOnly :=
  isTwoKings_of_valid
    ((Position.isValid_eq_true_iff kingsOnly).mp (by native_decide))
    (by native_decide)

/-- A quiet king move from the two-king position yields another two-king
position, which is dead. -/
theorem kingsOnly_e1d1_deadPosition :
    DeadPosition (kingsOnly.play (Move.std Square.e1 Square.d1)) :=
  deadPosition_of_isTwoKings
    (kingsOnly_isTwoKings.of_play (by native_decide : LegalMove kingsOnly
      (Move.std Square.e1 Square.d1)))

def kingsOnlyGame : GameState :=
  repeated kingsOnly 0

/-- A king move with only the two kings ends the game: the resulting
position cannot lead to checkmate. -/
theorem kingsOnly_e1d1_endsGame :
    EndsGame kingsOnlyGame (Action.move (Move.std Square.e1 Square.d1)) :=
  .deadPosition _ (by rfl) kingsOnly_e1d1_deadPosition

/-! ### Fivefold repetition -/

/-- A game whose history already contains four copies of the position
after `e2–e4`. Playing that move is a fifth occurrence. -/
def fivefoldBeforeE4 : GameState where
  current := Position.starting
  history :=
    let p := Position.starting.play (Move.std Square.e2 Square.e4)
    [p, p, p, p]
  drawProposed := false

theorem fivefoldBeforeE4_appears :
    AppearsFivefoldAfter fivefoldBeforeE4 (Move.std Square.e2 Square.e4) := by
  native_decide

/-- Playing `e2–e4` into a fifth occurrence ends the game. -/
theorem fivefoldBeforeE4_endsGame :
    EndsGame fivefoldBeforeE4
      (Action.move (Move.std Square.e2 Square.e4)) :=
  .fivefold _ (by rfl) fivefoldBeforeE4_appears

/-! ### Seventy-five-move rule -/

theorem kingsOnly_149_seventyFive :
    LeadsToSeventyFiveMove (repeated kingsOnly 149)
      (Move.std Square.e1 Square.d1) := by
  have hc : (repeated kingsOnly 149).current = kingsOnly := rfl
  have hclock : (repeated kingsOnly 149).pliesWithoutProgress = 149 :=
    pliesWithoutProgress_repeated kingsOnly 149
  simp [LeadsToSeventyFiveMove, leadsToSeventyFiveMove, hc,
    kingsOnly_e1d1_not_pawnOrCapture, hclock, seventyFiveMovePlies]

/-- A quiet king move after 149 quiet plies completes 75 moves by each
player and ends the game. -/
theorem kingsOnly_149_e1d1_endsGame :
    EndsGame (repeated kingsOnly 149)
      (Action.move (Move.std Square.e1 Square.d1)) :=
  .seventyFive _ (by rfl) kingsOnly_149_seventyFive

/-- After `1. e4 e5` with a draw offer, accepting the offer ends the game. -/
theorem afterE2e4e7e5Offer_acceptDraw_endsGame :
    EndsGame afterE2e4e7e5Offer .acceptDraw :=
  acceptDraw_endsGame _

end GameState

end Chess
