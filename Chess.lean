import Chess.Color
import Chess.Square
import Chess.Piece
import Chess.Board
import Chess.Geometry
import Chess.Valid
import Chess.Position
import Chess.PositionValid
import Chess.Check
import Chess.Move
import Chess.Checkmate
import Chess.TwoKings
import Chess.KingBishop
import Chess.KingKnight
import Chess.SameColorBishops
import Chess.Stalemate
import Chess.GameState
import Chess.Action
import Chess.EndsGame
import Chess.KingBishops
import Chess.KingKnights
import Chess.KingKnightsTheorems
import Chess.Rot180
import Chess.KingRookTheorems
import Chess.KingQueenTheorems
import Chess.KingPawnCover
import Chess.KingPawnTheorems
import Chess.LoneKing
import Chess.LoneKingMaterial
import Chess.LoneKingTheorems
import Chess.Decide
import Chess.DecideTheorems
import Chess.EndsGameTheorems
import Chess.FinishedGame
import Chess.ValidPlay
import Chess.Play
import Chess.Judgement

/-!
# Chess

A Lean 4 library of definitions and proofs about chess.

The modules are layered so that later files can depend on earlier ones
without circular imports:

* `Chess.Color` — player colors
* `Chess.Square` — files, ranks, and the 64 squares
* `Chess.Piece` — piece kinds and colored pieces
* `Chess.Board` — placements of pieces, including the starting position
* `Chess.Geometry` — empty-board attack geometry and its basic theorems
* `Chess.Valid` — occupied-board attacks and whether a placement is valid
* `Chess.Position` — board, side to move, castling rights, and en passant
* `Chess.PositionValid` — whether a position (board, turn, castling, en passant) is valid
* `Chess.Check` — whether the player to move is in check or double check
* `Chess.Move` — moves (including distinct promotions), playing them, and legal-move enumeration
* `Chess.Checkmate` — whether the player to move is checkmated
* `Chess.TwoKings` — two kings alone cannot reach checkmate
* `Chess.KingBishop` — king and bishop versus king cannot reach checkmate
* `Chess.KingKnight` — king and knight versus king cannot reach checkmate
* `Chess.SameColorBishops` — two kings and two same-color bishops cannot reach checkmate
* `Chess.Stalemate` — whether the player to move is stalemated
* `Chess.GameState` — current position, historical positions, and a pending draw offer
* `Chess.Action` — legal actions of the player to move in an unfinished game
* `Chess.EndsGame` — whether an action ends the game
* `Chess.EndsGameTheorems` — `EndsGame` is decidable when a played move leaves a valid position
* `Chess.KingBishops` — king and bishop versus king and bishop: checkmate is reachable exactly with
  opposite-color bishops
* `Chess.KingKnights` — king and knight versus king and knight: checkmate is reachable by an
  engineered mating line (`Chess.KingKnightsTheorems`)
* `Chess.Rot180` — 180° rotation and color swap, used to reduce a black-piece
  three-piece ending to the white-piece frame
* `Chess.KingRook` — king and rook versus king: checkmate is reachable exactly when
  the position is not dead (`Chess.KingRookTheorems`, covering files in
  `Chess.KingRookCover`)
* `Chess.KingQueen` — king and queen versus king: checkmate is reachable exactly when
  the position is not dead (`Chess.KingQueenTheorems`, covering files in
  `Chess.KingQueenCover`)
* `Chess.KingPawn` — king and pawn versus king: checkmate is reachable exactly when
  the position is not dead, by promoting and then following the king-and-queen line
  (`Chess.KingPawnTheorems`, covering files in `Chess.KingPawnCover`)
* `Chess.LoneKing` — a bare king against arbitrary material: an engineered mating line
  (sacrifices, promotions, then a proven three-piece line or a two-minor-piece corner
  mate) and an engineered proof of deadness settle most positions, and an exhaustive
  exploration of the reachable positions settles the rest, so that `CheckmateReachable`
  is decidable for every valid position in which one player has only a king
  (`Chess.LoneKingTheorems`)
* `Chess.LoneKingMaterial` — the bare-king shape is preserved by legal moves, and a king
  with bishops of one square color cannot checkmate a bare king
* `Chess.Decide` — any valid position: an engineered cooperative mating line (Fool's mate from
  the start, a recognized ending, a capture that reduces to one, or a bounded help-mate search)
  is checked with `Position.pathLegalN` and `Position.inCheckmate`; material that cannot mate
  (kings and bishops all on one square-color) is dead; remaining positions are explored like
  `LoneKing.explore`. `Position.checkmateVerdict` is correct for every valid position
  (`checkmateVerdict_iff` in `Chess.DecideTheorems`), so `Position.checkmateReachableDecidable`
  is a `Decidable (CheckmateReachable p)` from `Valid p` alone. `DeadPosition` is the
  negation, so `Position.deadPositionDecidable` decides it from the same hypothesis
* `Chess.EndsGameTheorems` — `GameState.endsGame` matches `EndsGame` when every move
  the action plays leaves a valid position (`endsGame_eq_true_iff`), so
  `GameState.endsGameDecidable` is a `Decidable (EndsGame g a)` from that hypothesis
* `Chess.FinishedGame` — completed games, and `ofAction` to finish by an ending action
* `Chess.ValidPlay` — a legal move from a valid position yields a valid
  position (`Position.valid_play`)
* `Chess.Play` — carrying out a legal action in a valid game:
  `GameState.after` returns the next unfinished game, or a finished game
  when the action ends play
* `Chess.Judgement` — the judgement of an unfinished game under optimal play:
  White is winning, nobody is winning, or Black is winning
-/
