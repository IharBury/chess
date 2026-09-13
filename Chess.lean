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
import Chess.LoneKingTheorems
import Chess.FinishedGame

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
  mate) decides `CheckmateReachable`, soundly everywhere and completely for at most
  three pieces (`Chess.LoneKingTheorems`)
* `Chess.FinishedGame` — completed games, and `ofAction` to finish by an ending action
-/
