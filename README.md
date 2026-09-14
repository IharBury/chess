# Chess

A [Lean 4](https://lean-lang.org) library of definitions and proofs about chess.

The board, pieces, empty-board attack geometry, full positions
(side to move, castling rights, and en passant), check and double check,
legal moves of a
position (promotions to different pieces counted separately), checkmate,
stalemate, game states
(current position, historical positions, and a pending draw offer),
legal actions of the player to move, whether an action ends the game,
finished games
(position history, player declarations, technical ends, and outcomes),
the result of playing an action
(the next game state, or a completed game),
and the judgement of a game state under optimal play
(White is winning, nobody is winning, or Black is winning)
are specified as Lean
types and predicates. Theorems in the library are machine-checked: `lake build`
fails if any of them stops being true of the definitions.

## Requirements

* [elan](https://github.com/leanprover/elan), which will install the Lean
  toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.33.0`)
* this package depends on [mathlib](https://github.com/leanprover-community/mathlib4)
  at the matching `v4.33.0` tag

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

## Build

From the repository root:

```bash
lake exe cache get   # download prebuilt mathlib (strongly recommended)
lake build
```

CI runs the same `lake build` via [lean-action](https://github.com/leanprover/lean-action).

## Library layout

| Module | Contents |
| --- | --- |
| `Chess.Color` | White and black, and the involution swapping them |
| `Chess.Square` | Files, ranks, the 64 squares, and square colors |
| `Chess.Piece` | Piece kinds and colored pieces |
| `Chess.Board` | Placements, including the standard starting position |
| `Chess.Geometry` | Empty-board attacks (bishop, rook, queen, king, knight, pawn) |
| `Chess.Valid` | Occupied-board attacks and whether a placement is valid |
| `Chess.Position` | Board, side to move, castling rights, and en passant |
| `Chess.PositionValid` | Whether a position is valid |
| `Chess.Check` | Whether the player to move is in check or double check |
| `Chess.Move` | Moves, playing a move, and the legal moves of a position |
| `Chess.Checkmate` | Whether the player to move is checkmated |
| `Chess.TwoKings` | Two kings alone cannot reach checkmate |
| `Chess.KingBishop` | King and bishop versus king cannot reach checkmate |
| `Chess.KingKnight` | King and knight versus king cannot reach checkmate |
| `Chess.SameColorBishops` | Two kings and two same-color bishops cannot reach checkmate |
| `Chess.Stalemate` | Whether the player to move is stalemated |
| `Chess.GameState` | Current position, historical positions, and a pending draw offer |
| `Chess.Action` | Legal actions of the player to move in an unfinished game |
| `Chess.EndsGame` | Whether an action ends the game (mate, stalemate, claims, dead position, fivefold, 75-move) |
| `Chess.KingBishops` | King and bishop versus king and bishop: checkmate is reachable exactly with opposite-color bishops, by an engineered mating line |
| `Chess.KingKnights` | King and knight versus king and knight: checkmate is reachable by an engineered mating line |
| `Chess.KingRook` | King and rook versus king: checkmate is reachable exactly when the position is not dead, by an engineered mating line |
| `Chess.KingQueen` | King and queen versus king: checkmate is reachable exactly when the position is not dead, by an engineered mating line |
| `Chess.KingPawn` | King and pawn versus king: checkmate is reachable exactly when the position is not dead, by promoting and then following the king-and-queen mating line |
| `Chess.LoneKing` | A bare king against arbitrary material: an engineered mating line (sacrifices, promotions, then a proven three-piece line or a two-minor-piece corner mate) and an engineered proof of deadness settle most positions, and an exhaustive exploration settles the rest, so that `CheckmateReachable` is decidable whenever one player has only a king (`Chess.LoneKingTheorems`) |
| `Chess.LoneKingMaterial` | The bare-king shape is preserved by legal moves; a king with bishops of one square color cannot checkmate a bare king |
| `Chess.Decide` | Any valid position: a checked cooperative mating line, a material-dead verdict, or exhaustive exploration; `Position.checkmateReachableDecidable` decides `CheckmateReachable` from `Valid p`, and `Position.deadPositionDecidable` decides `DeadPosition` (`Chess.DecideTheorems`) |
| `Chess.EndsGameTheorems` | `GameState.endsGameDecidable` decides `EndsGame` from a valid game and a legal action |
| `Chess.FinishedGame` | Completed games: positions, declarations, technical ends, and outcomes; finishing by an ending action |
| `Chess.Play` | Playing an action: the next game state, or a completed game |
| `Chess.Judgement` | Judgement of a game state under optimal play: White is winning, nobody is winning, or Black is winning |

Import the whole library with `import Chess`, or import a single module.

Sample facts already in the library:

* there are 64 squares and 12 distinct colored pieces
* `a1` is a black square; opposite corners have the same color
* the starting position has 32 pieces, 16 per side, with unique kings on `e1` and `e8`
* the starting position is a valid board; adjacent kings (both in check) are not
* the standard starting position is a valid position (`Position.starting_valid`): White to move, all four castling rights with king and rook at home, and no en passant
* a position is invalid if the opponent is in check, a castling right has king or rook off their starting squares, or en passant does not match a capturable two-square pawn jump
* the starting position is not in check; a rook, knight, bishop, queen, pawn, or king attack on the player to move is check; a blocked sliding ray is not
* double check is check by two or more pieces at once (`Position.inDoubleCheck`); a single checker is not, and blocking one of two rays leaves only a single check
* the starting position has 20 legal moves; promoting a pawn to a queen is a different move from promoting it to a rook
* checkmate is check with no legal move (`Position.inCheckmate`); a king that can flee, and a stalemate (no legal move, not in check), are not
* a valid position with only two kings is never checkmate, and no sequence of legal moves from it is checkmate (`twoKings_reachable_not_inCheckmate`)
* a valid position with two kings and one bishop is never checkmate, and no sequence of legal moves from it is checkmate (`kingBishop_reachable_not_inCheckmate`)
* a valid position with two kings and one knight is never checkmate, and no sequence of legal moves from it is checkmate (`kingKnight_reachable_not_inCheckmate`)
* a valid position with two kings and two bishops on the same square-color is never checkmate, and no sequence of legal moves from it is checkmate (`sameColorBishops_reachable_not_inCheckmate`)
* from a valid position with two kings and two bishops on opposite square-colors, checkmate is always reachable by cooperative play (`IsOppositeColorBishops.checkmateReachable`); `Position.kingBishopsCheckmateReachable` decides `CheckmateReachable` for any valid king-and-bishop versus king-and-bishop position, and `Position.kingBishopsMatingLine` produces a concrete mating line (19 plies from kings on `e1`/`e8` with bishops on `c1`/`c8`)
* from a valid position with two kings and two knights, checkmate is always reachable by cooperative play (`IsKingKnights.checkmateReachable`); `Position.kingKnightsCheckmateReachable` decides `CheckmateReachable` for any valid king-and-knight versus king-and-knight position, and `Position.kingKnightsMatingLine` produces a concrete mating line (21 plies from kings on `e1`/`e8` with knights on `b1`/`b8`)
* from a valid position with two kings and one rook, checkmate is reachable by cooperative play exactly when the position is not dead (`IsKingAndRook.checkmateReachable_iff`); if the rook side is to move it is always reachable (`IsKingAndRook.checkmateReachable_of_rookToMove`). Dead cases include stalemate of the lone king and a forced capture of an unprotected rook. `Position.kingRookCheckmateReachable` decides the property, and `Position.kingRookMatingLine` produces a concrete mating line
* from a valid position with two kings and one queen, checkmate is reachable by cooperative play exactly when the position is not dead (`IsKingAndQueen.checkmateReachable_iff`); if the queen side is to move it is always reachable (`IsKingAndQueen.checkmateReachable_of_queenToMove`). Dead cases include stalemate of the lone king and a forced capture of an unprotected queen. `Position.kingQueenCheckmateReachable` decides the property, and `Position.kingQueenMatingLine` produces a concrete mating line
* from a valid position with two kings and one pawn, checkmate is reachable by cooperative play exactly when the position is not dead (`IsKingAndPawn.checkmateReachable_iff`), by promoting to a queen and then following the king-and-queen line. Dead cases include stalemate of either side and a forced capture of an unprotected pawn. `Position.kingPawnCheckmateReachable` decides the property, and `Position.kingPawnMatingLine` produces a concrete mating line
* when one player has only a king, `Position.loneKingCheckmateReachable` decides whether checkmate is reachable without searching the game tree: it engineers a line that gives away every piece not needed for the mate, promotes the pawns, and then follows the proven queen, rook, or pawn line, or mates in a corner with two bishops, bishop and knight, or two knights. A `true` answer is sound for every valid position (`loneKingCheckmateReachable_sound`) and the answer is complete for valid positions with at most three pieces and no castling rights (`loneKingCheckmateReachable_iff_of_card_le_three`); `Position.loneKingDead` engineers the negative answer (a rejected three-piece ending, a stalemate, or every legal move leading to one within two plies). `Position.loneKingVerdict` answers with either procedure when one of them settles the position (`Position.loneKingDecided`) and otherwise explores the reachable positions exhaustively, stopping at the first checkmate or checked mating line and not expanding positions recognized as dead, among them a king with bishops of one square color against the bare king (`Chess.LoneKingMaterial`); the verdict is correct for every valid position in which one player has only a king (`loneKingVerdict_iff`), so `Position.loneKingDecidable` returns `Decidable (CheckmateReachable p)` from `Valid p` and `Position.HasLoneKing p`. `Position.loneKingMatingLine` produces the concrete line (25 plies for two knights from `b1`/`g1`, 82 plies for a lone white king against a black queen, rook, bishop, knight, and two pawns). The engineering replans after every ply with unproven ray-walking primitives (`LoneKing.legalFast`, `LoneKing.attackedFast`) and only the finished line is checked with the proven predicates, so a verdict costs a few milliseconds
* for an arbitrary valid position, `Position.checkmateReachableDecidable` decides `CheckmateReachable` from `Valid p` alone (`checkmateVerdict_iff`), and `Position.deadPositionDecidable` decides `DeadPosition`. Bare-king positions reuse `loneKingVerdict`. Every other position is answered by a checked cooperative mating line (`Decide.probe`, including Fool's mate from the standard start), by the material verdict when the pieces cannot mate (kings and bishops all on one square-color), or by exhaustive exploration of the reachable positions (`Decide.explore`). From the standard starting position the line is Fool's mate (four plies); from king and bishop versus king and knight on `e1`/`e8`/`c1`/`b8` a best-first search finds a 23-ply helpmate
* stalemate is no legal move without check (`Position.inStalemate`); checkmate, and a king that can flee, are not
* the starting game position has White to move, all four castling rights, and no en passant capture
* the starting game has an empty history, no pending draw offer, and its current position is the standard starting position
* the player to move may play a legal move, offer a draw with a move after the opponent has moved, resign, claim a draw by threefold repetition or the fifty-move rule (before or after a qualifying move), or accept a pending draw offer
* the starting game has 21 legal actions (20 moves and resignation); White may not offer a draw on the first move; after `1. e4` Black may play and offer a draw
* an action ends the game (`GameState.EndsGame`) when it checkmates, stalemates, accepts a draw, resigns, claims repetition or the fifty-move rule, or produces a dead position, fivefold repetition, or 75 moves without progress; White's `e2–e4` at the start does not. `GameState.endsGameDecidable` decides the property for a legal action in a valid game (`endsGame_eq_true_iff`): resignation at the start, `Qh7` mate, `a7` stalemate, a two-king king move, fivefold `e2–e4`, the 75-move rule, a threefold claim, and accepting a draw are settled by evaluating `GameState.endsGame`
* a finished game records every position, player declarations (repetition claim, resignation, draw proposals with proposer and turn, acceptance), technical termination (including the timer), and who won or a draw
* `FinishedGame.ofAction` turns an unfinished game and an ending action into that record: resignation at the start is a win for Black; a mating move is a win for the player who moved; accepting a draw, a repetition or fifty-move claim, stalemate, a dead position, fivefold repetition, and the 75-move rule are draws
* `GameState.after` carries out a legal action in a valid game: White's `e2–e4` at the start continues as the game after `1. e4`; resignation at the start finishes as a win for Black; after `1. e4`, Black playing `e7–e5` and offering a draw continues with that offer pending; a mating move, accepting a draw, a repetition or fifty-move claim, stalemate, a dead position, fivefold repetition, and the 75-move rule finish the game
* the judgement of a game under optimal play (`GameState.Judgement`) is a win for White, a draw (nobody is winning), or a win for Black: White is winning when they can force a win against any replies (`CanForceWin`), and nobody is winning when neither player can. From `beforeQueenMate`, White is winning (`Qh7` mates); from a back-rank mate in one, Black is winning (`Ra1` mates); with only two kings, nobody is winning
* White's win, Black's win, and a draw are three distinct outcomes
* bishops stay on one square-color; knights always change square-color
* a knight on `a1` attacks exactly `b3` and `c2`

## Adding proofs

1. Put new definitions and theorems in the existing module they belong to, or
   add a file `Chess/YourTopic.lean` and `import` it from `Chess.lean`.
2. Prefer hypotheses that match the current geometry: empty-board attacks do
   not account for pins. Occupied-board attacks (`Board.attacks`) do
   account for blocking pieces and are what `Board.isValid` uses for check,
   what `Position.isValid` uses to require that the opponent's king is
   not under attack, and what `Position.inCheck` / `Position.inDoubleCheck`
   use for the player to move. Checkmate (`Position.inCheckmate`) is that
   check together with an empty `legalMoves` set; stalemate
   (`Position.inStalemate`) is an empty `legalMoves` set without check.
3. Run `lake build` before opening a pull request.
