# Chess

A [Lean 4](https://lean-lang.org) library of definitions and proofs about chess.

The board, pieces, empty-board attack geometry, full positions
(side to move, castling rights, and en passant), check and double check,
legal moves of a
position (promotions to different pieces counted separately), checkmate,
stalemate, game states
(current position, historical positions, and a pending draw offer),
legal actions of the player to move, whether an action ends the game,
and finished games
(position history, player declarations, technical ends, and outcomes) are specified as Lean
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
| `Chess.FinishedGame` | Completed games: positions, declarations, technical ends, and outcomes; finishing by an ending action |

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
* from a valid position with two kings and two knights, checkmate is always reachable by cooperative play (`IsKingKnights.checkmateReachable`); `Position.kingKnightsCheckmateReachable` decides `CheckmateReachable` for any valid king-and-knight versus king-and-knight position, and `Position.kingKnightsMatingLine` produces a concrete mating line (31 plies from kings on `e1`/`e8` with knights on `b1`/`b8`)
* stalemate is no legal move without check (`Position.inStalemate`); checkmate, and a king that can flee, are not
* the starting game position has White to move, all four castling rights, and no en passant capture
* the starting game has an empty history, no pending draw offer, and its current position is the standard starting position
* the player to move may play a legal move, offer a draw with a move after the opponent has moved, resign, claim a draw by threefold repetition or the fifty-move rule (before or after a qualifying move), or accept a pending draw offer
* the starting game has 21 legal actions (20 moves and resignation); White may not offer a draw on the first move; after `1. e4` Black may play and offer a draw
* an action ends the game (`GameState.EndsGame`) when it checkmates, stalemates, accepts a draw, resigns, claims repetition or the fifty-move rule, or produces a dead position, fivefold repetition, or 75 moves without progress; White's `e2–e4` at the start does not
* a finished game records every position, player declarations (repetition claim, resignation, draw proposals with proposer and turn, acceptance), technical termination (including the timer), and who won or a draw
* `FinishedGame.ofAction` turns an unfinished game and an ending action into that record: resignation at the start is a win for Black; a mating move is a win for the player who moved; accepting a draw, a repetition or fifty-move claim, stalemate, a dead position, fivefold repetition, and the 75-move rule are draws
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
