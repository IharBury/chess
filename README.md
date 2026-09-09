# Chess

A [Lean 4](https://lean-lang.org) library of definitions and proofs about chess.

The board, pieces, empty-board attack geometry, full positions
(side to move, castling rights, and en passant), check and double check,
legal moves of a
position (promotions to different pieces counted separately), checkmate,
stalemate, game states
(current position plus historical positions), and finished games
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
| `Chess.Stalemate` | Whether the player to move is stalemated |
| `Chess.GameState` | Current position and all historical positions |
| `Chess.FinishedGame` | Completed games: positions, declarations, technical ends, and outcomes |

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
* stalemate is no legal move without check (`Position.inStalemate`); checkmate, and a king that can flee, are not
* the starting game position has White to move, all four castling rights, and no en passant capture
* the starting game has an empty history; its current position is the standard starting position
* a finished game records every position, player declarations (repetition claim, resignation, draw proposals with proposer and turn, acceptance), technical termination (including the timer), and who won or a draw
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
