import Chess.PositionValid
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# Moves

A move is a source square, a destination square, and an optional promotion
kind. Castling is the king stepping two files toward the rook; en passant
is a pawn capturing onto the en passant target square. Promotions to
different pieces are different moves.
-/

namespace Chess

/-- A chess move: origin, destination, and a promotion kind when a pawn
reaches the last rank. -/
@[ext]
structure Move where
  /-- Square the moving piece leaves. -/
  src : Square
  /-- Square the moving piece occupies after the move. -/
  dst : Square
  /-- Kind the pawn becomes, if this is a promotion; `none` otherwise. -/
  promotion : Option PieceKind
deriving DecidableEq, Repr, Inhabited

namespace Move

/-- Forget the structure, viewing a move as a triple. -/
def equivProd : Move ≃ Square × Square × Option PieceKind where
  toFun m := (m.src, m.dst, m.promotion)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv := by
    intro m
    cases m
    rfl
  right_inv := by
    intro q
    cases q
    rfl

instance : Fintype Move :=
  Fintype.ofEquiv (Square × Square × Option PieceKind) equivProd.symm

/-- A non-promoting move from `src` to `dst`. -/
def std (src dst : Square) : Move :=
  ⟨src, dst, none⟩

/-- A pawn promotion from `src` to `dst`, becoming `k`. -/
def promote (src dst : Square) (k : PieceKind) : Move :=
  ⟨src, dst, some k⟩

/-- Promotions to different kinds are different moves. -/
theorem ne_of_promotion_ne {src dst : Square} {k₁ k₂ : PieceKind}
    (h : k₁ ≠ k₂) :
    promote src dst k₁ ≠ promote src dst k₂ := by
  intro hm
  exact h (Option.some.inj (congrArg Move.promotion hm))

/-- Promoting to a queen is not the same move as promoting to a rook. -/
theorem promo_queen_ne_rook (src dst : Square) :
    promote src dst .queen ≠ promote src dst .rook :=
  ne_of_promotion_ne (by decide)

/-- Promoting to a queen is not the same move as promoting to a bishop. -/
theorem promo_queen_ne_bishop (src dst : Square) :
    promote src dst .queen ≠ promote src dst .bishop :=
  ne_of_promotion_ne (by decide)

/-- Promoting to a queen is not the same move as promoting to a knight. -/
theorem promo_queen_ne_knight (src dst : Square) :
    promote src dst .queen ≠ promote src dst .knight :=
  ne_of_promotion_ne (by decide)

/-- A promotion is not a non-promoting move with the same squares. -/
theorem promote_ne_std (src dst : Square) (k : PieceKind) :
    promote src dst k ≠ std src dst := by
  intro h
  cases h

/-- If this move is a castling manoeuvre by `c`, the side that is castling. -/
def castlingSide? (m : Move) (c : Color) : Option CastlingSide :=
  let rk : CastlingRight := ⟨c, .kingside⟩
  let rq : CastlingRight := ⟨c, .queenside⟩
  if m.src == rk.kingSquare && m.dst == rk.kingDest && m.promotion == none then
    some .kingside
  else if m.src == rq.kingSquare && m.dst == rq.kingDest && m.promotion == none then
    some .queenside
  else
    none

end Move

namespace CastlingRight

/-- Whether the king would not move from, through, or into check. -/
def kingPathSafe (r : CastlingRight) (b : Board) : Bool :=
  decide (∀ s ∈ r.kingTransitSquares, b.isAttackedBy r.color.other s = false)

end CastlingRight

namespace Position

/-- Board that results from playing `m` with the piece that stood on
`m.src` (the caller supplies that piece). -/
def boardAfter (p : Position) (m : Move) (piece : Piece) : Board :=
  let placed : Piece :=
    match m.promotion with
    | some k => { color := piece.color, kind := k }
    | none => piece
  let b' := p.board.relocate m.src m.dst placed
  if piece.kind == .king then
    match m.castlingSide? piece.color with
    | some side =>
      let r : CastlingRight := ⟨piece.color, side⟩
      b'.relocate r.rookSquare r.rookDest { color := piece.color, kind := .rook }
    | none => b'
  else if piece.kind == .pawn && p.enPassant == some m.dst &&
      (p.board m.dst).isNone then
    b'.clear ⟨m.dst.file, m.src.rank⟩
  else
    b'

/-- Remaining castling privileges after the pieces have moved to `b`. -/
def castlingAfter (castling : CastlingRights) (b : Board) : CastlingRights :=
  castling.filter fun r =>
    b r.kingSquare = some { color := r.color, kind := .king } ∧
      b r.rookSquare = some { color := r.color, kind := .rook }

/-- En passant target after a move of `piece`, if a two-square pawn
advance left a capturable target. -/
def enPassantAfter (m : Move) (piece : Piece) (b : Board) : Option Square :=
  if piece.kind == .pawn &&
      m.src.file == m.dst.file &&
      m.src.rank == pawnStartRank piece.color &&
      m.dst.rank == pawnJumpToRank piece.color then
    let ep : Square := ⟨m.src.file, pawnJumpOverRank piece.color⟩
    if existsPawnAttacking b piece.color.other ep then some ep else none
  else
    none

/-- The position that obtains after playing `m`.

Castling rights that no longer have king and rook at home are dropped.
An en passant target is recorded only when a two-square pawn advance
left a pawn of the new player to move able to capture it. Legality of
`m` is not checked. -/
def play (p : Position) (m : Move) : Position :=
  match p.board m.src with
  | none => { p with toMove := p.toMove.other }
  | some piece =>
    let b := p.boardAfter m piece
    { board := b
      toMove := p.toMove.other
      castling := castlingAfter p.castling b
      enPassant := enPassantAfter m piece b }

/-- Whether `dst` is empty or occupied by an enemy piece other than a king. -/
def destOk (p : Position) (m : Move) : Bool :=
  match p.board m.dst with
  | none => true
  | some q => (q.color != p.toMove) && (q.kind != .king)

/-- Whether `m` is a geometrically legal pawn move, including promotion
choice, double step, capture, and en passant. -/
def pawnMoveOk (p : Position) (m : Move) : Bool :=
  match p.board m.src with
  | none => false
  | some piece =>
    let c := piece.color
    let promoOk : Bool :=
      if m.dst.rank == pawnPromotionRank c then
        match m.promotion with
        | some k => k.canPromoteTo
        | none => false
      else
        m.promotion == none
    let destEmpty := (p.board m.dst).isNone
    let destEnemy :=
      match p.board m.dst with
      | some q => (q.color != c) && (q.kind != .king)
      | none => false
    let single :=
      (m.dst.file == m.src.file) &&
      decide (Square.deltaRank m.src m.dst = pawnPushDelta c) &&
      destEmpty
    let double :=
      (m.src.rank == pawnStartRank c) &&
      (m.dst.file == m.src.file) &&
      decide (Square.deltaRank m.src m.dst = 2 * pawnPushDelta c) &&
      destEmpty &&
      (p.board ⟨m.src.file, pawnJumpOverRank c⟩).isNone
    let capture :=
      decide (PawnAttacks c m.src m.dst) && destEnemy
    let ep :=
      decide (PawnAttacks c m.src m.dst) && destEmpty &&
        (p.enPassant == some m.dst)
    (single || double || capture || ep) && promoOk

/-- Whether `m` is a legal castling manoeuvre in `p` (rights, empty path,
king not moving through check), ignoring the resulting check on the
destination which `isLegalMove` also filters. -/
def castleMoveOk (p : Position) (m : Move) : Bool :=
  match m.castlingSide? p.toMove with
  | none => false
  | some side =>
    let r : CastlingRight := ⟨p.toMove, side⟩
    decide (r ∈ p.castling) &&
      (p.board r.kingSquare == some { color := p.toMove, kind := .king }) &&
      (p.board r.rookSquare == some { color := p.toMove, kind := .rook }) &&
      r.pathClear p.board &&
      r.kingPathSafe p.board

/-- Whether `m` is a legal move in `p`.

The moving piece belongs to the player to move, the destination is
empty or an enemy non-king, the geometry (including castling, en
passant, and promotion) is that of the piece, and the player's king is
not under attack after the move. Promotions to different pieces are
distinct. -/
def isLegalMove (p : Position) (m : Move) : Bool :=
  match p.board m.src with
  | none => false
  | some piece =>
    (piece.color == p.toMove) &&
      p.destOk m &&
      (if piece.kind == .pawn then
        p.pawnMoveOk m
      else if piece.kind == .king && (m.castlingSide? p.toMove).isSome then
        p.castleMoveOk m
      else
        p.board.attacks m.src m.dst && m.promotion == none) &&
      !(p.play m).board.kingIsAttacked p.toMove

/-- A move that is legal in `p`. -/
def LegalMove (p : Position) (m : Move) : Prop :=
  isLegalMove p m = true

instance {p : Position} {m : Move} : Decidable (LegalMove p m) :=
  inferInstanceAs (Decidable (isLegalMove p m = true))

/-- All legal moves from `p`. Promotions to different pieces are counted
as different moves. -/
def legalMoves (p : Position) : Finset Move :=
  Finset.univ.filter fun m => p.isLegalMove m

theorem mem_legalMoves (p : Position) (m : Move) :
    m ∈ p.legalMoves ↔ p.isLegalMove m = true := by
  simp [legalMoves]

theorem mem_legalMoves_iff_LegalMove (p : Position) (m : Move) :
    m ∈ p.legalMoves ↔ LegalMove p m :=
  mem_legalMoves p m

@[simp] theorem play_toMove (p : Position) (m : Move) :
    (p.play m).toMove = p.toMove.other := by
  unfold play
  cases p.board m.src <;> rfl

/-- Playing a move yields a different position from the starting
position: the player to move changes. -/
theorem starting_play_ne (m : Move) :
    starting.play m ≠ starting := by
  intro h
  have := congrArg Position.toMove h
  simp [play_toMove] at this

/-- The standard starting position has 20 legal moves: eight single pawn
steps, eight double pawn steps, and four knight moves. -/
theorem starting_legalMoves_card : starting.legalMoves.card = 20 := by
  native_decide

/-- White's `e2–e4` is legal at the start. -/
theorem starting_e2e4_legal : isLegalMove starting (Move.std Square.e2 Square.e4) = true := by
  native_decide

/-- White's `e2–e4` is among the starting legal moves. -/
theorem starting_e2e4_mem :
    Move.std Square.e2 Square.e4 ∈ starting.legalMoves := by
  native_decide

/-- A pawn cannot advance three squares. -/
theorem starting_e2e5_not_legal :
    isLegalMove starting (Move.std Square.e2 Square.e5) = false := by
  native_decide

/-- Castling is blocked by the pieces on the first rank at the start. -/
theorem starting_castle_kingside_not_legal :
    isLegalMove starting (Move.std Square.e1 Square.g1) = false := by
  native_decide

/-- After `e2–e4` from the start, Black is to move and the pawn stands on
`e4`. No en passant target is recorded: no black pawn attacks `e3`. -/
theorem starting_play_e2e4 :
    let p := starting.play (Move.std Square.e2 Square.e4)
    p.toMove = .black ∧
      p.board Square.e4 = some { color := .white, kind := .pawn } ∧
      p.board Square.e2 = none ∧
      p.enPassant = none := by
  native_decide

/-- Black to move from the starting placement also has 20 legal moves. -/
theorem starting_black_legalMoves_card :
    ({ starting with toMove := .black } : Position).legalMoves.card = 20 := by
  native_decide

/-- Kings, a white pawn on `a7`, and a black king: the pawn has four
distinct promotions. -/
def promotionBoard : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else if s = Square.a7 then some { color := .white, kind := .pawn }
  else none

def withPromotion : Position where
  board := promotionBoard
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem withPromotion_isValid : isValid withPromotion = true := by
  native_decide

theorem withPromotion_queen_legal :
    isLegalMove withPromotion (Move.promote Square.a7 Square.a8 .queen) = true := by
  native_decide

theorem withPromotion_rook_legal :
    isLegalMove withPromotion (Move.promote Square.a7 Square.a8 .rook) = true := by
  native_decide

theorem withPromotion_bishop_legal :
    isLegalMove withPromotion (Move.promote Square.a7 Square.a8 .bishop) = true := by
  native_decide

theorem withPromotion_knight_legal :
    isLegalMove withPromotion (Move.promote Square.a7 Square.a8 .knight) = true := by
  native_decide

/-- The four promotion choices are pairwise distinct and all legal. -/
theorem withPromotion_promotions_distinct :
    Move.promote Square.a7 Square.a8 .queen ∈ withPromotion.legalMoves ∧
      Move.promote Square.a7 Square.a8 .rook ∈ withPromotion.legalMoves ∧
      Move.promote Square.a7 Square.a8 .bishop ∈ withPromotion.legalMoves ∧
      Move.promote Square.a7 Square.a8 .knight ∈ withPromotion.legalMoves ∧
      Move.promote Square.a7 Square.a8 .queen ≠
        Move.promote Square.a7 Square.a8 .rook := by
  native_decide

/-- A pawn reaching the last rank must promote: `a7–a8` with no kind is
illegal. -/
theorem withPromotion_no_kind_not_legal :
    isLegalMove withPromotion (Move.std Square.a7 Square.a8) = false := by
  native_decide

/-- After promoting to a queen, `a8` holds a queen and no pawn remains. -/
theorem withPromotion_play_queen :
    let p := withPromotion.play (Move.promote Square.a7 Square.a8 .queen)
    p.board Square.a8 = some { color := .white, kind := .queen } ∧
      p.board Square.a7 = none := by
  native_decide

/-- En passant `d5×e6` is legal in `withEnPassant`. -/
theorem withEnPassant_capture_legal :
    isLegalMove withEnPassant (Move.std Square.d5 Square.e6) = true := by
  native_decide

theorem withEnPassant_capture_mem :
    Move.std Square.d5 Square.e6 ∈ withEnPassant.legalMoves := by
  native_decide

/-- After the en passant capture, the jumped pawn is gone and White's
pawn occupies `e6`. -/
theorem withEnPassant_play :
    let p := withEnPassant.play (Move.std Square.d5 Square.e6)
    p.board Square.e6 = some { color := .white, kind := .pawn } ∧
      p.board Square.e5 = none ∧
      p.board Square.d5 = none ∧
      p.enPassant = none := by
  native_decide

/-- Kings and both sides' rooks on their starting squares, otherwise
empty: both of White's castling manoeuvres are legal. -/
def castleBoard : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else if s = Square.a1 then some { color := .white, kind := .rook }
  else if s = Square.h1 then some { color := .white, kind := .rook }
  else if s = Square.a8 then some { color := .black, kind := .rook }
  else if s = Square.h8 then some { color := .black, kind := .rook }
  else none

def withCastling : Position where
  board := castleBoard
  toMove := .white
  castling := CastlingRights.all
  enPassant := none

theorem withCastling_isValid : isValid withCastling = true := by
  native_decide

theorem withCastling_kingside_legal :
    isLegalMove withCastling (Move.std Square.e1 Square.g1) = true := by
  native_decide

theorem withCastling_queenside_legal :
    isLegalMove withCastling (Move.std Square.e1 Square.c1) = true := by
  native_decide

/-- After White castles kingside, the king is on `g1`, the rook on `f1`,
and White has no remaining castling rights. -/
theorem withCastling_play_kingside :
    let p := withCastling.play (Move.std Square.e1 Square.g1)
    p.board Square.g1 = some { color := .white, kind := .king } ∧
      p.board Square.f1 = some { color := .white, kind := .rook } ∧
      p.board Square.e1 = none ∧
      p.board Square.h1 = none ∧
      p.castling.allows .white .kingside = false ∧
      p.castling.allows .white .queenside = false := by
  native_decide

/-- A black rook on `f4` attacks `f1`, so White cannot castle kingside. -/
def castleThroughCheck : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.h1 then some { color := .white, kind := .rook }
    else if s = Square.f4 then some { color := .black, kind := .rook }
    else none
  toMove := .white
  castling := {CastlingRight.whiteKingside}
  enPassant := none

theorem castleThroughCheck_kingside_not_legal :
    isLegalMove castleThroughCheck (Move.std Square.e1 Square.g1) = false := by
  native_decide

/-- A knight pinned to the king cannot leave the line of the pin. -/
def pinnedKnight : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.e2 then some { color := .white, kind := .knight }
    else if s = Square.e7 then some { color := .black, kind := .rook }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem pinnedKnight_c3_not_legal :
    isLegalMove pinnedKnight (Move.std Square.e2 Square.c3) = false := by
  native_decide

end Position

end Chess
