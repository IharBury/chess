import Chess.KingQueen

/-!
# King and pawn versus king

A valid position whose board holds only the two kings and one pawn is
king-and-pawn versus king. Checkmate with those three pieces never occurs:
the pawn attacks at most two squares, and the supporting king cannot cover
the remaining flights of a checked lone king without standing adjacent to
it (illegal). Checkmate is still reachable, by cooperative play that
promotes the pawn to a queen and then follows the engineered king-and-queen
mating line of `Chess.KingQueen`.

Checkmate is not *always* reachable. If the lone king is to move in
stalemate, or its only legal move is to capture an unprotected pawn, the
position is dead: every continuation is that same dead position or a two-king
position. The pawn side can also be stalemated (the king trapped behind its
own blocked rook pawn).

This module shows that from every other legal king-and-pawn versus king
position, checkmate is reachable by a helpmate. The two sides steer the pawn
to the seventh rank and promote to a queen on a square from which the
resulting king-and-queen position is not dead; `Chess.KingQueen` then
supplies the mate. A potential `KPState.mu` measures the distance of the three
pieces from a safe promotion (pawn rank, a route for the black king off the
pawn's file, a supporting square for the white king, and a bonus for being
in check). Every legal state is checkmate, is dead, promotes in a short
legal sequence to a non-dead king-and-queen position, or reaches a non-dead
king-and-pawn state of strictly smaller potential. Strong induction on the
potential, together with `KQState.checkmateReachable_of_okB_of_not_dead`,
gives `CheckmateReachable` for every non-dead state.

The exhaustive check is the Boolean `KPState.checkAll`, verified by
`native_decide`. It examines each of the `2 · 64³` three-piece placements
once; it is not a search for mate. Captures of the pawn are excluded from the
policy: they leave two kings. Promotion is the engineered exit into the
known queen-versus-king mating apparatus.

States are stored in a *white-pawn frame*: White owns the pawn. A position
in which Black owns the pawn is reduced by a 180° rotation and a color swap.
`kingPawnCheckmateReachable` decides `CheckmateReachable` for a valid
king-and-pawn versus king position, and `kingPawnMatingLine` produces a
concrete mating sequence (or `[]` when the position is dead or not of this
material).
-/

namespace Chess


namespace Board

/-- White king on `wk`, black king on `bk`, and a pawn of color `c` on
`ps`. -/
def kingsPawnBoard (wk bk ps : Square) (c : Color) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = ps then some { color := c, kind := .pawn }
  else none

theorem kingsPawnBoard_white (wk bk ps : Square) (c : Color) :
    kingsPawnBoard wk bk ps c wk = some { color := .white, kind := .king } := by
  simp [kingsPawnBoard]

theorem kingsPawnBoard_black (wk bk ps : Square) (c : Color) (h : wk ≠ bk) :
    kingsPawnBoard wk bk ps c bk = some { color := .black, kind := .king } := by
  simp [kingsPawnBoard, h.symm]

theorem kingsPawnBoard_pawn (wk bk ps : Square) (c : Color)
    (hw : wk ≠ ps) (hb : bk ≠ ps) :
    kingsPawnBoard wk bk ps c ps = some { color := c, kind := .pawn } := by
  simp [kingsPawnBoard, hw.symm, hb.symm]

theorem kingsPawnBoard_other (wk bk ps s : Square) (c : Color)
    (hw : s ≠ wk) (hb : s ≠ bk) (hps : s ≠ ps) :
    kingsPawnBoard wk bk ps c s = none := by
  simp [kingsPawnBoard, hw, hb, hps]

theorem kingsPawnBoard_eq_white_king {wk bk ps s : Square} {c : Color}
    (h : kingsPawnBoard wk bk ps c s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsPawnBoard at h
  split_ifs at h <;> simp_all

theorem kingsPawnBoard_eq_black_king {wk bk ps s : Square} {c : Color}
    (h : kingsPawnBoard wk bk ps c s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsPawnBoard at h
  split_ifs at h <;> simp_all

theorem kingsPawnBoard_eq_pawn {wk bk ps s : Square} {c : Color}
    (h : kingsPawnBoard wk bk ps c s = some { color := c, kind := .pawn }) :
    s = ps := by
  unfold kingsPawnBoard at h
  split_ifs at h <;> simp_all

theorem kingsPawnBoard_isSome (wk bk ps s : Square) (c : Color) :
    ((kingsPawnBoard wk bk ps c) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = ps := by
  unfold kingsPawnBoard
  split_ifs <;> simp_all

theorem attacks_pawn {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .pawn }) :
    b.attacks s t = decide (PawnAttacks c s t) := by
  unfold attacks
  rw [h]
  simp [PieceKind.isSlider]

theorem kingsPawnBoard_occupiedBy_white (wk bk ps : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ps : wk ≠ ps) (_hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).occupiedBy .white =
      match c with
      | .white => {wk, ps}
      | .black => {wk} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsPawnBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsPawnBoard
    split_ifs <;> simp_all

theorem kingsPawnBoard_occupiedBy_black (wk bk ps : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ps : wk ≠ ps) (_hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).occupiedBy .black =
      match c with
      | .white => {bk}
      | .black => {bk, ps} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsPawnBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsPawnBoard
    split_ifs <;> simp_all

theorem kingsPawnBoard_kingSquares_white (wk bk ps : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ps : wk ≠ ps) (_hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsPawnBoard
  split_ifs <;> simp_all

theorem kingsPawnBoard_kingSquares_black (wk bk ps : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ps : wk ≠ ps) (_hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsPawnBoard
  split_ifs <;> simp_all

theorem kingsPawnBoard_occupied (wk bk ps : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ps : wk ≠ ps) (_hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).occupied = {wk, bk, ps} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsPawnBoard
  split_ifs <;> simp_all

theorem kingsPawnBoard_black_piece {wk bk ps s : Square} {c : Color}
    (h : (kingsPawnBoard wk bk ps c s).map (·.color) = some .black) :
    s = bk ∨ (c = .black ∧ s = ps) := by
  unfold kingsPawnBoard at h
  split_ifs at h <;> simp_all

theorem kingsPawnBoard_white_piece {wk bk ps s : Square} {c : Color}
    (h : (kingsPawnBoard wk bk ps c s).map (·.color) = some .white) :
    s = wk ∨ (c = .white ∧ s = ps) := by
  unfold kingsPawnBoard at h
  split_ifs at h <;> simp_all

theorem kingsPawnBoard_kingIsAttacked_white (wk bk ps : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_ps : wk ≠ ps) (hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨ (c = .black ∧ PawnAttacks .black ps wk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsPawnBoard_kingSquares_white wk bk ps c hwk_bk hwk_ps hbk_ps,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsPawnBoard_black_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsPawnBoard_black wk bk ps c hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [attacks_pawn (kingsPawnBoard_pawn wk bk ps Color.black hwk_ps hbk_ps)] at hatt
      exact Or.inr ⟨hc, of_decide_eq_true hatt⟩
  · intro h
    rcases h with hk | ⟨hc, hp⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsPawnBoard_black wk bk ps c hwk_bk]
      · rw [attacks_king (kingsPawnBoard_black wk bk ps c hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨ps, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsPawnBoard_pawn wk bk ps Color.black hwk_ps hbk_ps]
      · subst hc
        rw [attacks_pawn (kingsPawnBoard_pawn wk bk ps Color.black hwk_ps hbk_ps)]
        exact decide_eq_true hp

theorem kingsPawnBoard_kingIsAttacked_black (wk bk ps : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_ps : wk ≠ ps) (hbk_ps : bk ≠ ps) :
    (kingsPawnBoard wk bk ps c).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨ (c = .white ∧ PawnAttacks .white ps bk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsPawnBoard_kingSquares_black wk bk ps c hwk_bk hwk_ps hbk_ps,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsPawnBoard_white_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsPawnBoard_white wk bk ps c)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [attacks_pawn (kingsPawnBoard_pawn wk bk ps Color.white hwk_ps hbk_ps)] at hatt
      exact Or.inr ⟨hc, of_decide_eq_true hatt⟩
  · intro h
    rcases h with hk | ⟨hc, hp⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsPawnBoard_white]
      · rw [attacks_king (kingsPawnBoard_white wk bk ps c)]
        exact decide_eq_true hk
    · refine ⟨ps, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsPawnBoard_pawn wk bk ps Color.white hwk_ps hbk_ps]
      · subst hc
        rw [attacks_pawn (kingsPawnBoard_pawn wk bk ps Color.white hwk_ps hbk_ps)]
        exact decide_eq_true hp

theorem relocate_kingsPawnBoard_white (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate wk dst { color := .white, kind := .king } =
      kingsPawnBoard dst bk ps c := by
  funext s
  unfold relocate kingsPawnBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_black (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate bk dst { color := .black, kind := .king } =
      kingsPawnBoard wk dst ps c := by
  funext s
  unfold relocate kingsPawnBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_pawn (wk bk ps dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps c).relocate ps dst { color := c, kind := .pawn } =
      kingsPawnBoard wk bk dst c := by
  funext s
  unfold relocate kingsPawnBoard
  split_ifs <;> simp_all

theorem relocate_kingsPawnBoard_promote (wk bk ps dst : Square)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdp : dst ≠ ps) :
    (kingsPawnBoard wk bk ps .white).relocate ps dst { color := .white, kind := .queen } =
      kingsQueenBoard wk bk dst .white := by
  funext s
  unfold relocate kingsPawnBoard kingsQueenBoard
  split_ifs <;> simp_all

theorem relocate_capture_pawn_black (wk bk ps : Square)
    (_hne : wk ≠ bk) (_hwp : wk ≠ ps) (_hbp : bk ≠ ps) :
    (kingsPawnBoard wk bk ps .white).relocate bk ps
      { color := .black, kind := .king } =
      kingsBoard wk ps := by
  funext s
  unfold relocate kingsPawnBoard kingsBoard
  split_ifs <;> simp_all

theorem rot180_kingsPawnBoard_white (wk bk ps : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) :
    (kingsPawnBoard wk bk ps .white).rot180 =
      kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 .black := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_ps : wk.rot180 ≠ ps.rot180 := mt rot180_injective h2
  have hbk_ps : bk.rot180 ≠ ps.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsPawnBoard_white wk bk ps Color.white]
    change some { color := Color.black, kind := .king } =
      kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.black wk.rot180
    rw [kingsPawnBoard_black bk.rot180 wk.rot180 ps.rot180 Color.black hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsPawnBoard_black wk bk ps Color.white h1]
      change some { color := Color.white, kind := .king } =
        kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.black bk.rot180
      rw [kingsPawnBoard_white bk.rot180 wk.rot180 ps.rot180 Color.black]
    · by_cases hP : s.rot180 = ps
      · have hs : s = ps.rot180 := rot180_eq_iff.mp hP
        rw [hP, hs, kingsPawnBoard_pawn wk bk ps Color.white h2 h3]
        change some { color := Color.black, kind := .pawn } =
          kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.black ps.rot180
        rw [kingsPawnBoard_pawn bk.rot180 wk.rot180 ps.rot180 Color.black hbk_ps hwk_ps]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsP : s ≠ ps.rot180 := fun h => hP (rot180_eq_iff.mpr h)
        rw [kingsPawnBoard_other wk bk ps s.rot180 Color.white hA hB hP]
        change none = kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.black s
        rw [kingsPawnBoard_other bk.rot180 wk.rot180 ps.rot180 s Color.black hsB hsW hsP]

theorem rot180_kingsPawnBoard_black (wk bk ps : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) :
    (kingsPawnBoard wk bk ps .black).rot180 =
      kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 .white := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_ps : wk.rot180 ≠ ps.rot180 := mt rot180_injective h2
  have hbk_ps : bk.rot180 ≠ ps.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsPawnBoard_white wk bk ps Color.black]
    change some { color := Color.black, kind := .king } =
      kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.white wk.rot180
    rw [kingsPawnBoard_black bk.rot180 wk.rot180 ps.rot180 Color.white hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsPawnBoard_black wk bk ps Color.black h1]
      change some { color := Color.white, kind := .king } =
        kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.white bk.rot180
      rw [kingsPawnBoard_white bk.rot180 wk.rot180 ps.rot180 Color.white]
    · by_cases hP : s.rot180 = ps
      · have hs : s = ps.rot180 := rot180_eq_iff.mp hP
        rw [hP, hs, kingsPawnBoard_pawn wk bk ps Color.black h2 h3]
        change some { color := Color.white, kind := .pawn } =
          kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.white ps.rot180
        rw [kingsPawnBoard_pawn bk.rot180 wk.rot180 ps.rot180 Color.white hbk_ps hwk_ps]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsP : s ≠ ps.rot180 := fun h => hP (rot180_eq_iff.mpr h)
        rw [kingsPawnBoard_other wk bk ps s.rot180 Color.black hA hB hP]
        change none = kingsPawnBoard bk.rot180 wk.rot180 ps.rot180 Color.white s
        rw [kingsPawnBoard_other bk.rot180 wk.rot180 ps.rot180 s Color.white hsB hsW hsP]

end Board

namespace Position

/-- Board after a pawn move (no en passant capture; `p.enPassant` is
empty). Promotion is taken from `m.promotion`. -/
theorem boardAfter_pawn (p : Position) (m : Move) {c : Color}
    (hep : p.enPassant = none) :
    p.boardAfter m { color := c, kind := .pawn } =
      p.board.relocate m.src m.dst
        (match m.promotion with
          | some k => { color := c, kind := k }
          | none => { color := c, kind := .pawn }) := by
  unfold boardAfter
  have hking :
      (({ color := c, kind := PieceKind.pawn } : Piece).kind == PieceKind.king) = false := rfl
  have hep' : (p.enPassant == some m.dst) = false := by simp [hep]
  simp [hking, hep']
  rfl

theorem enPassantAfter_pawn_no_enemy (m : Move) (c : Color) (b : Board)
    (h : existsPawnAttacking b c.other
      ⟨m.src.file, pawnJumpOverRank c⟩ = false) :
    enPassantAfter m { color := c, kind := .pawn } b = none := by
  unfold enPassantAfter
  split_ifs with hcond
  · simp [h]
  · rfl

theorem some_pawn_ne_king {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .pawn } : Option Piece) =
      some { color := c₂, kind := .king }) : False := by
  simp at h

theorem some_king_ne_pawn' {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

/-- `p` contains only two kings and one pawn, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingAndPawn (p : Position) : Prop :=
  ∃ wk bk ps : Square, ∃ c : Color,
    wk ≠ bk ∧
      wk ≠ ps ∧
      bk ≠ ps ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsPawnBoard wk bk ps c ∧
      p.castling = ∅ ∧
      p.enPassant = none

theorem destOk_kingsPawnBoard {p : Position} {m : Move} {wk bk ps : Square}
    {c : Color}
    (hboard : p.board = Board.kingsPawnBoard wk bk ps c)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = ps := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsPawnBoard wk bk ps c m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsPawnBoard at hdst
    split_ifs at hdst with h1 h2 h3
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr h3

theorem destOk_toMove_of_dst_pawn {p : Position} {m : Move}
    {wk bk ps : Square} {c : Color}
    (hboard : p.board = Board.kingsPawnBoard wk bk ps c)
    (hwk_ps : wk ≠ ps) (hbk_ps : bk ≠ ps)
    (hdst : m.dst = ps) (hok : p.destOk m = true) :
    p.toMove = c.other := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsPawnBoard_pawn wk bk ps c hwk_ps hbk_ps] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem kingPawn_legalMove_core {p : Position} {m : Move} {wk bk ps : Square}
    {c : Color}
    (hboard : p.board = Board.kingsPawnBoard wk bk ps c)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = ps) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .pawn) ∧
        (piece.kind = .king → m.castlingSide? p.toMove = none ∧
          m.promotion = none ∧ p.board.attacks m.src m.dst = true) ∧
        (piece.kind = .pawn → p.pawnMoveOk m = true) := by
  have hm' : isLegalMove p m = true := hm
  unfold isLegalMove at hm'
  cases hsrcB : p.board m.src with
  | none => simp [hsrcB] at hm'
  | some piece =>
    simp only [hsrcB, Bool.and_eq_true] at hm'
    obtain ⟨⟨hcolDest, hifs⟩, hsafeB⟩ := hm'
    have hcol' : piece.color = p.toMove := beq_iff_eq.mp hcolDest.1
    have hdestOk : p.destOk m = true := hcolDest.2
    have hdstOr := destOk_kingsPawnBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsPawnBoard wk bk ps c m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .pawn := by
      have hsrc' := hsrc
      unfold Board.kingsPawnBoard at hsrc'
      split_ifs at hsrc' with _h1 _h2 _h3
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inr rfl
    have hside : piece.kind = .king → m.castlingSide? p.toMove = none ∧
        m.promotion = none ∧ p.board.attacks m.src m.dst = true := by
      intro hk
      have hpawn : (piece.kind == PieceKind.pawn) = false := by simp [hk]
      cases hopt : m.castlingSide? p.toMove with
      | none =>
        have hgeo : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
          simpa [hpawn, hk, hopt, Bool.and_eq_true, beq_iff_eq] using hifs
        exact ⟨rfl, hgeo.2, hgeo.1⟩
      | some _ =>
        have hs : (m.castlingSide? p.toMove).isSome = true := by simp [hopt]
        have hcastle := castleMoveOk_of_empty (m := m) hcstl
        have hifs' := hifs
        simp [hk, hs, hcastle] at hifs'
    have hpawn : piece.kind = .pawn → p.pawnMoveOk m = true := by
      intro hk
      have hpawnB : (piece.kind == PieceKind.pawn) = true := by simp [hk]
      simpa [hpawnB] using hifs
    exact ⟨hdestOk, hdstOr, hsafe, piece, rfl, hcol', hkind, hside, hpawn⟩

end Position


/-! ## Three-piece states (white-pawn frame) -/

/-- A king-and-pawn versus king position by the squares of its three
pieces and the side to move. White owns the pawn. -/
structure KPState where
  /-- The side to move. -/
  toMove : Color
  /-- White king (the pawn's support). -/
  wk : Square
  /-- Black king (the lone king). -/
  bk : Square
  /-- White pawn. -/
  ps : Square
deriving DecidableEq, Repr

/-- A move of the side to move: the white king, the black king, or the
pawn goes to `dst`. Captures are not represented. A pawn destination on
the eighth rank is a promotion to queen. -/
inductive KPMove where
  | king (dst : Square)
  | pawn (dst : Square)
deriving DecidableEq, Repr

namespace KPState

/-- All 64 squares. -/
def allSquares : List Square := KQState.allSquares

theorem mem_allSquares (x : Square) : x ∈ allSquares :=
  KQState.mem_allSquares x

/-- Index of a square in a 64-entry table. -/
def idx (q : Square) : Nat := KQState.idx q

/-- Squares a king on `k` can step to. -/
def kingNeighbors (k : Square) : List Square := KQState.kingNeighbors k

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := KQState.dist a b

/-- Chebyshev distance. -/
def cheb (x y x' y' : Nat) : Nat := KQState.cheb x y x' y'

/-- Forward pawn destinations on an empty board: one-square push, and
the two-square first move from rank 2. Occupancy is checked later. -/
def pawnDestsOf (ps : Square) : List Square :=
  let single : List Square :=
    if h : ps.rank.val + 1 < 8 then
      [⟨ps.file, ⟨ps.rank.val + 1, h⟩⟩]
    else []
  let double : List Square :=
    if ps.rank.val == 1 then [⟨ps.file, ⟨3, by omega⟩⟩] else []
  single ++ double

/-- Pawn destinations of every square, indexed by `idx`. -/
def pawnDestsTable : Array (List Square) := (allSquares.map pawnDestsOf).toArray

/-- Squares a white pawn on `ps` can advance to on an empty board. -/
def pawnDests (ps : Square) : List Square := pawnDestsTable.getD (idx ps) []

/-- The black king on `bk` is attacked by the white king `wk` or the pawn
`ps`. -/
def kingAttackedBlack (wk bk ps : Square) : Bool :=
  decide (KingAttacks wk bk) || decide (PawnAttacks .white ps bk)

/-- The white king on `wk` is attacked by the black king `bk`. -/
def kingAttackedWhite (wk bk : Square) : Bool :=
  decide (KingAttacks wk bk)

/-- The king of `c` among `wk`, `bk`. -/
def king (s : KPState) : Color → Square
  | .white => s.wk
  | .black => s.bk

/-- The king of `c` is attacked. -/
def inCheckB (s : KPState) (c : Color) : Bool :=
  match c with
  | .white => kingAttackedWhite s.wk s.bk
  | .black => kingAttackedBlack s.wk s.bk s.ps

/-- Geometric legality of the white king step `wk → d`. Captures are
excluded. -/
def fastKingW (wk d bk ps : Square) : Bool :=
  decide (KingAttacks wk d) && d != bk && d != ps && !decide (KingAttacks bk d)

/-- Geometric legality of the black king step `bk → d`, including capture
of an unprotected pawn. -/
def fastKingB (wk d bk ps : Square) : Bool :=
  decide (KingAttacks bk d) && d != wk &&
    (if d == ps then !decide (KingAttacks wk d)
      else !decide (KingAttacks wk d) && !decide (PawnAttacks .white ps d))

/-- Geometric legality of the white pawn advance `ps → d`. Captures are
excluded. -/
def fastPawn (wk d bk ps : Square) : Bool :=
  d.file == ps.file && d != wk && d != bk &&
    (decide (Square.deltaRank ps d = (1 : ℤ)) ||
      (ps.rank.val == 1 && d.rank.val == 3 &&
        decide ((⟨ps.file, ⟨2, by omega⟩⟩ : Square) ≠ wk) &&
        decide ((⟨ps.file, ⟨2, by omega⟩⟩ : Square) ≠ bk)))

/-- The state describes a legal three-piece position: distinct squares,
kings not adjacent, pawn off the back ranks, and the side not to move
not in check. -/
def okB (s : KPState) : Bool :=
  s.wk != s.bk && s.wk != s.ps && s.bk != s.ps &&
    !decide (KingAttacks s.wk s.bk) &&
    decide (1 ≤ s.ps.rank.val ∧ s.ps.rank.val ≤ 6) &&
    !s.inCheckB s.toMove.other

/-- Whether this move is a promotion to queen. -/
def isPromotion : KPMove → Bool
  | .pawn d => d.rank.val == 7
  | .king _ => false

/-- Geometric legality of a (non-capturing) move in an `okB` state. -/
def fastLegal (s : KPState) : KPMove → Bool
  | .king d =>
    match s.toMove with
    | .white => fastKingW s.wk d s.bk s.ps
    | .black => d != s.ps && fastKingB s.wk d s.bk s.ps
  | .pawn d =>
    s.toMove == .white && fastPawn s.wk d s.bk s.ps

/-- The state after a non-promoting move. Promotion is not applied here:
the pawn would occupy the eighth rank, which is not a `KPState`. -/
def apply (s : KPState) : KPMove → KPState
  | .king d =>
    match s.toMove with
    | .white => { s with toMove := .black, wk := d }
    | .black => { s with toMove := .white, bk := d }
  | .pawn d =>
    { s with toMove := .black, ps := d }

/-- King-and-queen state after promoting on `d`. -/
def promoKQ (s : KPState) (d : Square) : KQState :=
  ⟨.black, s.wk, s.bk, d⟩

/-- Promoting on `d` yields a legal, non-dead king-and-queen position
(or an immediate queen mate). -/
def promoOk (s : KPState) (d : Square) : Bool :=
  let kq := s.promoKQ d
  kq.okB && (kq.mateB || !kq.deadB)

/-- The side to move is checkmated: Black is in check from the pawn and
every king step is onto the white king, onto an attacked square, or onto
the protected pawn. -/
def mateB (s : KPState) : Bool :=
  s.toMove == .black && kingAttackedBlack s.wk s.bk s.ps &&
    (kingNeighbors s.bk).all fun d =>
      d == s.wk || decide (KingAttacks s.wk d) ||
        (d != s.ps && decide (PawnAttacks .white s.ps d))

/-- Whether some non-capturing move is geometrically legal. -/
def hasNoncaptureLegal (s : KPState) : Bool :=
  match s.toMove with
  | .white =>
    (kingNeighbors s.wk).any (fun d => fastKingW s.wk d s.bk s.ps) ||
      (pawnDests s.ps).any (fun d => fastPawn s.wk d s.bk s.ps)
  | .black =>
    (kingNeighbors s.bk).any (fun d => d != s.ps && fastKingB s.wk d s.bk s.ps)

/-- The state is dead for helpmate: not checkmate, and the only legal
continuations (if any) capture the pawn. -/
def deadB (s : KPState) : Bool :=
  !s.mateB && !s.hasNoncaptureLegal

/-- The chess position of the state. -/
def toPosition (s : KPState) : Position where
  board := Board.kingsPawnBoard s.wk s.bk s.ps .white
  toMove := s.toMove
  castling := ∅
  enPassant := none

/-- The chess move of a state move. A pawn step onto the eighth rank is a
queen promotion. -/
def move (s : KPState) : KPMove → Move
  | .king d => Move.std (s.king s.toMove) d
  | .pawn d =>
    if d.rank.val == 7 then Move.promote s.ps d .queen
    else Move.std s.ps d

/-! ### Potential -/

/-- Supporting square for the white king: sixth rank, adjacent file,
not blocking the pawn. -/
def wkTarget (ps : Square) : Square :=
  if h0 : ps.file.val = 0 then ⟨⟨1, by omega⟩, ⟨5, by omega⟩⟩
  else if h7 : ps.file.val = 7 then ⟨⟨6, by omega⟩, ⟨5, by omega⟩⟩
  else ⟨⟨ps.file.val + 1, by omega⟩, ⟨5, by omega⟩⟩

/-- Far eighth-rank corner, away from the pawn's file. -/
def bkTarget (ps : Square) : Square :=
  if ps.file.val ≤ 3 then ⟨⟨7, by omega⟩, ⟨7, by omega⟩⟩
  else ⟨⟨0, by omega⟩, ⟨7, by omega⟩⟩

/-- Penalty for parking the white king on the pawn's file in front of
it, or on the promotion square. -/
def zoneW (wk ps : Square) : Nat :=
  if wk.file.val == ps.file.val && wk.rank.val > ps.rank.val then 6
  else if wk.file.val == ps.file.val && wk.rank.val == 7 then 8
  else 0

/-- The pawn is adjacent to the black king and not protected. -/
def hangingPawn (s : KPState) : Bool :=
  decide (KingAttacks s.bk s.ps) && !decide (KingAttacks s.wk s.ps)

/-- White king distance to its supporting square. -/
def workWk (s : KPState) : Nat :=
  let t := wkTarget s.ps
  3 * cheb s.wk.file.val s.wk.rank.val t.file.val t.rank.val +
    dist s.wk.file.val t.file.val + dist s.wk.rank.val t.rank.val +
    zoneW s.wk s.ps

/-- Black king distance to the far corner, plus a penalty for blocking
the pawn's file. -/
def workBk (s : KPState) : Nat :=
  let t := bkTarget s.ps
  let block :=
    (if s.bk.file.val == s.ps.file.val && s.bk.rank.val > s.ps.rank.val then 4
      else 0) +
      (if s.bk.file.val == s.ps.file.val && s.bk.rank.val == 7 then 4 else 0) +
      (if decide (KingAttacks s.bk s.ps) then 1 else 0)
  3 * cheb s.bk.file.val s.bk.rank.val t.file.val t.rank.val +
    dist s.bk.file.val t.file.val + dist s.bk.rank.val t.rank.val + block

/-- Distance of the pawn from the seventh rank. -/
def pawnWork (s : KPState) : Nat := 6 - s.ps.rank.val

/-- White's contribution to the potential. -/
def whitePart (s : KPState) : Nat :=
  workWk s + (if s.hangingPawn then 10 else 0)

/-- Black's contribution to the potential. -/
def blackPart (s : KPState) : Nat := workBk s

/-- Tempo: the side that has finished its work must still move. -/
def tempo (s : KPState) (w b : Nat) : Nat :=
  match s.toMove with
  | .white => if w == 0 then 1 else 0
  | .black => if b == 0 then 1 else 0

/-- Potential without the check bonus. -/
def muBase (s : KPState) : Nat :=
  let w := s.whitePart
  let b := s.blackPart
  let p := 12 * s.pawnWork
  2 * (p + w + b) + tempo s w b

/-- Bonus so that fleeing check lowers the potential. -/
def checkBonus (s : KPState) : Nat := if s.inCheckB s.toMove then 80 else 0

/-- Lyapunov potential of the state. -/
def mu (s : KPState) : Nat := s.muBase + s.checkBonus

/-! ### Scripted policy -/

/-- The move is legal, leads to a legal state, and does not enter a dead
position unless it mates or promotes to a live queen. -/
def oneOk (s : KPState) (m : KPMove) : Bool :=
  s.fastLegal m &&
    match m with
    | .pawn d =>
      if d.rank.val == 7 then s.promoOk d
      else
        let s1 := s.apply m
        s1.okB && (s1.mateB || !s1.deadB)
    | .king _ =>
      let s1 := s.apply m
      s1.okB && (s1.mateB || !s1.deadB)

/-- The move is legal and mates, promotes safely, or lowers the
potential without entering a dead position. -/
def progressMove (s : KPState) (x : Nat) (m : KPMove) : Bool :=
  s.fastLegal m &&
    match m with
    | .pawn d =>
      if d.rank.val == 7 then s.promoOk d
      else
        let s1 := s.apply m
        s1.okB && (s1.mateB || (s1.mu < x && !s1.deadB))
    | .king _ =>
      let s1 := s.apply m
      s1.okB && (s1.mateB || (s1.mu < x && !s1.deadB))

/-- Score of a move: `0` for mate or a mating promotion, `1` for a
non-mating promotion, otherwise one more than the new potential. -/
def score (s : KPState) (m : KPMove) : Nat :=
  match m with
  | .pawn d =>
    if d.rank.val == 7 then
      if (s.promoKQ d).mateB then 0 else 1
    else
      let s1 := s.apply m
      if s1.mateB then 0 else s1.muBase + 1
  | .king _ =>
    let s1 := s.apply m
    if s1.mateB then 0 else s1.muBase + 1

/-- The legal non-dead move with the smallest score, first wins ties. -/
def bestOf (s : KPState) (ms : List KPMove) : Option KPMove :=
  let best := ms.foldl (init := (none : Option (KPMove × Nat))) fun best m =>
    if s.oneOk m then
      let sc := s.score m
      match best with
      | none => some (m, sc)
      | some (_, bsc) => if sc < bsc then some (m, sc) else best
    else best
  best.map (·.1)

/-- First legal move that does not raise the potential and does not
stalemate (or a safe promotion). -/
def waitMove (s : KPState) : Option KPMove :=
  let x := s.mu
  match s.toMove with
  | .white =>
    match (pawnDests s.ps).find? fun d =>
        let m := KPMove.pawn d
        s.fastLegal m &&
          (if d.rank.val == 7 then s.promoOk d
            else (s.apply m).okB && (s.apply m).mu ≤ x && !(s.apply m).deadB) with
    | some d => some (.pawn d)
    | none =>
      (kingNeighbors s.wk).findSome? fun d =>
        let m := KPMove.king d
        if s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x &&
            !(s.apply m).deadB then
          some m
        else none
  | .black =>
    (kingNeighbors s.bk).findSome? fun d =>
      let m := KPMove.king d
      if d != s.ps && s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x &&
          !(s.apply m).deadB then
        some m
      else none

/-- Unhang the pawn if it is hanging and White is to move. -/
def unhangPawn (s : KPState) : Option KPMove :=
  if s.toMove == .white && s.hangingPawn then
    let x := s.mu
    match (pawnDests s.ps).find? fun d => s.progressMove x (.pawn d) with
    | some d => some (.pawn d)
    | none =>
      match (kingNeighbors s.wk).find? fun d => s.progressMove x (.king d) with
      | some d => some (.king d)
      | none =>
        match (pawnDests s.ps).find? fun d =>
            s.oneOk (.pawn d) && (d.rank.val == 7 || !decide (KingAttacks s.bk d)) with
        | some d => some (.pawn d)
        | none =>
          (kingNeighbors s.wk).findSome? fun d =>
            if s.oneOk (.king d) && decide (KingAttacks d s.ps) then
              some (.king d)
            else none
  else none

/-- The scripted move. White unhangs first, then prefers a pawn progress
(especially promotion), else a king progress, else a waiting move, else
the legal move with the best score. -/
def scriptMove (s : KPState) : Option KPMove :=
  match s.unhangPawn with
  | some m => some m
  | none =>
    let x := s.mu
    match s.toMove with
    | .black =>
      let kingMoves := (kingNeighbors s.bk).filterMap fun d =>
        if d == s.ps then none else some (KPMove.king d)
      if s.inCheckB .black then s.bestOf kingMoves
      else
        match s.bestOf (kingMoves.filter fun m => s.progressMove x m) with
        | some m => some m
        | none =>
          match s.waitMove with
          | some m => some m
          | none => s.bestOf kingMoves
    | .white =>
      let kingMoves := (kingNeighbors s.wk).map KPMove.king
      let pawnMoves := (pawnDests s.ps).map KPMove.pawn
      match (pawnDests s.ps).find? fun d => s.progressMove x (.pawn d) with
      | some d => some (.pawn d)
      | none =>
        match (kingNeighbors s.wk).find? fun d => s.progressMove x (.king d) with
        | some d => some (.king d)
        | none =>
          match s.waitMove with
          | some m => some m
          | none => s.bestOf (pawnMoves ++ kingMoves)

/-- The state has reached the goal relative to `s0`: it is checkmate, or
its potential is below that of `s0` and it is not dead. -/
def goal (s0 s : KPState) : Bool :=
  s.mateB || (s.mu < s0.mu && !s.deadB)

/-- Whether `m` from `s` is a successful promotion or a `goal` state. -/
def goalMove (s0 s : KPState) (m : KPMove) : Bool :=
  match m with
  | .pawn d =>
    if d.rank.val == 7 then s.promoOk d
    else goal s0 (s.apply m)
  | .king _ => goal s0 (s.apply m)

/-- Within `n` plies of scripted play from `s`, the goal relative to `s0`
is reached (or a safe promotion occurs). Each ply first probes a waiting
move, then follows the script. Every played move is checked with `oneOk`. -/
def chain (s0 : KPState) : KPState → Nat → Bool
  | _, 0 => false
  | s, n + 1 =>
    (match s.waitMove with
      | some m => s.oneOk m && goalMove s0 s m
      | none => false) ||
    match s.scriptMove with
    | none => false
    | some m =>
      s.oneOk m &&
        (goalMove s0 s m ||
          match m with
          | .pawn d =>
            if d.rank.val == 7 then false
            else chain s0 (s.apply m) n
          | .king _ => chain s0 (s.apply m) n)

/-- Plies of scripted play allowed to lower the potential. Four suffice;
six leaves a margin. -/
def window : Nat := 6

/-- A state passes: it is illegal, checkmate, dead, or the script lowers
its potential or promotes. -/
def checkState (s : KPState) : Bool :=
  !s.okB || s.mateB || s.deadB || chain s s window

/-- Every placement of the three pieces, with either side to move, is
covered. -/
def checkAll : Bool :=
  allSquares.all fun wk =>
    allSquares.all fun bk =>
      allSquares.all fun ps =>
        checkState ⟨.white, wk, bk, ps⟩ && checkState ⟨.black, wk, bk, ps⟩

/-! ### The mating line -/

/-- The moves of a successful `chain` from `s` relative to `s0`, if any. -/
def chainPath (s0 : KPState) : KPState → Nat → Option (List KPMove)
  | _, 0 => none
  | s, n + 1 =>
    let viaWait : Option (List KPMove) :=
      match s.waitMove with
      | some m => if s.oneOk m && goalMove s0 s m then some [m] else none
      | none => none
    match viaWait with
    | some ms => some ms
    | none =>
      match s.scriptMove with
      | none => none
      | some m =>
        if s.oneOk m then
          if goalMove s0 s m then some [m]
          else
            match m with
            | .pawn d =>
              if d.rank.val == 7 then none
              else (chainPath s0 (s.apply m) n).map (m :: ·)
            | .king _ => (chainPath s0 (s.apply m) n).map (m :: ·)
        else none

/-- The state after a sequence of non-promoting moves. -/
def applyAll (s : KPState) (ms : List KPMove) : KPState :=
  ms.foldl apply s

/-- Whether `ms` contains a promoting pawn move. -/
def seqPromotes : List KPMove → Bool
  | [] => false
  | m :: ms => isPromotion m || seqPromotes ms

/-- The mating line in state moves; `fuel` bounds the number of rounds. -/
def matingLineAux : KPState → Nat → List KPMove
  | _, 0 => []
  | s, fuel + 1 =>
    if s.mateB || s.deadB then []
    else
      match chainPath s s window with
      | some ms =>
        if seqPromotes ms then ms
        else ms ++ matingLineAux (s.applyAll ms) fuel
      | none => []

/-- The chess moves of a sequence of state moves. -/
def toMoves : KPState → List KPMove → List Move
  | _, [] => []
  | s, m :: ms => s.move m :: toMoves (s.apply m) ms

/-- The king-and-queen state after a promoting sequence, if the last move
promotes. -/
def promoAfter : KPState → List KPMove → Option KQState
  | _, [] => none
  | s, m :: ms =>
    match m with
    | .pawn d =>
      if d.rank.val == 7 then
        if ms = [] then some (s.promoKQ d) else none
      else promoAfter (s.apply m) ms
    | .king _ => promoAfter (s.apply m) ms

/-- The engineered mating line from `s`, as chess moves. After a
promotion the king-and-queen mating line is appended. -/
def matingLine (s : KPState) : List Move :=
  let ms := matingLineAux s (2 * s.mu + 2)
  let chess := s.toMoves ms
  match promoAfter s ms with
  | some kq => chess ++ kq.matingLine
  | none => chess

/-- The three-piece state of a white-pawn position, if the board holds
exactly those pieces in a legal arrangement. -/
def ofPositionWhite? (p : Position) : Option KPState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .white, kind := .pawn }) with
  | some wk, some bk, some ps =>
    if (⟨p.toMove, wk, bk, ps⟩ : KPState).okB && (allSquares.all fun q =>
          p.board q == Board.kingsPawnBoard wk bk ps .white q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove, wk, bk, ps⟩
    else none
  | _, _, _ => none

/-- The three-piece state of a black-pawn position, rotated into the
white-pawn frame. -/
def ofPositionBlack? (p : Position) : Option KPState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .pawn }) with
  | some wk, some bk, some ps =>
    if (⟨p.toMove.other, bk.rot180, wk.rot180, ps.rot180⟩ : KPState).okB &&
        (allSquares.all fun q =>
          p.board q == Board.kingsPawnBoard wk bk ps .black q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove.other, bk.rot180, wk.rot180, ps.rot180⟩
    else none
  | _, _, _ => none

/-- The white-pawn-frame state of a king-and-pawn versus king position. -/
def ofPosition? (p : Position) : Option KPState :=
  match ofPositionWhite? p with
  | some s => some s
  | none => ofPositionBlack? p

/-- Every white-king file is covered by the script. -/
def checkFile (f : Fin 8) : Bool :=
  (List.finRange 8).all fun r =>
    allSquares.all fun bk =>
      allSquares.all fun ps =>
        checkState ⟨.white, ⟨f, r⟩, bk, ps⟩ &&
          checkState ⟨.black, ⟨f, r⟩, bk, ps⟩

set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile0 : checkFile 0 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile1 : checkFile 1 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile2 : checkFile 2 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile3 : checkFile 3 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile4 : checkFile 4 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile5 : checkFile 5 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile6 : checkFile 6 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KP vs K states.
theorem checkFile7 : checkFile 7 = true := by native_decide

theorem checkFile_true (f : Fin 8) : checkFile f = true :=
  match f with
  | ⟨0, _⟩ => checkFile0
  | ⟨1, _⟩ => checkFile1
  | ⟨2, _⟩ => checkFile2
  | ⟨3, _⟩ => checkFile3
  | ⟨4, _⟩ => checkFile4
  | ⟨5, _⟩ => checkFile5
  | ⟨6, _⟩ => checkFile6
  | ⟨7, _⟩ => checkFile7

theorem checkAll_true : checkAll = true := by
  refine List.all_eq_true.mpr ?_
  intro wk _
  rcases wk with ⟨f, r⟩
  exact (List.all_eq_true.mp (checkFile_true f)) r (by simp [List.mem_finRange])

end KPState

namespace KPState

open Position

theorem kingAttacks_ne {s t : Square} (h : KingAttacks s t) : s ≠ t := h.1

theorem mem_kingNeighbors {k d : Square} (h : KingAttacks k d) :
    d ∈ kingNeighbors k :=
  KQState.mem_kingNeighbors h

theorem kingAttacks_of_mem_kingNeighbors {k d : Square}
    (h : d ∈ kingNeighbors k) : KingAttacks k d :=
  KQState.kingAttacks_of_mem_kingNeighbors h

theorem castlingSide_none_of_kingAttacks (c : Color) {s t : Square}
    (h : KingAttacks s t) : (Move.std s t).castlingSide? c = none :=
  KQState.castlingSide_none_of_kingAttacks c h

theorem okB_iff (s : KPState) :
    s.okB = true ↔
      s.wk ≠ s.bk ∧ s.wk ≠ s.ps ∧ s.bk ≠ s.ps ∧
        ¬ KingAttacks s.wk s.bk ∧
          1 ≤ s.ps.rank.val ∧ s.ps.rank.val ≤ 6 ∧
            s.inCheckB s.toMove.other = false := by
  simp [okB, and_assoc]

theorem kingAttackedBlack_iff (wk bk ps : Square) :
    kingAttackedBlack wk bk ps = true ↔
      KingAttacks wk bk ∨ PawnAttacks .white ps bk := by
  simp [kingAttackedBlack, Bool.or_eq_true]

theorem kingIsAttacked_white_eq (wk bk ps : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) :
    (Board.kingsPawnBoard wk bk ps .white).kingIsAttacked .white =
      kingAttackedWhite wk bk := by
  rw [Bool.eq_iff_iff, Board.kingsPawnBoard_kingIsAttacked_white wk bk ps .white h1 h2 h3]
  simp [kingAttackedWhite, kingAttacks_symmetric]

theorem kingIsAttacked_black_eq (wk bk ps : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ ps) (h3 : bk ≠ ps) :
    (Board.kingsPawnBoard wk bk ps .white).kingIsAttacked .black =
      kingAttackedBlack wk bk ps := by
  rw [Bool.eq_iff_iff, Board.kingsPawnBoard_kingIsAttacked_black wk bk ps .white h1 h2 h3]
  simp [kingAttackedBlack_iff]

theorem kingIsAttacked_eq (s : KPState) (hok : s.okB = true) (c : Color) :
    s.toPosition.board.kingIsAttacked c = s.inCheckB c := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  cases c with
  | white => exact kingIsAttacked_white_eq _ _ _ h1 h2 h3
  | black => exact kingIsAttacked_black_eq _ _ _ h1 h2 h3

theorem fastKingW_iff (wk d bk ps : Square) :
    fastKingW wk d bk ps = true ↔
      KingAttacks wk d ∧ d ≠ bk ∧ d ≠ ps ∧ ¬ KingAttacks bk d := by
  simp [fastKingW, and_assoc]

theorem fastKingB_iff (wk d bk ps : Square) :
    fastKingB wk d bk ps = true ↔
      KingAttacks bk d ∧ d ≠ wk ∧
        (d = ps ∧ ¬ KingAttacks wk d ∨
          d ≠ ps ∧ ¬ KingAttacks wk d ∧ ¬ PawnAttacks .white ps d) := by
  unfold fastKingB
  by_cases hd : d = ps
  · simp [hd, and_assoc]
  · simp [hd, and_assoc]

theorem fastPawn_iff (wk d bk ps : Square) :
    fastPawn wk d bk ps = true ↔
      d.file = ps.file ∧ d ≠ wk ∧ d ≠ bk ∧
        (Square.deltaRank ps d = 1 ∨
          (ps.rank.val = 1 ∧ d.rank.val = 3 ∧
            (⟨ps.file, ⟨2, by omega⟩⟩ : Square) ≠ wk ∧
            (⟨ps.file, ⟨2, by omega⟩⟩ : Square) ≠ bk)) := by
  simp [fastPawn, and_assoc]

theorem ne_of_kingsPawnBoard_eq_none {wk bk ps s : Square} {c : Color}
    (h : Board.kingsPawnBoard wk bk ps c s = none) :
    s ≠ wk ∧ s ≠ bk ∧ s ≠ ps := by
  unfold Board.kingsPawnBoard at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem existsPawnAttacking_whitePawnBoard (wk bk ps t : Square) :
    existsPawnAttacking (Board.kingsPawnBoard wk bk ps .white) .black t = false := by
  cases h : existsPawnAttacking (Board.kingsPawnBoard wk bk ps .white) .black t
  · rfl
  · obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp h
    have hp : Board.kingsPawnBoard wk bk ps .white s =
        some { color := .black, kind := .pawn } := (hasPawn_eq_true_iff _ _ _).mp hs
    unfold Board.kingsPawnBoard at hp
    split_ifs at hp <;> cases hp

theorem existsPawnAttacking_kingsQueenBoard_white (wk bk qs t : Square) :
    existsPawnAttacking (Board.kingsQueenBoard wk bk qs .white) .black t = false := by
  cases h : existsPawnAttacking (Board.kingsQueenBoard wk bk qs .white) .black t
  · rfl
  · obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp h
    have hp : Board.kingsQueenBoard wk bk qs .white s =
        some { color := .black, kind := .pawn } := (hasPawn_eq_true_iff _ _ _).mp hs
    unfold Board.kingsQueenBoard at hp
    split_ifs at hp <;> cases hp

theorem enPassantAfter_whitePawn (m : Move) (wk bk ps : Square) :
    enPassantAfter m { color := .white, kind := .pawn }
      (Board.kingsPawnBoard wk bk ps .white) = none :=
  enPassantAfter_pawn_no_enemy m Color.white _
    (existsPawnAttacking_whitePawnBoard wk bk ps _)

theorem enPassantAfter_whitePawn_on_queenBoard (m : Move) (wk bk qs : Square) :
    enPassantAfter m { color := .white, kind := .pawn }
      (Board.kingsQueenBoard wk bk qs .white) = none :=
  enPassantAfter_pawn_no_enemy m Color.white _
    (existsPawnAttacking_kingsQueenBoard_white wk bk qs _)

/-! ### Playing moves -/

theorem play_whiteKing {s : KPState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastKingW s.wk d s.bk s.ps = true) :
    isLegalMove s.toPosition (Move.std s.wk d) = true ∧
      s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdbk, hdps, hsafe⟩ := (fastKingW_iff _ _ _ _).mp hm
  have hdwk : d ≠ s.wk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.wk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsPawnBoard s.wk s.bk s.ps .white s.wk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsPawnBoard_white _ _ _ _
  have hdstNone : s.toPosition.board (Move.std s.wk d).dst = none :=
    Board.kingsPawnBoard_other _ _ _ _ _ hdwk hdbk hdps
  have hside : (Move.std s.wk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.wk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.wk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsPawnBoard d s.bk s.ps .white := by
    rw [hba]
    change (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.wk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsPawnBoard_white _ _ _ _ _ h1 h2 h3 hdwk hdbk hdps
  have hplay' : s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_king]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.wk d).src (Move.std s.wk d).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.wk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .black, wk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsPawnBoard d s.bk s.ps .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq d s.bk s.ps hdbk hdps h3]
    simpa [kingAttackedWhite] using mt kingAttacks_symmetric.mp hsafe
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.wk d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.wk d).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem play_blackKing {s : KPState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : d ≠ s.ps)
    (hmv : fastKingB s.wk d s.bk s.ps = true) :
    isLegalMove s.toPosition (Move.std s.bk d) = true ∧
      s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
  have hdbk : d ≠ s.bk := (kingAttacks_ne hka).symm
  have hdps : d ≠ s.ps := hm
  have hsrcP : s.toPosition.board (Move.std s.bk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsPawnBoard s.wk s.bk s.ps .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsPawnBoard_black _ _ _ _ h1
  have hdstNone : s.toPosition.board (Move.std s.bk d).dst = none :=
    Board.kingsPawnBoard_other _ _ _ _ _ hdwk hdbk hdps
  have hside : (Move.std s.bk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsPawnBoard s.wk d s.ps .white := by
    rw [hba]
    change (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.bk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsPawnBoard_black _ _ _ _ _ h1 h2 h3 hdwk hdbk hdps
  have hplay' : s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_king]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.bk d).src (Move.std s.bk d).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafeK : ¬ KingAttacks s.wk d := by
    rcases hrest with ⟨_, h⟩ | ⟨_, h, _⟩
    · exact h
    · exact h
  have hnP : ¬ PawnAttacks .white s.ps d := by
    rcases hrest with ⟨heq, _⟩ | ⟨_, _, h⟩
    · exact (hm heq).elim
    · exact h
  have hsafe' : (s.toPosition.play (Move.std s.bk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .white, bk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsPawnBoard s.wk d s.ps .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk d s.ps hdwk.symm h2 hdps]
    simp [kingAttackedBlack, hsafeK, hnP]
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.bk d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.bk d).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

set_option maxHeartbeats 0 in
-- `native_decide` of pawnMoveOk for every white-pawn push.
theorem pawnMoveOk_aux (wk bk ps d : Square) :
    (if fastPawn wk d bk ps && (⟨.white, wk, bk, ps⟩ : KPState).okB then
      (⟨.white, wk, bk, ps⟩ : KPState).toPosition.pawnMoveOk
        ((⟨.white, wk, bk, ps⟩ : KPState).move (.pawn d))
     else true) = true := by
  revert wk bk ps d
  native_decide

theorem pawnMoveOk_of_fastPawn {s : KPState} {d : Square}
    (hok : s.okB = true) (ht : s.toMove = .white)
    (hm : fastPawn s.wk d s.bk s.ps = true) :
    s.toPosition.pawnMoveOk (s.move (.pawn d)) = true := by
  rcases s with ⟨tm, wk, bk, ps⟩
  subst ht
  have h := pawnMoveOk_aux wk bk ps d
  have hcond : (fastPawn wk d bk ps &&
      (⟨.white, wk, bk, ps⟩ : KPState).okB) = true := by
    exact (Bool.and_eq_true_iff.mpr ⟨hm, hok⟩)
  simp only [hcond, ↓reduceIte] at h
  exact h

set_option maxHeartbeats 0 in
-- `native_decide` recovering fastPawn from pawnMoveOk on an empty destination.
theorem fastPawn_of_pawnMoveOk_aux (wk bk ps d : Square) (pr : Option PieceKind) :
    (if (⟨.white, wk, bk, ps⟩ : KPState).okB &&
        (Board.kingsPawnBoard wk bk ps .white d).isNone &&
        (⟨.white, wk, bk, ps⟩ : KPState).toPosition.pawnMoveOk ⟨ps, d, pr⟩ then
      fastPawn wk d bk ps
     else true) = true := by
  revert wk bk ps d pr
  native_decide

theorem play_pawn {s : KPState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastPawn s.wk d s.bk s.ps = true)
    (hnp : d.rank.val ≠ 7) :
    isLegalMove s.toPosition (Move.std s.ps d) = true ∧
      s.toPosition.play (Move.std s.ps d) = (s.apply (.pawn d)).toPosition := by
  obtain ⟨h1, h2, h3, hna, _, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hfile, hdwk, hdbk, hstep⟩ := (fastPawn_iff _ _ _ _).mp hm
  have hdps : d ≠ s.ps := by
    intro heq
    rcases hstep with h1s | h2s
    · have h0 : Square.deltaRank s.ps d = 0 := by simp [Square.deltaRank, heq]
      exact (by decide : (0 : ℤ) ≠ 1) (h0.symm.trans h1s)
    · have : d.rank.val = s.ps.rank.val := by simp [heq]
      omega
  have hsrcP : s.toPosition.board (Move.std s.ps d).src =
      some { color := s.toPosition.toMove, kind := .pawn } := by
    change Board.kingsPawnBoard s.wk s.bk s.ps .white s.ps =
      some { color := s.toMove, kind := .pawn }
    rw [ht]
    exact Board.kingsPawnBoard_pawn _ _ _ _ h2 h3
  have hdstNone : s.toPosition.board (Move.std s.ps d).dst = none :=
    Board.kingsPawnBoard_other _ _ _ _ _ hdwk hdbk hdps
  have hplay := play_of_some s.toPosition (Move.std s.ps d) hsrcP
  have hba := boardAfter_pawn s.toPosition (Move.std s.ps d) (c := .white) rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.ps d)
      { color := .white, kind := .pawn } =
      Board.kingsPawnBoard s.wk s.bk d .white := by
    rw [hba]
    change (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.ps d
      { color := .white, kind := .pawn } = _
    exact Board.relocate_kingsPawnBoard_pawn _ _ _ _ _ h1 h2 h3 hdwk hdbk hdps
  have htm : s.toPosition.toMove = Color.white := by simp [toPosition, ht]
  have hplay' : s.toPosition.play (Move.std s.ps d) = (s.apply (.pawn d)).toPosition := by
    rw [hplay, htm, hboard']
    refine Position.ext rfl (by simp [toPosition, apply])
      (by simp [toPosition, apply, castlingAfter_empty])
      (enPassantAfter_whitePawn (Move.std s.ps d) s.wk s.bk d)
  refine ⟨?_, hplay'⟩
  have hrankB : (d.rank.val == 7) = false := by
    cases h : (d.rank.val == 7)
    · rfl
    · exact (hnp (beq_iff_eq.mp h)).elim
  have hmv : s.move (.pawn d) = Move.std s.ps d := by simp [move, hrankB]
  have hpok : s.toPosition.pawnMoveOk (Move.std s.ps d) = true := by
    simpa [hmv] using pawnMoveOk_of_fastPawn hok ht hm
  have hsafe' : (s.toPosition.play (Move.std s.ps d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.pawn d) = { s with toMove := .black, ps := d } := by
      simp [apply]
    rw [hplay', happ]
    change (Board.kingsPawnBoard s.wk s.bk d .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq s.wk s.bk d h1 hdwk.symm hdbk.symm]
    simpa [kingAttackedWhite] using hna
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.ps d) hdstNone]
  simp only [Bool.true_and]
  simp only [hpok]
  simpa using hsafe'

theorem play_pawn_promote {s : KPState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastPawn s.wk d s.bk s.ps = true)
    (hp : d.rank.val = 7) :
    isLegalMove s.toPosition (Move.promote s.ps d .queen) = true ∧
      s.toPosition.play (Move.promote s.ps d .queen) =
        (s.promoKQ d).toPosition := by
  obtain ⟨h1, h2, h3, hna, _, hr6, _⟩ := (okB_iff s).mp hok
  obtain ⟨_, hdwk, hdbk, _⟩ := (fastPawn_iff _ _ _ _).mp hm
  have hdps : d ≠ s.ps := by
    intro heq
    have : s.ps.rank.val = 7 := by rw [← heq, hp]
    omega
  have hsrcP : s.toPosition.board (Move.promote s.ps d .queen).src =
      some { color := s.toPosition.toMove, kind := .pawn } := by
    change Board.kingsPawnBoard s.wk s.bk s.ps .white s.ps =
      some { color := s.toMove, kind := .pawn }
    rw [ht]
    exact Board.kingsPawnBoard_pawn _ _ _ _ h2 h3
  have hdstNone : s.toPosition.board (Move.promote s.ps d .queen).dst = none :=
    Board.kingsPawnBoard_other _ _ _ _ _ hdwk hdbk hdps
  have hplay := play_of_some s.toPosition (Move.promote s.ps d .queen) hsrcP
  have hba := boardAfter_pawn s.toPosition (Move.promote s.ps d .queen) (c := .white) rfl
  have hboard' : s.toPosition.boardAfter (Move.promote s.ps d .queen)
      { color := .white, kind := .pawn } =
      Board.kingsQueenBoard s.wk s.bk d .white := by
    rw [hba]
    change (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.ps d
      { color := .white, kind := .queen } = _
    exact Board.relocate_kingsPawnBoard_promote _ _ _ _ h1 h2 h3 hdwk hdbk hdps
  have htm : s.toPosition.toMove = Color.white := by simp [toPosition, ht]
  have hplay' : s.toPosition.play (Move.promote s.ps d .queen) =
      (s.promoKQ d).toPosition := by
    rw [hplay, htm, hboard']
    refine Position.ext rfl (by simp [promoKQ, KQState.toPosition])
      (by
        have hc : s.toPosition.castling = ∅ := rfl
        simp only [hc]
        exact castlingAfter_empty _)
      (enPassantAfter_whitePawn_on_queenBoard
        (Move.promote s.ps d .queen) s.wk s.bk d)
  refine ⟨?_, hplay'⟩
  have hrankB : (d.rank.val == 7) = true := by simp [hp]
  have hmv : s.move (.pawn d) = Move.promote s.ps d .queen := by simp [move, hrankB]
  have hpok : s.toPosition.pawnMoveOk (Move.promote s.ps d .queen) = true := by
    simpa [hmv] using pawnMoveOk_of_fastPawn hok ht hm
  have hsafe' : (s.toPosition.play (Move.promote s.ps d .queen)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    rw [hplay']
    change (Board.kingsQueenBoard s.wk s.bk d .white).kingIsAttacked s.toMove = false
    rw [ht, KQState.kingIsAttacked_white_eq s.wk s.bk d h1 hdwk.symm hdbk.symm]
    simpa [KQState.kingAttackedWhite] using hna
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.promote s.ps d .queen) hdstNone]
  simp only [Bool.true_and]
  simp only [hpok]
  simpa using hsafe'

theorem fastLegal_sound {s : KPState} {m : KPMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) (hnp : isPromotion m = false) :
    isLegalMove s.toPosition (s.move m) = true ∧
      s.toPosition.play (s.move m) = (s.apply m).toPosition := by
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.wk d) ▸
        play_whiteKing hok ht hm
    | black =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hnps, hmv⟩ := Bool.and_eq_true_iff.mp hm
      have hn : d ≠ s.ps := bne_iff_ne.mp hnps
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.bk d) ▸
        play_blackKing hok ht hn hmv
  | pawn d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      have hrank : d.rank.val ≠ 7 := by
        simp only [isPromotion] at hnp
        intro heq
        simp [heq] at hnp
      have hrankB : (d.rank.val == 7) = false := by
        cases h : (d.rank.val == 7)
        · rfl
        · exact (hrank (beq_iff_eq.mp h)).elim
      exact (by simp [move, hrankB] : s.move (.pawn d) = Move.std s.ps d) ▸
        play_pawn hok ht hm hrank
    | black =>
      simp [fastLegal, ht] at hm

theorem legalMove_of_fastLegal {s : KPState} {m : KPMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) (hnp : isPromotion m = false) :
    LegalMove s.toPosition (s.move m) :=
  (fastLegal_sound hok hm hnp).1

theorem play_move_eq {s : KPState} {m : KPMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) (hnp : isPromotion m = false) :
    s.toPosition.play (s.move m) = (s.apply m).toPosition :=
  (fastLegal_sound hok hm hnp).2

theorem promo_sound {s : KPState} {d : Square} (hok : s.okB = true)
    (hm : s.fastLegal (.pawn d) = true) (hp : d.rank.val = 7) :
    LegalMove s.toPosition (Move.promote s.ps d .queen) ∧
      s.toPosition.play (Move.promote s.ps d .queen) =
        (s.promoKQ d).toPosition := by
  have ht : s.toMove = .white := by
    have hm' := hm
    simp only [fastLegal] at hm'
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp hm').1
  have hfp : fastPawn s.wk d s.bk s.ps = true := by
    simp only [fastLegal, ht, beq_self_eq_true, Bool.true_and] at hm
    exact hm
  exact play_pawn_promote hok ht hfp hp

theorem promoOk_not_dead {s : KPState} {d : Square} (h : s.promoOk d = true) :
    (s.promoKQ d).okB = true ∧ (s.promoKQ d).deadB = false := by
  simp only [promoOk, Bool.and_eq_true, Bool.or_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases hm : (s.promoKQ d).mateB with
  | true =>
    simp [KQState.deadB, hm]
  | false =>
    have : (!(s.promoKQ d).deadB) = true := by
      simpa [hm] using h.2
    simpa using this

theorem mem_pawnDests (ps d : Square)
    (hfile : d.file = ps.file)
    (hstep : Square.deltaRank ps d = 1 ∨ (ps.rank.val = 1 ∧ d.rank.val = 3)) :
    d ∈ pawnDests ps := by
  revert ps d
  native_decide

theorem apply_okB_of_fastLegal {s : KPState} {m : KPMove}
    (hok : s.okB = true) (hm : s.fastLegal m = true)
    (hnp : isPromotion m = false) : (s.apply m).okB = true := by
  obtain ⟨h1, h2, h3, hna, hlo, hhi, _⟩ := (okB_iff s).mp hok
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hka, hdbk, hdps, hsafeK⟩ := (fastKingW_iff _ _ _ _).mp hm
      have hna' : ¬ KingAttacks d s.bk := mt kingAttacks_symmetric.mp hsafeK
      have happ : s.apply (.king d) = ⟨.black, d, s.bk, s.ps⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.black, d, s.bk, s.ps⟩).mpr
        ⟨hdbk, hdps, h3, hna', hlo, hhi,
          by simpa [inCheckB, kingAttackedWhite] using hna'⟩
    | black =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hnps, hmv⟩ := Bool.and_eq_true_iff.mp hm
      obtain ⟨_hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
      have hdps : d ≠ s.ps := bne_iff_ne.mp hnps
      have hsafeK : ¬ KingAttacks s.wk d := by
        rcases hrest with ⟨_, h⟩ | ⟨_, h, _⟩ <;> exact h
      have happ : s.apply (.king d) = ⟨.white, s.wk, d, s.ps⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.white, s.wk, d, s.ps⟩).mpr
        ⟨hdwk.symm, h2, hdps, hsafeK, hlo, hhi, by
          change kingAttackedBlack s.wk d s.ps = false
          rcases hrest with ⟨heq, _⟩ | ⟨_, _, hp⟩
          · exact (hdps heq).elim
          · simp [kingAttackedBlack, decide_eq_false hsafeK, decide_eq_false hp]⟩
  | pawn d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨_, hdwk, hdbk, hstep⟩ := (fastPawn_iff _ _ _ _).mp hm
      have hne7 : d.rank.val ≠ 7 := by
        simp only [isPromotion] at hnp
        intro heq
        simp [heq] at hnp
      have hrank : 1 ≤ d.rank.val ∧ d.rank.val ≤ 6 := by
        rcases hstep with h1s | ⟨_, hr3, _, _⟩
        · have : d.rank.val = s.ps.rank.val + 1 := by
            simp [Square.deltaRank] at h1s
            omega
          omega
        · simp [hr3]
      have happ : s.apply (.pawn d) = ⟨.black, s.wk, s.bk, d⟩ := by simp [apply]
      rw [happ]
      exact (okB_iff ⟨.black, s.wk, s.bk, d⟩).mpr
        ⟨h1, hdwk.symm, hdbk.symm, hna, hrank.1, hrank.2,
          by simpa [inCheckB, kingAttackedWhite] using hna⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem oneOk_fastLegal {s : KPState} {m : KPMove} (h : s.oneOk m = true) :
    s.fastLegal m = true := by
  simp only [oneOk, Bool.and_eq_true] at h
  exact h.1

theorem oneOk_nonpromo {s : KPState} {m : KPMove} (h : s.oneOk m = true)
    (hnp : isPromotion m = false) :
    s.fastLegal m = true ∧ (s.apply m).okB = true ∧
      ((s.apply m).mateB = true ∨ (s.apply m).deadB = false) := by
  cases m with
  | king d =>
    simp only [oneOk, Bool.and_eq_true] at h
    refine ⟨h.1, h.2.1, ?_⟩
    have hdisj := Bool.or_eq_true_iff.mp h.2.2
    cases hdisj with
    | inl hm => exact Or.inl hm
    | inr hnd => exact Or.inr (by simpa using hnd)
  | pawn d =>
    have hpB : (d.rank.val == 7) = false := by
      simp only [isPromotion] at hnp
      exact hnp
    simp only [oneOk, hpB, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    refine ⟨h.1, h.2.1, ?_⟩
    have hdisj := Bool.or_eq_true_iff.mp h.2.2
    cases hdisj with
    | inl hm => exact Or.inl hm
    | inr hnd => exact Or.inr (by simpa using hnd)

theorem oneOk_promo {s : KPState} {d : Square} (h : s.oneOk (.pawn d) = true)
    (hp : d.rank.val = 7) :
    s.fastLegal (.pawn d) = true ∧ s.promoOk d = true := by
  have hpB : (d.rank.val == 7) = true := by simp [hp]
  simp only [oneOk, hpB, ↓reduceIte, Bool.and_eq_true] at h
  exact h

def Progress (s0 s1 : KPState) : Prop :=
  s1.okB = true ∧ Reachable s0.toPosition s1.toPosition ∧
    (s1.mateB = true ∨ (s1.mu < s0.mu ∧ s1.deadB = false))

def Promo (s0 s : KPState) (d : Square) : Prop :=
  s.okB = true ∧ Reachable s0.toPosition s.toPosition ∧
    s.fastLegal (.pawn d) = true ∧ d.rank.val = 7 ∧ s.promoOk d = true

theorem reachable_apply {s0 s : KPState} {m : KPMove}
    (hr : Reachable s0.toPosition s.toPosition) (hok : s.okB = true)
    (hm : s.fastLegal m = true) (hnp : isPromotion m = false) :
    Reachable s0.toPosition (s.apply m).toPosition := by
  have := Reachable.step (s.move m) hr (legalMove_of_fastLegal hok hm hnp)
  rwa [play_move_eq hok hm hnp] at this

theorem reachable_promo {s0 s : KPState} {d : Square}
    (hr : Reachable s0.toPosition s.toPosition) (hok : s.okB = true)
    (hm : s.fastLegal (.pawn d) = true) (hp : d.rank.val = 7) :
    Reachable s0.toPosition (s.promoKQ d).toPosition := by
  have ⟨hleg, hplay⟩ := promo_sound hok hm hp
  have := Reachable.step (Move.promote s.ps d .queen) hr hleg
  rwa [hplay] at this

theorem goal_sound {s0 s : KPState} (hok : s.okB = true)
    (hr : Reachable s0.toPosition s.toPosition) (hg : goal s0 s = true) :
    ∃ s1, Progress s0 s1 := by
  unfold goal at hg
  cases hm : s.mateB with
  | true => exact ⟨s, hok, hr, Or.inl hm⟩
  | false =>
    have hrest : decide (s.mu < s0.mu) && !s.deadB = true := by
      simpa [hm] using hg
    have hltB := (Bool.and_eq_true_iff.mp hrest).1
    have hndB := (Bool.and_eq_true_iff.mp hrest).2
    have hlt : s.mu < s0.mu := of_decide_eq_true hltB
    have hnd : s.deadB = false := by simpa using hndB
    exact ⟨s, hok, hr, Or.inr ⟨hlt, hnd⟩⟩

theorem goalMove_sound {s0 s : KPState} {m : KPMove} (hok : s.okB = true)
    (hr : Reachable s0.toPosition s.toPosition) (hone : s.oneOk m = true)
    (hg : goalMove s0 s m = true) :
    (∃ s1, Progress s0 s1) ∨ ∃ d, Promo s0 s d := by
  cases m with
  | king d =>
    simp only [goalMove] at hg
    have hnp : isPromotion (.king d) = false := rfl
    have ⟨hfl, hok1, _⟩ := oneOk_nonpromo hone hnp
    exact Or.inl (goal_sound hok1 (reachable_apply hr hok hfl hnp) hg)
  | pawn d =>
    cases hp : (d.rank.val == 7)
    · simp only [goalMove, hp, Bool.false_eq_true, ↓reduceIte] at hg
      have hnp : isPromotion (.pawn d) = false := by simp [isPromotion, hp]
      have ⟨hfl, hok1, _⟩ := oneOk_nonpromo hone hnp
      exact Or.inl (goal_sound hok1 (reachable_apply hr hok hfl hnp) hg)
    · simp only [goalMove, hp, ↓reduceIte] at hg
      have hpr : d.rank.val = 7 := beq_iff_eq.mp hp
      have ⟨hfl, hpo⟩ := oneOk_promo hone hpr
      exact Or.inr ⟨d, hok, hr, hfl, hpr, hpo⟩

theorem chain_sound {s0 : KPState} :
    ∀ (n : Nat) (s : KPState), s.okB = true → Reachable s0.toPosition s.toPosition →
      chain s0 s n = true →
        (∃ s1, Progress s0 s1) ∨ ∃ s' d, Promo s0 s' d := by
  intro n
  induction n with
  | zero =>
    intro s _ _ h
    simp [chain] at h
  | succ n ih =>
    intro s hok hr h
    simp only [chain, Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · rename_i m _
        obtain ⟨hone, hg⟩ := Bool.and_eq_true_iff.mp h
        rcases goalMove_sound hok hr hone hg with hP | ⟨d, hPr⟩
        · exact Or.inl hP
        · exact Or.inr ⟨s, d, hPr⟩
      · cases h
    · split at h
      · cases h
      · rename_i m _
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨hone, hrest⟩ := h
        rcases hrest with hg | hc
        · rcases goalMove_sound hok hr hone hg with hP | ⟨d, hPr⟩
          · exact Or.inl hP
          · exact Or.inr ⟨s, d, hPr⟩
        · cases m with
          | pawn d =>
            cases hp : (d.rank.val == 7)
            · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hc
              have hnp : isPromotion (.pawn d) = false := by simp [isPromotion, hp]
              have ⟨hfl, hok1, _⟩ := oneOk_nonpromo hone hnp
              have hr1 := reachable_apply hr hok hfl hnp
              exact ih _ hok1 hr1 hc
            · simp [hp] at hc
          | king d =>
            simp only at hc
            have hnp : isPromotion (.king d) = false := rfl
            have ⟨hfl, hok1, _⟩ := oneOk_nonpromo hone hnp
            have hr1 := reachable_apply hr hok hfl hnp
            exact ih _ hok1 hr1 hc

theorem chain_sound' {s0 : KPState} {n : Nat} {s : KPState}
    (hok : s.okB = true) (hr : Reachable s0.toPosition s.toPosition)
    (h : chain s0 s n = true) :
    (∃ s1, Progress s0 s1) ∨ ∃ s' d, Promo s0 s' d :=
  chain_sound n s hok hr h

theorem checkState_progress {s : KPState} (hok : s.okB = true)
    (h : s.checkState = true) :
    s.mateB = true ∨ s.deadB = true ∨ (∃ s1, Progress s s1) ∨
      ∃ s' d, Promo s s' d := by
  unfold checkState at h
  have hn : (!s.okB) = false := by simp [hok]
  rw [hn, Bool.false_or] at h
  cases hm : s.mateB with
  | true => exact Or.inl rfl
  | false =>
    rw [hm, Bool.false_or] at h
    cases hd : s.deadB with
    | true => exact Or.inr (Or.inl rfl)
    | false =>
      rw [hd, Bool.false_or] at h
      rcases chain_sound' hok Reachable.refl h with hP | hPr
      · exact Or.inr (Or.inr (Or.inl hP))
      · exact Or.inr (Or.inr (Or.inr hPr))

theorem mateB_toMove {s : KPState} (hm : s.mateB = true) : s.toMove = .black := by
  simp only [mateB, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1

theorem mateB_checked {s : KPState} (hm : s.mateB = true) :
    kingAttackedBlack s.wk s.bk s.ps = true := by
  simp only [mateB, Bool.and_eq_true] at hm
  exact hm.1.2

theorem mateB_flight {s : KPState} (hm : s.mateB = true) {d : Square}
    (hd : d ∈ kingNeighbors s.bk) :
    (d == s.wk || decide (KingAttacks s.wk d) ||
      (d != s.ps && decide (PawnAttacks .white s.ps d))) = true := by
  simp only [mateB, Bool.and_eq_true, List.all_eq_true] at hm
  exact hm.2 d hd

/-- In a `mateB` state, Black has no legal move. -/
theorem mateB_black_no_legalMove {s : KPState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : s.mateB = true) (m : Move) :
    ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hdestOk, hdstOr, hsafe, piece, hsrc, hpc, hkind, hside, hpawn⟩ :=
    kingPawn_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .black := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
      some ⟨.black, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.bk := Board.kingsPawnBoard_eq_black_king hsrc'
    have hka : KingAttacks s.bk m.dst := by
      have hatt' :
          (Board.kingsPawnBoard s.wk s.bk s.ps .white).attacks m.src m.dst = true :=
        (hside rfl).2.2
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .black = none := ht ▸ (hside rfl).1
    have hpromo : m.promotion = none := (hside rfl).2.1
    have hplay := play_of_some s.toPosition m hsrc
    have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hside' hpromo
    have hboard : (s.toPosition.play m).board =
        (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.bk m.dst
          { color := .black, kind := .king } := by
      rw [hplay, hba, hsq]
      rfl
    have hmem := mateB_flight hm (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hps
    · obtain ⟨hdwk, hdbk, hdps⟩ := ne_of_kingsPawnBoard_eq_none (by
        simpa [toPosition] using hempty)
      rw [hboard, Board.relocate_kingsPawnBoard_black s.wk s.bk s.ps m.dst .white
        h1 h2 h3 hdwk hdbk hdps, kingIsAttacked_black_eq s.wk m.dst s.ps
        hdwk.symm h2 hdps] at hsafe'
      have hwkB : (m.dst == s.wk) = false := by simp [hdwk]
      have hsafe'' : ¬ KingAttacks s.wk m.dst ∧
          ¬ PawnAttacks .white s.ps m.dst := by
        simpa [kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      have hkaF : decide (KingAttacks s.wk m.dst) = false := decide_eq_false hsafe''.1
      have hpF : decide (PawnAttacks .white s.ps m.dst) = false :=
        decide_eq_false hsafe''.2
      have hne : (m.dst != s.ps) = true := bne_iff_ne.mpr hdps
      simp [hwkB, hkaF, hne, hpF] at hmem
    · rw [hps] at hmem hboard
      have hwkB : (s.ps == s.wk) = false := by simp [h2.symm]
      by_cases hprot : KingAttacks s.wk s.ps
      · rw [hboard, Board.relocate_capture_pawn_black s.wk s.bk s.ps h1 h2 h3] at hsafe'
        rw [Board.kingsBoard_kingIsAttacked_black s.wk s.ps h2] at hsafe'
        exact of_decide_eq_false hsafe' hprot
      · have hkaF : decide (KingAttacks s.wk s.ps) = false := decide_eq_false hprot
        simp [hwkB, hkaF] at hmem
  · simp only at hk
    subst hk
    have hsrc'' := hsrc'
    unfold Board.kingsPawnBoard at hsrc''
    split_ifs at hsrc'' <;> cases hsrc''

theorem inCheckmate_of_mateB {s : KPState} (hok : s.okB = true) (hm : s.mateB = true) :
    InCheckmate s.toPosition := by
  rw [InCheckmate_iff_forall_not_LegalMove]
  have ht : s.toMove = .black := mateB_toMove hm
  refine ⟨?_, ?_⟩
  · change s.toPosition.board.kingIsAttacked s.toPosition.toMove = true
    rw [kingIsAttacked_eq s hok]
    change s.inCheckB s.toMove = true
    rw [ht]
    simp [inCheckB, mateB_checked hm]
  · exact mateB_black_no_legalMove hok ht hm

theorem hasNoncaptureLegal_of_fastLegal {s : KPState} {m : KPMove}
    (hm : s.fastLegal m = true) : s.hasNoncaptureLegal = true := by
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      have hka : KingAttacks s.wk d := ((fastKingW_iff _ _ _ _).mp hm).1
      simp only [hasNoncaptureLegal, ht, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl ⟨d, mem_kingNeighbors hka, hm⟩
    | black =>
      simp only [fastLegal, ht] at hm
      have hne := (Bool.and_eq_true_iff.mp hm).1
      have hmv := (Bool.and_eq_true_iff.mp hm).2
      have hka : KingAttacks s.bk d := ((fastKingB_iff _ _ _ _).mp hmv).1
      simp only [hasNoncaptureLegal, ht, List.any_eq_true]
      exact ⟨d, mem_kingNeighbors hka, by simp [hne, hmv]⟩
  | pawn d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hfile, _, _, hstep⟩ := (fastPawn_iff _ _ _ _).mp hm
      have hmem := mem_pawnDests s.ps d hfile (hstep.imp_right fun h => ⟨h.1, h.2.1⟩)
      simp only [hasNoncaptureLegal, ht, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨d, hmem, hm⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem toPosition_isKingAndPawn {s : KPState} (hok : s.okB = true) :
    IsKingAndPawn s.toPosition := by
  obtain ⟨h1, h2, h3, hna, _, _, _⟩ := (okB_iff s).mp hok
  exact ⟨s.wk, s.bk, s.ps, .white, h1, h2, h3, hna, rfl, rfl, rfl⟩

end KPState

namespace KPState

open Position

theorem destOk_capture_pawn {s : KPState} (hok : s.okB = true)
    (ht : s.toMove = .black) :
    s.toPosition.destOk (Move.std s.bk s.ps) = true := by
  obtain ⟨_, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  unfold destOk
  change (match Board.kingsPawnBoard s.wk s.bk s.ps .white s.ps with
    | none => true
    | some q => (q.color != s.toPosition.toMove) && (q.kind != .king)) = true
  rw [Board.kingsPawnBoard_pawn s.wk s.bk s.ps .white h2 h3]
  simp [toPosition, ht]

theorem play_blackCapture {s : KPState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hka : KingAttacks s.bk s.ps)
    (hprot : ¬ KingAttacks s.wk s.ps) :
    isLegalMove s.toPosition (Move.std s.bk s.ps) = true := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  have hsrcP : s.toPosition.board (Move.std s.bk s.ps).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsPawnBoard s.wk s.bk s.ps .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsPawnBoard_black _ _ _ _ h1
  have hside : (Move.std s.bk s.ps).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk s.ps) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk s.ps)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk s.ps)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsBoard s.wk s.ps := by
    rw [hba]
    change (Board.kingsPawnBoard s.wk s.bk s.ps .white).relocate s.bk s.ps
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_capture_pawn_black _ _ _ h1 h2 h3
  have hgeo : s.toPosition.board.attacks (Move.std s.bk s.ps).src
      (Move.std s.bk s.ps).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.bk s.ps)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    rw [hplay, hboard']
    change (Board.kingsBoard s.wk s.ps).kingIsAttacked s.toMove = false
    rw [ht, Board.kingsBoard_kingIsAttacked_black s.wk s.ps h2]
    exact decide_eq_false hprot
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  have hdest : s.toPosition.destOk (Move.std s.bk s.ps) = true :=
    destOk_capture_pawn hok ht
  rw [hdest]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.bk s.ps).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem deadB_mate_eq_false {s : KPState} (hd : s.deadB = true) :
    s.mateB = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.1

theorem deadB_hasNoncapture_eq_false {s : KPState} (hd : s.deadB = true) :
    s.hasNoncaptureLegal = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.2

theorem white_not_inCheck {s : KPState} (hok : s.okB = true) :
    s.inCheckB .white = false := by
  obtain ⟨_, _, _, hna, _, _, _⟩ := (okB_iff s).mp hok
  simp [inCheckB, kingAttackedWhite, hna]

theorem inCheckmate_implies_mateB {s : KPState} (hok : s.okB = true)
    (hm : InCheckmate s.toPosition) : s.mateB = true := by
  have hchk : s.inCheckB s.toMove = true := by
    have hchk0 : s.toPosition.board.kingIsAttacked s.toPosition.toMove = true := hm.1
    rw [kingIsAttacked_eq s hok] at hchk0
    simpa [toPosition] using hchk0
  cases ht : s.toMove with
  | white =>
    rw [ht] at hchk
    exact (Bool.false_ne_true ((white_not_inCheck hok).symm.trans hchk)).elim
  | black =>
    rw [ht] at hchk
    have hchk' : kingAttackedBlack s.wk s.bk s.ps = true := by
      simpa [inCheckB] using hchk
    have hall : (kingNeighbors s.bk).all (fun d =>
        d == s.wk || decide (KingAttacks s.wk d) ||
          (d != s.ps && decide (PawnAttacks .white s.ps d))) = true := by
      refine List.all_eq_true.mpr ?_
      intro d hd
      by_contra hf
      have h1 : (d == s.wk) = false := by
        cases h : (d == s.wk)
        · rfl
        · simp [h] at hf
      have h2 : decide (KingAttacks s.wk d) = false := by
        cases h : decide (KingAttacks s.wk d)
        · rfl
        · simp [h1, h] at hf
      have h3 : (d != s.ps && decide (PawnAttacks .white s.ps d)) = false := by
        cases h : (d != s.ps && decide (PawnAttacks .white s.ps d))
        · rfl
        · simp [h1, h2, h] at hf
      have hkaB : KingAttacks s.bk d := kingAttacks_of_mem_kingNeighbors hd
      have hkaW : ¬ KingAttacks s.wk d := of_decide_eq_false h2
      have hnoleg : ∀ mv : Move, ¬ LegalMove s.toPosition mv :=
        (InCheckmate_iff_forall_not_LegalMove s.toPosition).mp hm |>.2
      by_cases hps : d = s.ps
      · subst hps
        have hleg : LegalMove s.toPosition (Move.std s.bk s.ps) :=
          play_blackCapture hok ht hkaB hkaW
        exact hnoleg _ hleg
      · have hne : (d != s.ps) = true := bne_iff_ne.mpr hps
        have hnP : ¬ PawnAttacks .white s.ps d := by
          have : decide (PawnAttacks .white s.ps d) = false := by simpa [hne] using h3
          exact of_decide_eq_false this
        have hdwk : d ≠ s.wk := bne_iff_ne.mp (by simpa using h1)
        have hmv : fastKingB s.wk d s.bk s.ps = true := by
          simp [fastKingB, hkaB, hdwk, hps, hkaW, hnP]
        have hfl : s.fastLegal (.king d) = true := by
          simp [fastLegal, ht, bne_iff_ne.mpr hps, hmv]
        exact hnoleg _ (legalMove_of_fastLegal hok hfl (by simp [isPromotion]))
    simp [mateB, ht, hchk', hall]

theorem not_inCheckmate_of_deadB {s : KPState} (hok : s.okB = true)
    (hd : s.deadB = true) : ¬ InCheckmate s.toPosition := by
  intro hm
  have := inCheckmate_implies_mateB hok hm
  exact Bool.false_ne_true ((deadB_mate_eq_false hd).symm.trans this)

theorem fastLegal_of_legalMove_noncapture {s : KPState} {m : Move}
    (hok : s.okB = true) (hm : LegalMove s.toPosition m)
    (he : s.toPosition.board m.dst = none) :
    ∃ km, s.fastLegal km = true := by
  obtain ⟨h1, h2, h3, _, hlo, hhi, _⟩ := (okB_iff s).mp hok
  obtain ⟨_, _, hsafe, piece, hsrc, hpc, hkind, hside, hpawn⟩ :=
    kingPawn_legalMove_core rfl rfl hm
  obtain ⟨hdwk, hdbk, hdps⟩ := ne_of_kingsPawnBoard_eq_none (by
    simpa [toPosition] using he)
  rcases piece with ⟨pc, pk⟩
  subst hpc
  rcases hkind with hk | hk
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcW : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some { color := .white, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.wk := Board.kingsPawnBoard_eq_white_king hsrcW
      have hka : KingAttacks s.wk m.dst := by
        have hattW :
            (Board.kingsPawnBoard s.wk s.bk s.ps .white).attacks m.src m.dst = true :=
          (hside rfl).2.2
        rw [Board.attacks_king hsrcW, hsq] at hattW
        exact of_decide_eq_true hattW
      have hplay := play_of_some s.toPosition m hsrc
      have hsideW : m.castlingSide? Color.white = none := by
        simpa [toPosition, ht] using (hside rfl).1
      have hpromo : m.promotion = none := (hside rfl).2.1
      have hba := boardAfter_king_no_castle s.toPosition m (c := .white) hsideW hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsPawnBoard m.dst s.bk s.ps .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.white := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsPawnBoard_white s.wk s.bk s.ps m.dst .white
          h1 h2 h3 hdwk hdbk hdps
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .white = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_white_eq m.dst s.bk s.ps hdbk hdps h3] at hsafe'
      have hsafeK : ¬ KingAttacks s.bk m.dst := by
        simpa [kingAttackedWhite, kingAttacks_symmetric] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, fastKingW, hka, hdbk, hdps, hsafeK]
    | black =>
      have hsrcB : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some { color := .black, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.bk := Board.kingsPawnBoard_eq_black_king hsrcB
      have hka : KingAttacks s.bk m.dst := by
        have hattB :
            (Board.kingsPawnBoard s.wk s.bk s.ps .white).attacks m.src m.dst = true :=
          (hside rfl).2.2
        rw [Board.attacks_king hsrcB, hsq] at hattB
        exact of_decide_eq_true hattB
      have hplay := play_of_some s.toPosition m hsrc
      have hsideB : m.castlingSide? Color.black = none := by
        simpa [toPosition, ht] using (hside rfl).1
      have hpromo : m.promotion = none := (hside rfl).2.1
      have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsPawnBoard s.wk m.dst s.ps .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsPawnBoard_black s.wk s.bk s.ps m.dst .white
          h1 h2 h3 hdwk hdbk hdps
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_black_eq s.wk m.dst s.ps hdwk.symm h2 hdps] at hsafe'
      have hpair : decide (KingAttacks s.wk m.dst) = false ∧
          decide (PawnAttacks .white s.ps m.dst) = false := by
        simpa [kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, bne_iff_ne.mpr hdps, fastKingB, hka, hdwk, hdps,
        of_decide_eq_false hpair.1, of_decide_eq_false hpair.2]
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcP : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some { color := .white, kind := .pawn } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.ps := Board.kingsPawnBoard_eq_pawn hsrcP
      have hpok : s.toPosition.pawnMoveOk m = true := hpawn rfl
      have hfl : fastPawn s.wk m.dst s.bk s.ps = true := by
        have haux := fastPawn_of_pawnMoveOk_aux s.wk s.bk s.ps m.dst m.promotion
        have hnone : (Board.kingsPawnBoard s.wk s.bk s.ps .white m.dst).isNone = true := by
          simpa [toPosition] using (Option.isNone_iff_eq_none.mpr he)
        have hm' : (⟨.white, s.wk, s.bk, s.ps⟩ : KPState).toPosition.pawnMoveOk
            ⟨s.ps, m.dst, m.promotion⟩ = true := by
          have hm0 : (⟨.white, s.wk, s.bk, s.ps⟩ : KPState).toPosition.pawnMoveOk m = true := by
            simpa [toPosition, ht] using hpok
          have heq : ({ src := s.ps, dst := m.dst, promotion := m.promotion } : Move) = m := by
            rcases m with ⟨src, dst, pr⟩
            have hsrcEq : src = s.ps := hsq
            subst hsrcEq
            rfl
          rwa [heq]
        have hok' : (⟨.white, s.wk, s.bk, s.ps⟩ : KPState).okB = true := by
          rcases s with ⟨tm, wk, bk, ps⟩
          subst ht
          exact hok
        have hcond :
            ((⟨.white, s.wk, s.bk, s.ps⟩ : KPState).okB &&
              (Board.kingsPawnBoard s.wk s.bk s.ps .white m.dst).isNone &&
              (⟨.white, s.wk, s.bk, s.ps⟩ : KPState).toPosition.pawnMoveOk
                ⟨s.ps, m.dst, m.promotion⟩) = true :=
          Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hok', hnone⟩, hm'⟩
        simp only [hcond, ↓reduceIte] at haux
        exact haux
      refine ⟨.pawn m.dst, ?_⟩
      simp [fastLegal, ht, hfl]
    | black =>
      have hsrc' : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some ⟨.black, .pawn⟩ := by simpa [toPosition, ht] using hsrc
      unfold Board.kingsPawnBoard at hsrc'
      split_ifs at hsrc' <;> cases hsrc'

theorem twoKings_of_deadB_legal {s : KPState} {m : Move}
    (hok : s.okB = true) (hd : s.deadB = true) (hm : LegalMove s.toPosition m) :
    IsTwoKings (s.toPosition.play m) := by
  obtain ⟨h1, h2, h3, _, _, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hdestOk, hdstOr, hsafe, piece, hsrc, hpc, hkind, hside, hpawn⟩ :=
    kingPawn_legalMove_core rfl rfl hm
  cases hdstOr with
  | inl he =>
    obtain ⟨km, hfl⟩ := fastLegal_of_legalMove_noncapture hok hm he
    exact (Bool.false_ne_true
      ((deadB_hasNoncapture_eq_false hd).symm.trans
        (hasNoncaptureLegal_of_fastLegal hfl))).elim
  | inr hps =>
    have ht : s.toMove = .black :=
      destOk_toMove_of_dst_pawn (p := s.toPosition) (m := m) (wk := s.wk)
        (bk := s.bk) (ps := s.ps) (c := Color.white) rfl h2 h3 hps hdestOk
    rcases piece with ⟨pc, pk⟩
    have hpc' : pc = .black := hpc.trans ht
    subst hpc'
    cases hkind with
    | inr hrk =>
      subst hrk
      have hsrc' : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some ⟨.black, .pawn⟩ := by simpa [toPosition, ht] using hsrc
      unfold Board.kingsPawnBoard at hsrc'
      split_ifs at hsrc' <;> cases hsrc'
    | inl hk =>
      subst hk
      have hsrcB : Board.kingsPawnBoard s.wk s.bk s.ps .white m.src =
          some { color := .black, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.bk := Board.kingsPawnBoard_eq_black_king hsrcB
      have hpl := play_of_some s.toPosition m hsrc
      have hsideB : m.castlingSide? Color.black = none := by
        simpa [toPosition, ht] using (hside rfl).1
      have hpromo : m.promotion = none := (hside rfl).2.1
      have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
      have hboard : (s.toPosition.play m).board = Board.kingsBoard s.wk s.ps := by
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this, hba, hsq, hps]
        exact Board.relocate_capture_pawn_black s.wk s.bk s.ps h1 h2 h3
      have hcast : (s.toPosition.play m).castling = ∅ := by
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this, hba]; exact castlingAfter_empty _
      have hep : (s.toPosition.play m).enPassant = none := by
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this]
        simp [enPassantAfter]
      have hna' : ¬ KingAttacks s.wk s.ps := by
        have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false :=
          by simpa [ht, toPosition] using hsafe
        rw [hboard, Board.kingsBoard_kingIsAttacked_black s.wk s.ps h2] at hsafe'
        exact of_decide_eq_false hsafe'
      exact ⟨s.wk, s.ps, h2, hna', hboard, hcast, hep⟩

theorem reachable_from_deadB {s : KPState} {q : Position}
    (hok : s.okB = true) (hd : s.deadB = true)
    (hr : Reachable s.toPosition q) :
    q = s.toPosition ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl rfl
  | step m _hr hleg ih =>
    cases ih with
    | inl hsame =>
      subst hsame
      exact Or.inr (twoKings_of_deadB_legal hok hd hleg)
    | inr htk =>
      exact Or.inr (IsTwoKings.of_play htk hleg)

theorem not_CheckmateReachable_of_deadB {s : KPState} (hok : s.okB = true)
    (hd : s.deadB = true) : ¬ CheckmateReachable s.toPosition := by
  intro ⟨q, hr, hq⟩
  rcases reachable_from_deadB hok hd hr with h | h
  · subst h
    exact not_inCheckmate_of_deadB hok hd hq
  · exact h.not_InCheckmate hq

theorem progress_exists {s : KPState} (hok : s.okB = true) :
    s.mateB = true ∨ s.deadB = true ∨ (∃ s1, Progress s s1) ∨
      ∃ s' d, Promo s s' d := by
  have hcs : s.checkState = true := by
    rcases s with ⟨tm, wk, bk, ps⟩
    have hwk := (List.all_eq_true.mp checkAll_true) wk (mem_allSquares _)
    have hbk := (List.all_eq_true.mp hwk) bk (mem_allSquares _)
    have hps := (List.all_eq_true.mp hbk) ps (mem_allSquares _)
    have hpair := Bool.and_eq_true_iff.mp hps
    cases tm
    · exact hpair.1
    · exact hpair.2
  exact checkState_progress hok hcs

theorem dead_or_checkmate_of_okB_aux :
    ∀ n (s : KPState), s.okB = true → s.mu = n →
      s.deadB = true ∨ CheckmateReachable s.toPosition := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hok hn
    rcases progress_exists hok with hm | hd | ⟨s1, hok1, hr, hp⟩ | ⟨s', d, hs'ok, hr', hfl, hp, hpo⟩
    · exact Or.inr ⟨s.toPosition, Reachable.refl, inCheckmate_of_mateB hok hm⟩
    · exact Or.inl hd
    · rcases hp with hm1 | ⟨hlt, hnd⟩
      · exact Or.inr ⟨s1.toPosition, hr, inCheckmate_of_mateB hok1 hm1⟩
      · have hnd' : s1.deadB = false := hnd
        have hlt' : s1.mu < n := hn ▸ hlt
        have ih1 := ih s1.mu hlt' s1 hok1 rfl
        cases ih1 with
        | inl hd1 => exact (Bool.false_ne_true (hnd'.symm.trans hd1)).elim
        | inr hcr =>
          obtain ⟨q, hrq, hq⟩ := hcr
          exact Or.inr ⟨q, hr.trans hrq, hq⟩
    · have ⟨hokQ, hndQ⟩ := promoOk_not_dead hpo
      have hrQ := reachable_promo hr' hs'ok hfl hp
      have hcr := KQState.checkmateReachable_of_okB_of_not_dead hokQ hndQ
      obtain ⟨q, hrq, hq⟩ := hcr
      exact Or.inr ⟨q, hrQ.trans hrq, hq⟩

theorem checkmateReachable_of_okB_of_not_dead {s : KPState}
    (hok : s.okB = true) (hnd : s.deadB = false) :
    CheckmateReachable s.toPosition := by
  have h := dead_or_checkmate_of_okB_aux s.mu s hok rfl
  cases h with
  | inl hd => exact (Bool.false_ne_true (hnd.symm.trans hd)).elim
  | inr hcr => exact hcr

theorem checkmateReachable_iff_not_dead {s : KPState} (hok : s.okB = true) :
    CheckmateReachable s.toPosition ↔ s.deadB = false := by
  constructor
  · intro h
    cases hd : s.deadB with
    | true => exact (not_CheckmateReachable_of_deadB hok hd h).elim
    | false => rfl
  · intro hnd
    exact checkmateReachable_of_okB_of_not_dead hok hnd

end KPState

end Chess

