import Chess.TwoKings

/-!
# King and knight versus king

A valid position whose board holds only the two kings and one knight is
never checkmate. The side that has the knight is not in check: the lone
king is the only enemy piece, and the kings are not adjacent (otherwise
the opponent would be in check). The lone king, if in check, is checked
by the knight; an orthogonal neighbor has the same square-color as the
knight, so the knight cannot cover it. The other king, not being
adjacent, cannot cover both the horizontal and the vertical neighbor, so
one of those squares is a legal flight. A legal move either keeps the
same three pieces or captures the knight, leaving two kings. In the
latter case `IsTwoKings` applies. Hence no sequence of legal moves
produces checkmate.
-/

namespace Chess

namespace Board

/-- White king on `wk`, black king on `bk`, and a knight of color `c` on
`ns`. -/
def kingsKnightBoard (wk bk ns : Square) (c : Color) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = ns then some { color := c, kind := .knight }
  else none

theorem kingsKnightBoard_white (wk bk ns : Square) (c : Color) :
    kingsKnightBoard wk bk ns c wk = some { color := .white, kind := .king } := by
  simp [kingsKnightBoard]

theorem kingsKnightBoard_black (wk bk ns : Square) (c : Color) (h : wk ≠ bk) :
    kingsKnightBoard wk bk ns c bk = some { color := .black, kind := .king } := by
  simp [kingsKnightBoard, h.symm]

theorem kingsKnightBoard_knight (wk bk ns : Square) (c : Color)
    (hw : wk ≠ ns) (hb : bk ≠ ns) :
    kingsKnightBoard wk bk ns c ns = some { color := c, kind := .knight } := by
  simp [kingsKnightBoard, hw.symm, hb.symm]

theorem kingsKnightBoard_other (wk bk ns s : Square) (c : Color)
    (hw : s ≠ wk) (hb : s ≠ bk) (hns : s ≠ ns) :
    kingsKnightBoard wk bk ns c s = none := by
  simp [kingsKnightBoard, hw, hb, hns]

theorem kingsKnightBoard_eq_white_king {wk bk ns s : Square} {c : Color}
    (h : kingsKnightBoard wk bk ns c s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsKnightBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightBoard_eq_black_king {wk bk ns s : Square} {c : Color}
    (h : kingsKnightBoard wk bk ns c s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsKnightBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightBoard_eq_knight {wk bk ns s : Square} {c : Color}
    (h : kingsKnightBoard wk bk ns c s = some { color := c, kind := .knight }) :
    s = ns := by
  unfold kingsKnightBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightBoard_isSome (wk bk ns s : Square) (c : Color) :
    ((kingsKnightBoard wk bk ns c) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = ns := by
  unfold kingsKnightBoard
  split_ifs <;> simp_all

theorem attacks_knight {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .knight }) :
    b.attacks s t = decide (KnightAttacks s t) := by
  unfold attacks
  rw [h]
  simp [PieceKind.isSlider]

theorem kingsKnightBoard_occupiedBy_white (wk bk ns : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ns : wk ≠ ns) (_hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).occupiedBy .white =
      match c with
      | .white => {wk, ns}
      | .black => {wk} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsKnightBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsKnightBoard
    split_ifs <;> simp_all

theorem kingsKnightBoard_occupiedBy_black (wk bk ns : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ns : wk ≠ ns) (_hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).occupiedBy .black =
      match c with
      | .white => {bk}
      | .black => {bk, ns} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsKnightBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsKnightBoard
    split_ifs <;> simp_all

theorem kingsKnightBoard_kingSquares_white (wk bk ns : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ns : wk ≠ ns) (_hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsKnightBoard
  split_ifs <;> simp_all

theorem kingsKnightBoard_kingSquares_black (wk bk ns : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ns : wk ≠ ns) (_hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsKnightBoard
  split_ifs <;> simp_all

theorem kingsKnightBoard_occupied (wk bk ns : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_ns : wk ≠ ns) (_hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).occupied = {wk, bk, ns} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsKnightBoard
  split_ifs <;> simp_all

theorem kingsKnightBoard_black_piece {wk bk ns s : Square} {c : Color}
    (h : (kingsKnightBoard wk bk ns c s).map (·.color) = some .black) :
    s = bk ∨ (c = .black ∧ s = ns) := by
  unfold kingsKnightBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightBoard_white_piece {wk bk ns s : Square} {c : Color}
    (h : (kingsKnightBoard wk bk ns c s).map (·.color) = some .white) :
    s = wk ∨ (c = .white ∧ s = ns) := by
  unfold kingsKnightBoard at h
  split_ifs at h <;> simp_all

theorem kingsKnightBoard_kingIsAttacked_white (wk bk ns : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨ (c = .black ∧ KnightAttacks ns wk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsKnightBoard_kingSquares_white wk bk ns c hwk_bk hwk_ns hbk_ns,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsKnightBoard_black_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsKnightBoard_black wk bk ns c hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [attacks_knight (kingsKnightBoard_knight wk bk ns Color.black hwk_ns hbk_ns)]
        at hatt
      exact Or.inr ⟨hc, of_decide_eq_true hatt⟩
  · intro h
    rcases h with hk | ⟨hc, hN⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightBoard_black wk bk ns c hwk_bk]
      · rw [attacks_king (kingsKnightBoard_black wk bk ns c hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨ns, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsKnightBoard_knight wk bk ns Color.black hwk_ns hbk_ns]
      · subst hc
        rw [attacks_knight (kingsKnightBoard_knight wk bk ns Color.black hwk_ns hbk_ns)]
        exact decide_eq_true hN

theorem kingsKnightBoard_kingIsAttacked_black (wk bk ns : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns) :
    (kingsKnightBoard wk bk ns c).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨ (c = .white ∧ KnightAttacks ns bk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsKnightBoard_kingSquares_black wk bk ns c hwk_bk hwk_ns hbk_ns,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsKnightBoard_white_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsKnightBoard_white wk bk ns c)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [attacks_knight (kingsKnightBoard_knight wk bk ns Color.white hwk_ns hbk_ns)]
        at hatt
      exact Or.inr ⟨hc, of_decide_eq_true hatt⟩
  · intro h
    rcases h with hk | ⟨hc, hN⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsKnightBoard_white]
      · rw [attacks_king (kingsKnightBoard_white wk bk ns c)]
        exact decide_eq_true hk
    · refine ⟨ns, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsKnightBoard_knight wk bk ns Color.white hwk_ns hbk_ns]
      · subst hc
        rw [attacks_knight (kingsKnightBoard_knight wk bk ns Color.white hwk_ns hbk_ns)]
        exact decide_eq_true hN

theorem relocate_kingsKnightBoard_white (wk bk ns dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwn : wk ≠ ns) (_hbn : bk ≠ ns)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdn : dst ≠ ns) :
    (kingsKnightBoard wk bk ns c).relocate wk dst { color := .white, kind := .king } =
      kingsKnightBoard dst bk ns c := by
  funext s
  unfold relocate kingsKnightBoard
  split_ifs <;> simp_all

theorem relocate_kingsKnightBoard_black (wk bk ns dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwn : wk ≠ ns) (_hbn : bk ≠ ns)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdn : dst ≠ ns) :
    (kingsKnightBoard wk bk ns c).relocate bk dst { color := .black, kind := .king } =
      kingsKnightBoard wk dst ns c := by
  funext s
  unfold relocate kingsKnightBoard
  split_ifs <;> simp_all

theorem relocate_kingsKnightBoard_knight (wk bk ns dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwn : wk ≠ ns) (_hbn : bk ≠ ns)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdn : dst ≠ ns) :
    (kingsKnightBoard wk bk ns c).relocate ns dst { color := c, kind := .knight } =
      kingsKnightBoard wk bk dst c := by
  funext s
  unfold relocate kingsKnightBoard
  split_ifs <;> simp_all

theorem relocate_capture_knight_white (wk bk ns : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ ns) (_hbn : bk ≠ ns) :
    (kingsKnightBoard wk bk ns .black).relocate wk ns
      { color := .white, kind := .king } =
      kingsBoard ns bk := by
  funext s
  unfold relocate kingsKnightBoard kingsBoard
  split_ifs <;> simp_all

theorem relocate_capture_knight_black (wk bk ns : Square)
    (_hne : wk ≠ bk) (_hwn : wk ≠ ns) (_hbn : bk ≠ ns) :
    (kingsKnightBoard wk bk ns .white).relocate bk ns
      { color := .black, kind := .king } =
      kingsBoard wk ns := by
  funext s
  unfold relocate kingsKnightBoard kingsBoard
  split_ifs <;> simp_all

end Board

namespace Position

/-- Square of the king that does not own the knight. -/
def knLone (wk bk : Square) (c : Color) : Square :=
  match c with
  | .white => bk
  | .black => wk

/-- Square of the king that owns the knight. -/
def knSupport (wk bk : Square) (c : Color) : Square :=
  match c with
  | .white => wk
  | .black => bk

/-- Orthogonal flight square for the lone king. -/
def knEscape (wk bk : Square) (c : Color) : Square :=
  kingOrthoEscape (knLone wk bk c) (knSupport wk bk c)

/-- `p` contains only two kings and one knight, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingAndKnight (p : Position) : Prop :=
  ∃ wk bk ns : Square, ∃ c : Color,
    wk ≠ bk ∧
      wk ≠ ns ∧
      bk ≠ ns ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsKnightBoard wk bk ns c ∧
      p.castling = ∅ ∧
      p.enPassant = none

theorem some_knight_ne_rook {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .knight } : Option Piece) =
      some { color := c₂, kind := .rook }) : False := by
  simp at h

theorem some_knight_ne_pawn {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .knight } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

theorem boardAfter_knight (p : Position) (m : Move) {c : Color}
    (hpromo : m.promotion = none) :
    p.boardAfter m { color := c, kind := .knight } =
      p.board.relocate m.src m.dst { color := c, kind := .knight } := by
  unfold boardAfter
  simp [hpromo]

theorem enPassantAfter_knight (m : Move) (c : Color) (b : Board) :
    enPassantAfter m { color := c, kind := .knight } b = none := by
  unfold enPassantAfter
  simp

theorem castlingSide_none_of_ortho (col : Color) {s t : Square}
    (h : OrthogonalAdjacent s t) :
    (Move.std s t).castlingSide? col = none := by
  revert col s t
  native_decide

theorem bool_eq_false_or_true (b : Bool) : b = false ∨ b = true := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem destOk_of_empty {p : Position} {m : Move}
    (h : p.board m.dst = none) : p.destOk m = true := by
  unfold destOk
  rw [h]

/-- Boolean skeleton of a non-pawn, non-castling `isLegalMove` check. -/
theorem legal_king_step_bool {unused₁ unused₂ : Bool} (att promoNone attacked : Bool)
    (hatt : att = true) (hpromo : promoNone = true) (hsafe : attacked = false) :
    ((if false = true then unused₁
      else if false = true then unused₂
      else att && promoNone) && !attacked) = true := by
  simp [hatt, hpromo, hsafe]

theorem eq_other_of_ne_color {a b : Color} (h : a ≠ b) : a = b.other := by
  cases a <;> cases b <;> simp_all [Color.other]

theorem IsKingAndKnight.knightToMove_not_inCheck {p : Position}
    {wk bk ns : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (ht : p.toMove = c) :
    p.inCheck = false := by
  unfold inCheck
  rw [hboard, ht]
  cases hc : c with
  | white =>
    have hiff := Board.kingsKnightBoard_kingIsAttacked_white wk bk ns .white
      hwk_bk hwk_ns hbk_ns
    cases hAtt : (Board.kingsKnightBoard wk bk ns Color.white).kingIsAttacked Color.white
    · rfl
    · have hP := hiff.mp hAtt
      rcases hP with hk | ⟨hcb, _⟩
      · exact (hna (kingAttacks_symmetric.mp hk)).elim
      · exact nomatch hcb
  | black =>
    have hiff := Board.kingsKnightBoard_kingIsAttacked_black wk bk ns .black
      hwk_bk hwk_ns hbk_ns
    cases hAtt : (Board.kingsKnightBoard wk bk ns Color.black).kingIsAttacked Color.black
    · rfl
    · have hP := hiff.mp hAtt
      rcases hP with hk | ⟨hcb, _⟩
      · exact (hna hk).elim
      · exact nomatch hcb

theorem IsKingAndKnight.inCheck_knightAttacks {p : Position}
    {wk bk ns : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (ht : p.toMove = c.other)
    (hchk : p.inCheck = true) :
    KnightAttacks ns (knLone wk bk c) := by
  unfold inCheck at hchk
  rw [hboard, ht] at hchk
  cases c with
  | white =>
    have hiff := Board.kingsKnightBoard_kingIsAttacked_black wk bk ns .white
      hwk_bk hwk_ns hbk_ns
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna hk).elim
    · exact h.2
  | black =>
    have hiff := Board.kingsKnightBoard_kingIsAttacked_white wk bk ns .black
      hwk_bk hwk_ns hbk_ns
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna (kingAttacks_symmetric.mp hk)).elim
    · exact h.2

theorem knEscape_ortho (wk bk : Square) (c : Color) :
    OrthogonalAdjacent (knLone wk bk c) (knEscape wk bk c) :=
  kingOrthoEscape_ortho _ _

theorem knEscape_not_kingAttacks (wk bk : Square) (c : Color)
    (hne : wk ≠ bk) (hna : ¬ KingAttacks wk bk) :
    ¬ KingAttacks (knSupport wk bk c) (knEscape wk bk c) := by
  cases c with
  | white =>
    exact kingOrthoEscape_not_kingAttacks bk wk hne hna
  | black =>
    exact kingOrthoEscape_not_kingAttacks wk bk hne.symm
      (mt kingAttacks_symmetric.mp hna)

theorem knEscape_ne_lone (wk bk : Square) (c : Color) :
    knEscape wk bk c ≠ knLone wk bk c :=
  kingOrthoEscape_ne_self _ _

theorem knEscape_ne_support (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    knEscape wk bk c ≠ knSupport wk bk c := by
  cases c with
  | white => exact kingOrthoEscape_ne_other bk wk hna
  | black =>
    exact kingOrthoEscape_ne_other wk bk (mt kingAttacks_symmetric.mp hna)

theorem knEscape_ne_knight {wk bk ns : Square} {c : Color}
    (hatt : KnightAttacks ns (knLone wk bk c)) :
    knEscape wk bk c ≠ ns := by
  intro heq
  have ho := knEscape_ortho wk bk c
  rw [heq] at ho
  exact not_knightAttacks_of_orthoAdj (orthoAdj_symmetric.mp ho) hatt

theorem knEscape_ne_wk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    knEscape wk bk c ≠ wk := by
  cases c with
  | white => exact knEscape_ne_support wk bk .white hna
  | black => exact knEscape_ne_lone wk bk .black

theorem knEscape_ne_bk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    knEscape wk bk c ≠ bk := by
  cases c with
  | white => exact knEscape_ne_lone wk bk .white
  | black => exact knEscape_ne_support wk bk .black hna

theorem kingKnight_escape_src {p : Position} {wk bk ns : Square} {c : Color}
    (hwk_bk : wk ≠ bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (ht : p.toMove = c.other) :
    p.board (knLone wk bk c) = some { color := p.toMove, kind := .king } := by
  rw [hboard, ht]
  cases c with
  | white =>
    simpa [knLone] using Board.kingsKnightBoard_black wk bk ns Color.white hwk_bk
  | black =>
    simpa [knLone] using Board.kingsKnightBoard_white wk bk ns Color.black

theorem kingKnight_escape_dst {p : Position} {wk bk ns : Square} {c : Color}
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (hattN : KnightAttacks ns (knLone wk bk c)) :
    p.board (knEscape wk bk c) = none := by
  rw [hboard]
  exact Board.kingsKnightBoard_other wk bk ns (knEscape wk bk c) c
    (knEscape_ne_wk wk bk c hna)
    (knEscape_ne_bk wk bk c hna)
    (knEscape_ne_knight hattN)

theorem kingKnight_play_escape_board_white {p : Position} {wk bk ns : Square}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns .white)
    (ht : p.toMove = .black)
    (hattN : KnightAttacks ns bk)
    (hsrc : m.src = bk)
    (hdst : m.dst = knEscape wk bk .white)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .black = none)
    (hsrcP : p.board m.src = some { color := .black, kind := .king }) :
    (p.play m).board =
      Board.kingsKnightBoard wk (knEscape wk bk .white) ns .white := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .black) hside hpromo
  have htne_wk := knEscape_ne_wk wk bk .white hna
  have htne_bk := knEscape_ne_bk wk bk .white hna
  have htne_ns : knEscape wk bk .white ≠ ns :=
    knEscape_ne_knight (wk := wk) (bk := bk) (c := Color.white)
      (show KnightAttacks ns (knLone wk bk Color.white) from hattN)
  have hrel := Board.relocate_kingsKnightBoard_black wk bk ns (knEscape wk bk .white)
    Color.white hwk_bk hwk_ns hbk_ns htne_wk htne_bk htne_ns
  calc (p.play m).board
      = p.boardAfter m { color := .black, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
    _ = (Board.kingsKnightBoard wk bk ns .white).relocate
          bk (knEscape wk bk .white) { color := .black, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsKnightBoard wk (knEscape wk bk .white) ns .white := hrel

theorem kingKnight_play_escape_board_black {p : Position} {wk bk ns : Square}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns .black)
    (ht : p.toMove = .white)
    (hattN : KnightAttacks ns wk)
    (hsrc : m.src = wk)
    (hdst : m.dst = knEscape wk bk .black)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .white = none)
    (hsrcP : p.board m.src = some { color := .white, kind := .king }) :
    (p.play m).board =
      Board.kingsKnightBoard (knEscape wk bk .black) bk ns .black := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .white) hside hpromo
  have htne_wk := knEscape_ne_wk wk bk .black hna
  have htne_bk := knEscape_ne_bk wk bk .black hna
  have htne_ns : knEscape wk bk .black ≠ ns :=
    knEscape_ne_knight (wk := wk) (bk := bk) (c := Color.black)
      (show KnightAttacks ns (knLone wk bk Color.black) from hattN)
  have hrel := Board.relocate_kingsKnightBoard_white wk bk ns (knEscape wk bk .black)
    Color.black hwk_bk hwk_ns hbk_ns htne_wk htne_bk htne_ns
  calc (p.play m).board
      = p.boardAfter m { color := .white, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
    _ = (Board.kingsKnightBoard wk bk ns .black).relocate
          wk (knEscape wk bk .black) { color := .white, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsKnightBoard (knEscape wk bk .black) bk ns .black := hrel

theorem kingKnight_escape_safe {p : Position} {wk bk ns : Square} {c : Color}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (ht : p.toMove = c.other)
    (hattN : KnightAttacks ns (knLone wk bk c))
    (hsrc : m.src = knLone wk bk c)
    (hdst : m.dst = knEscape wk bk c)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? p.toMove = none)
    (hsrcP : p.board m.src = some { color := p.toMove, kind := .king }) :
    (p.play m).board.kingIsAttacked p.toMove = false := by
  have ho := knEscape_ortho wk bk c
  have hnk := knEscape_not_kingAttacks wk bk c hwk_bk hna
  have hnn : ¬ KnightAttacks ns (knEscape wk bk c) :=
    orthoAdj_not_knightAttacks ho hattN
  cases c with
  | white =>
    have hnb := kingKnight_play_escape_board_white hwk_bk hwk_ns hbk_ns hna
      hboard ht hattN hsrc hdst hpromo (by simpa [ht] using hside)
      (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_wk := knEscape_ne_wk wk bk .white hna
    have hiff := Board.kingsKnightBoard_kingIsAttacked_black wk
      (knEscape wk bk .white) ns .white htne_wk.symm hwk_ns
      (knEscape_ne_knight (wk := wk) (bk := bk) (c := Color.white) hattN)
    cases hAtt :
      (Board.kingsKnightBoard wk (knEscape wk bk .white) ns .white).kingIsAttacked
        .black
    · simpa [Color.other] using hAtt
    · rcases hiff.mp hAtt with hk | ⟨_, hN⟩
      · exact (hnk hk).elim
      · exact (hnn hN).elim
  | black =>
    have hnb := kingKnight_play_escape_board_black hwk_bk hwk_ns hbk_ns hna
      hboard ht hattN hsrc hdst hpromo (by simpa [ht] using hside)
      (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_ns : knEscape wk bk .black ≠ ns :=
      knEscape_ne_knight (wk := wk) (bk := bk) (c := Color.black) hattN
    have hiff := Board.kingsKnightBoard_kingIsAttacked_white
      (knEscape wk bk .black) bk ns .black
      (knEscape_ne_bk wk bk .black hna) htne_ns hbk_ns
    cases hAtt :
      (Board.kingsKnightBoard (knEscape wk bk .black) bk ns .black).kingIsAttacked
        .white
    · simpa [Color.other] using hAtt
    · rcases hiff.mp hAtt with hk | ⟨_, hN⟩
      · exact (hnk hk).elim
      · exact (hnn hN).elim

theorem kingKnight_escape_isLegalMove {p : Position} {wk bk ns : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (ht : p.toMove = c.other)
    (hchk : p.inCheck = true) :
    isLegalMove p (Move.std (knLone wk bk c) (knEscape wk bk c)) = true := by
  let m := Move.std (knLone wk bk c) (knEscape wk bk c)
  have hattN := IsKingAndKnight.inCheck_knightAttacks
    hwk_bk hwk_ns hbk_ns hna hboard ht hchk
  have hsrcP : p.board (knLone wk bk c) =
      some { color := p.toMove, kind := .king } :=
    kingKnight_escape_src hwk_bk hboard ht
  have hdstNone := kingKnight_escape_dst hna hboard hattN
  have ho := knEscape_ortho wk bk c
  have hside := castlingSide_none_of_ortho p.toMove ho
  have hgeo : p.board.attacks (knLone wk bk c) (knEscape wk bk c) = true := by
    have hsk : Board.kingsKnightBoard wk bk ns c (knLone wk bk c) =
        some { color := p.toMove, kind := .king } := by
      simpa [hboard] using hsrcP
    rw [hboard, Board.attacks_king hsk]
    exact decide_eq_true (orthoAdj_kingAttacks ho)
  have hsrcP' : p.board m.src = some { color := p.toMove, kind := .king } := hsrcP
  have hsafe := kingKnight_escape_safe hwk_bk hwk_ns hbk_ns hna hboard ht hattN
    (rfl : m.src = knLone wk bk c) (rfl : m.dst = knEscape wk bk c) rfl hside hsrcP'
  unfold isLegalMove
  rw [hsrcP']
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := m) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std (knLone wk bk c) (knEscape wk bk c)).castlingSide?
      p.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool
    (p.board.attacks (knLone wk bk c) (knEscape wk bk c))
    ((Move.std (knLone wk bk c) (knEscape wk bk c)).promotion == none)
    ((p.play m).board.kingIsAttacked p.toMove)
    hgeo rfl hsafe

set_option linter.constructorNameAsVariable false

theorem IsKingAndKnight.not_inCheckmate {p : Position} (h : IsKingAndKnight p) :
    p.inCheckmate = false := by
  set_option maxRecDepth 1024 in
  obtain ⟨wk, bk, ns, c, hwk_bk, hwk_ns, hbk_ns, hna, hboard, _, _⟩ := h
  by_cases ht : p.toMove = c
  · exact not_inCheck_not_inCheckmate
      (IsKingAndKnight.knightToMove_not_inCheck hwk_bk hwk_ns hbk_ns hna hboard ht)
  · have ht' : p.toMove = c.other := eq_other_of_ne_color ht
    have hsplit := bool_eq_false_or_true p.inCheck
    cases hsplit with
    | inl hIn => exact not_inCheck_not_inCheckmate hIn
    | inr hIn =>
      have hleg := kingKnight_escape_isLegalMove hwk_bk hwk_ns hbk_ns hna
        hboard ht' hIn
      have hmem :
          Move.std (knLone wk bk c) (knEscape wk bk c) ∈ p.legalMoves :=
        (mem_legalMoves p _).mpr hleg
      have hne : p.legalMoves.card ≠ 0 :=
        mt Finset.card_eq_zero.mp (Finset.ne_empty_of_mem hmem)
      unfold inCheckmate
      rw [hIn]
      simp only [Bool.true_and]
      exact beq_eq_false_iff_ne.mpr hne

theorem IsKingAndKnight.not_InCheckmate {p : Position} (h : IsKingAndKnight p) :
    ¬ InCheckmate p :=
  mt (inCheckmate_eq_true_iff p).mpr
    (Eq.trans_ne h.not_inCheckmate Bool.false_ne_true)

theorem destOk_kingsKnightBoard {p : Position} {m : Move} {wk bk ns : Square}
    {c : Color}
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = ns := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsKnightBoard wk bk ns c m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsKnightBoard at hdst
    split_ifs at hdst with h1 h2 h3
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr h3

theorem kingKnight_legalMove_core {p : Position} {m : Move} {wk bk ns : Square}
    {c : Color}
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = ns) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .knight) ∧
        (piece.kind = .king → m.castlingSide? p.toMove = none) := by
  have hm' : isLegalMove p m = true := hm
  unfold isLegalMove at hm'
  cases hsrcB : p.board m.src with
  | none => simp [hsrcB] at hm'
  | some piece =>
    simp only [hsrcB, Bool.and_eq_true] at hm'
    obtain ⟨⟨hcolDest, hifs⟩, hsafeB⟩ := hm'
    have hcol' : piece.color = p.toMove := beq_iff_eq.mp hcolDest.1
    have hdestOk : p.destOk m = true := hcolDest.2
    have hdstOr := destOk_kingsKnightBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsKnightBoard wk bk ns c m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .knight := by
      have hsrc' := hsrc
      unfold Board.kingsKnightBoard at hsrc'
      split_ifs at hsrc' with _h1 _h2 _h3
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inr rfl
    have hpawn : (piece.kind == PieceKind.pawn) = false := by
      cases hkind with
      | inl hk => simp [hk]
      | inr hn => simp [hn]
    have hside : piece.kind = .king → m.castlingSide? p.toMove = none := by
      intro hk
      cases hopt : m.castlingSide? p.toMove with
      | none => rfl
      | some _ =>
        have hs : (m.castlingSide? p.toMove).isSome = true := by simp [hopt]
        have hcastle := castleMoveOk_of_empty (m := m) hcstl
        have hifs' := hifs
        simp [hk, hs, hcastle] at hifs'
    have hpromo : m.promotion = none := by
      cases hkind with
      | inl hk =>
        have hsnone := hside hk
        have hifs' : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
          simpa [hpawn, hk, hsnone, Bool.and_eq_true, beq_iff_eq] using hifs
        exact hifs'.2
      | inr hn =>
        have hifs' : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
          simpa [hpawn, hn, Bool.and_eq_true, beq_iff_eq] using hifs
        exact hifs'.2
    exact ⟨hpromo, hdestOk, hdstOr, hsafe, piece, rfl, hcol', hkind, hside⟩

theorem destOk_toMove_of_dst_knight {p : Position} {m : Move}
    {wk bk ns : Square} {c : Color}
    (hboard : p.board = Board.kingsKnightBoard wk bk ns c)
    (hwk_ns : wk ≠ ns) (hbk_ns : bk ≠ ns)
    (hdst : m.dst = ns) (hok : p.destOk m = true) :
    p.toMove = c.other := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem piece_eq_of_eq_some {p : Position} {s : Square} {piece q : Piece}
    (h1 : p.board s = some piece) (h2 : p.board s = some q) : piece = q :=
  Option.some.inj (h1.symm.trans h2)

theorem some_king_ne_knight {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .knight }) : False := by
  simp at h

theorem IsKingAndKnight.of_play {p : Position} {m : Move}
    (h : IsKingAndKnight p) (hm : LegalMove p m) :
    IsKingAndKnight (p.play m) ∨ IsTwoKings (p.play m) := by
  obtain ⟨wk, bk, ns, c, hwk_bk, hwk_ns, hbk_ns, hna, hboard, hcstl, _hep⟩ := h
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, piece, hsrcP, hcol', hkind, hside⟩ :=
    kingKnight_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = ns :=
    (Board.kingsKnightBoard_isSome wk bk ns m.src c).mp (by
      have : (p.board m.src).isSome = true := by simp [hsrcP]
      simpa [hboard] using this)
  have hcast' : (p.play m).castling = ∅ := by
    rw [hplay]
    cases hkind with
    | inl hk =>
      have hpiece : piece = { color := p.toMove, kind := .king } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_king_no_castle p m (c := p.toMove)
        (hside (by simp [hpiece])) hpromo, hcstl]
      exact castlingAfter_empty _
    | inr hn =>
      have hpiece : piece = { color := p.toMove, kind := .knight } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_knight p m (c := p.toMove) hpromo, hcstl]
      exact castlingAfter_empty _
  have hep' : (p.play m).enPassant = none := by
    cases hkind with
    | inl hk =>
      have hpiece : piece = { color := p.toMove, kind := .king } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .king }
              (p.boardAfter m { color := p.toMove, kind := .king }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_king _ _ _
    | inr hn =>
      have hpiece : piece = { color := p.toMove, kind := .knight } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .knight }
              (p.boardAfter m { color := p.toMove, kind := .knight }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_knight _ _ _
  rcases hdstOr with hdstNone | hdstNs
  · -- Empty destination: the three pieces remain.
    have hdstW : m.dst ≠ wk := by
      intro heq; rw [heq, hboard, Board.kingsKnightBoard_white] at hdstNone; cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsKnightBoard_black wk bk ns c hwk_bk] at hdstNone
      cases hdstNone
    have hdstS : m.dst ≠ ns := by
      intro heq
      rw [heq, hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns] at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · -- White king moves.
      have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsKnightBoard_white])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsKnightBoard_white wk bk ns m.dst c
        hwk_bk hwk_ns hbk_ns hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsKnightBoard m.dst bk ns c := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsKnightBoard wk bk ns c).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsKnightBoard m.dst bk ns c := hrel
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by simpa [ht] using hsafe
        have hiff := Board.kingsKnightBoard_kingIsAttacked_white m.dst bk ns c
          hdstB hdstS hbk_ns
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨m.dst, bk, ns, c, hdstB, hdstS, hbk_ns, hna', hboard', hcast', hep'⟩
    · -- Black king moves.
      have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsKnightBoard_black wk bk ns c hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsKnightBoard_black wk bk ns m.dst c
        hwk_bk hwk_ns hbk_ns hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsKnightBoard wk m.dst ns c := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsKnightBoard wk bk ns c).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsKnightBoard wk m.dst ns c := hrel
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by simpa [ht] using hsafe
        have hiff := Board.kingsKnightBoard_kingIsAttacked_black wk m.dst ns c
          hdstW.symm hwk_ns hdstS
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨wk, m.dst, ns, c, hdstW.symm, hwk_ns, hdstS, hna', hboard', hcast', hep'⟩
    · -- Knight moves.
      have hpiece : piece = { color := c, kind := .knight } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcS, hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns])
      have ht : p.toMove = c := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_knight p m (c := c) hpromo
      have hrel := Board.relocate_kingsKnightBoard_knight wk bk ns m.dst c
        hwk_bk hwk_ns hbk_ns hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsKnightBoard wk bk m.dst c := by
        calc (p.play m).board
            = p.boardAfter m { color := c, kind := .knight } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := c, kind := .knight } := hba
          _ = (Board.kingsKnightBoard wk bk ns c).relocate ns m.dst
                { color := c, kind := .knight } := by
              rw [hboard, hsrcS]
          _ = Board.kingsKnightBoard wk bk m.dst c := hrel
      exact Or.inl ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep'⟩
  · -- Capture on the knight's square: two kings remain.
    have hknight : p.board ns = some { color := c, kind := .knight } := by
      rw [hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns]
    have ht : p.toMove = c.other :=
      destOk_toMove_of_dst_knight hboard hwk_ns hbk_ns hdstNs hdestOk
    have hsrcNeNs : m.src ≠ ns := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hknight] at hsrcP'
      have hpc : c = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      exact Color.other_ne c hpc.symm
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · -- White king captures the black knight.
      have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsKnightBoard_white])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.black := by
        have : c.other = Color.white := ht.symm.trans htW
        cases c
        · simp [Color.other] at this
        · rfl
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [htW] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_knight_white wk bk ns hwk_bk hwk_ns hbk_ns
      have hboard' : (p.play m).board = Board.kingsBoard ns bk := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsKnightBoard wk bk ns .black).relocate wk ns
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstNs, hc]
          _ = Board.kingsBoard ns bk := hrel
      have hna' : ¬ KingAttacks ns bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [htW] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_white ns bk hbk_ns.symm] at hsafe'
        exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
      exact Or.inr ⟨ns, bk, hbk_ns.symm, hna', hboard', hcast', hep'⟩
    · -- Black king captures the white knight.
      have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsKnightBoard_black wk bk ns c hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.white := by
        have : c.other = Color.black := ht.symm.trans htB
        cases c
        · rfl
        · simp [Color.other] at this
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [htB] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_knight_black wk bk ns hwk_bk hwk_ns hbk_ns
      have hboard' : (p.play m).board = Board.kingsBoard wk ns := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsKnightBoard wk bk ns .white).relocate bk ns
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstNs, hc]
          _ = Board.kingsBoard wk ns := hrel
      have hna' : ¬ KingAttacks wk ns := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [htB] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_black wk ns hwk_ns] at hsafe'
        exact of_decide_eq_false hsafe'
      exact Or.inr ⟨wk, ns, hwk_ns, hna', hboard', hcast', hep'⟩
    · exact (hsrcNeNs hsrcS).elim

theorem IsKingAndKnight.of_reachable {p q : Position}
    (h : IsKingAndKnight p) (hr : Reachable p q) :
    IsKingAndKnight q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    cases ih with
    | inl hkn => exact hkn.of_play hleg
    | inr htk => exact Or.inr (htk.of_play hleg)

/-- A valid position with exactly three occupied squares, one of them a
knight, holds only the two kings and that knight, with the kings not
adjacent. -/
theorem isKingAndKnight_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hknight : ∃ s c, p.board s = some { color := c, kind := .knight }) :
    IsKingAndKnight p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨ns, c, hns⟩ := hknight
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_ns : wk ≠ ns := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hns)
  have hbk_ns : bk ≠ ns := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_knight (hking.symm.trans hns)
  have hoccEq : p.board.occupied = {wk, bk, ns} := by
    have hsub : ({wk, bk, ns} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hns]
    have hcard : ({wk, bk, ns} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_ns]
      · simp [hwk_bk, hwk_ns]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsKnightBoard wk bk ns c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsKnightBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsKnightBoard_black wk bk ns c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = ns
        · rw [hs, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns]
          exact hns
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsKnightBoard_other wk bk ns s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsKnightBoard_kingIsAttacked_black wk bk ns c
          hwk_bk hwk_ns hbk_ns).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsKnightBoard_kingIsAttacked_white wk bk ns c
          hwk_bk hwk_ns hbk_ns).mpr (Or.inl (kingAttacks_symmetric.mp hk))
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
  have hc : p.castling = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro r hr
    obtain ⟨_, hrook⟩ := hcast r hr
    have hmem : r.rookSquare ∈ p.board.occupied := by
      simp [Board.mem_occupied, hrook]
    rw [hoccEq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hsq | hsq | hsq
    · rw [hsq, hboard, Board.kingsKnightBoard_white] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsKnightBoard_black wk bk ns c hwk_bk] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns] at hrook
      exact some_knight_ne_rook hrook
  have he : p.enPassant = none := by
    cases hep' : p.enPassant with
    | none => rfl
    | some ep =>
      obtain ⟨_, _, hcap⟩ :=
        (enPassantOk_some p ep hep').mp (by simpa [hep'] using hep)
      obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp hcap
      have hpawn := (hasPawn_eq_true_iff _ _ _).mp hs
      have hmem : s ∈ p.board.occupied := by
        simp [Board.mem_occupied, hpawn]
      rw [hoccEq] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hsq | hsq | hsq
      · rw [hsq, hboard, Board.kingsKnightBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsKnightBoard_black wk bk ns c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsKnightBoard_knight wk bk ns c hwk_ns hbk_ns] at hpawn
        cases some_knight_ne_pawn hpawn
  exact ⟨wk, bk, ns, c, hwk_bk, hwk_ns, hbk_ns, hna, hboard, hc, he⟩

theorem not_inCheckmate_of_kn_or_tk {q : Position}
    (h : IsKingAndKnight q ∨ IsTwoKings q) : q.inCheckmate = false := by
  cases h with
  | inl hkn => exact hkn.not_inCheckmate
  | inr htk => exact htk.not_inCheckmate

theorem not_InCheckmate_of_kn_or_tk {q : Position}
    (h : IsKingAndKnight q ∨ IsTwoKings q) : ¬ InCheckmate q := by
  cases h with
  | inl hkn => exact hkn.not_InCheckmate
  | inr htk => exact htk.not_InCheckmate

/-- A valid king-and-knight versus king position is never checkmate. -/
theorem kingKnight_not_inCheckmate {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hknight : ∃ s c, p.board s = some { color := c, kind := .knight }) :
    p.inCheckmate = false :=
  (isKingAndKnight_of_valid hv hocc hknight).not_inCheckmate

/-- From a valid position with only two kings and one knight, every
legally reachable position is still not checkmate. -/
theorem kingKnight_reachable_not_inCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hknight : ∃ s c, p.board s = some { color := c, kind := .knight })
    (hr : Reachable p q) : q.inCheckmate = false :=
  not_inCheckmate_of_kn_or_tk
    (IsKingAndKnight.of_reachable (isKingAndKnight_of_valid hv hocc hknight) hr)

/-- From a valid position with only two kings and one knight, no
sequence of legal moves produces checkmate. -/
theorem kingKnight_legalSeq_not_inCheckmate {p : Position} {ms : List Move}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hknight : ∃ s c, p.board s = some { color := c, kind := .knight })
    (hms : LegalSeq p ms) :
    (playSeq p ms).inCheckmate = false :=
  kingKnight_reachable_not_inCheckmate hv hocc hknight (legalSeq_reachable hms)

theorem kingKnight_reachable_not_InCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hknight : ∃ s c, p.board s = some { color := c, kind := .knight })
    (hr : Reachable p q) : ¬ InCheckmate q :=
  not_InCheckmate_of_kn_or_tk
    (IsKingAndKnight.of_reachable (isKingAndKnight_of_valid hv hocc hknight) hr)

/-! ### Example: kings on `e1` and `e8`, knight on `c2` -/

/-- White king on `e1`, black king on `e8`, black knight on `c2`, White
to move. -/
def kingAndKnight : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c2 then some { color := .black, kind := .knight }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingAndKnight_isValid : isValid kingAndKnight = true := by
  native_decide

theorem kingAndKnight_occupied_card : kingAndKnight.board.occupied.card = 3 := by
  native_decide

theorem kingAndKnight_has_knight :
    ∃ s c, kingAndKnight.board s = some { color := c, kind := .knight } :=
  ⟨Square.c2, Color.black, by native_decide⟩

theorem kingAndKnight_not_inCheckmate : kingAndKnight.inCheckmate = false :=
  kingKnight_not_inCheckmate
    ((isValid_eq_true_iff kingAndKnight).mp kingAndKnight_isValid)
    kingAndKnight_occupied_card
    kingAndKnight_has_knight

/-- White's `e1–e2` is a legal flight from the knight check. -/
theorem kingAndKnight_e1e2_legal :
    isLegalMove kingAndKnight (Move.std Square.e1 Square.e2) = true := by
  native_decide

/-- After `e1–e2`, the position is still not checkmate. -/
theorem kingAndKnight_play_e1e2_not_inCheckmate :
    (kingAndKnight.play (Move.std Square.e1 Square.e2)).inCheckmate = false := by
  native_decide

end Position

end Chess
