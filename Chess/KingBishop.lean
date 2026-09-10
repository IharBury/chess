import Chess.TwoKings

/-!
# King and bishop versus king

A valid position whose board holds only the two kings and one bishop is
never checkmate. The side that has the bishop is not in check: the lone
king is the only enemy piece, and the kings are not adjacent (otherwise
the opponent would be in check). The lone king, if in check, is checked
by the bishop and therefore stands on the bishop's square-color; an
orthogonal neighbor has the opposite color, so the bishop cannot cover
it. The other king, not being adjacent, cannot cover both the horizontal
and the vertical neighbor, so one of those squares is a legal flight.
A legal move either keeps the same three pieces or captures the bishop,
leaving two kings. In the latter case `IsTwoKings` applies. Hence no
sequence of legal moves produces checkmate.
-/

namespace Chess

namespace Board

/-- White king on `wk`, black king on `bk`, and a bishop of color `c` on
`bs`. -/
def kingsBishopBoard (wk bk bs : Square) (c : Color) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = bs then some { color := c, kind := .bishop }
  else none

theorem kingsBishopBoard_white (wk bk bs : Square) (c : Color) :
    kingsBishopBoard wk bk bs c wk = some { color := .white, kind := .king } := by
  simp [kingsBishopBoard]

theorem kingsBishopBoard_black (wk bk bs : Square) (c : Color) (h : wk ≠ bk) :
    kingsBishopBoard wk bk bs c bk = some { color := .black, kind := .king } := by
  simp [kingsBishopBoard, h.symm]

theorem kingsBishopBoard_bishop (wk bk bs : Square) (c : Color)
    (hw : wk ≠ bs) (hb : bk ≠ bs) :
    kingsBishopBoard wk bk bs c bs = some { color := c, kind := .bishop } := by
  simp [kingsBishopBoard, hw.symm, hb.symm]

theorem kingsBishopBoard_other (wk bk bs s : Square) (c : Color)
    (hw : s ≠ wk) (hb : s ≠ bk) (hbs : s ≠ bs) :
    kingsBishopBoard wk bk bs c s = none := by
  simp [kingsBishopBoard, hw, hb, hbs]

theorem kingsBishopBoard_eq_white_king {wk bk bs s : Square} {c : Color}
    (h : kingsBishopBoard wk bk bs c s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsBishopBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopBoard_eq_black_king {wk bk bs s : Square} {c : Color}
    (h : kingsBishopBoard wk bk bs c s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsBishopBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopBoard_eq_bishop {wk bk bs s : Square} {c : Color}
    (h : kingsBishopBoard wk bk bs c s = some { color := c, kind := .bishop }) :
    s = bs := by
  unfold kingsBishopBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopBoard_isSome (wk bk bs s : Square) (c : Color) :
    ((kingsBishopBoard wk bk bs c) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = bs := by
  unfold kingsBishopBoard
  split_ifs <;> simp_all

theorem attacks_bishop_iff {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .bishop }) :
    b.attacks s t = true ↔
      BishopAttacks s t ∧
        ¬ ∃ u : Square, Between s t u ∧ (b u).isSome = true := by
  unfold attacks
  rw [h]
  simp only [PieceKind.bishop_isSlider, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not]

theorem kingsBishopBoard_bishop_blocked {wk bk bs t : Square} {c : Color} :
    (∃ u : Square, Between bs t u ∧
        ((kingsBishopBoard wk bk bs c) u).isSome = true) ↔
      Between bs t wk ∨ Between bs t bk := by
  constructor
  · intro ⟨u, hB, hocc⟩
    have hu : u = wk ∨ u = bk ∨ u = bs :=
      (kingsBishopBoard_isSome wk bk bs u c).mp hocc
    rcases hu with hu | hu | hu
    · subst u; exact Or.inl hB
    · subst u; exact Or.inr hB
    · subst u
      exact (hB.1 rfl).elim
  · intro h
    cases h with
    | inl hB =>
      exact ⟨wk, hB, (kingsBishopBoard_isSome wk bk bs wk c).mpr (Or.inl rfl)⟩
    | inr hB =>
      exact ⟨bk, hB, (kingsBishopBoard_isSome wk bk bs bk c).mpr (Or.inr (Or.inl rfl))⟩

theorem kingsBishopBoard_attacks_bishop_iff {wk bk bs t : Square} {c : Color}
    (hw : wk ≠ bs) (hb : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).attacks bs t = true ↔
      BishopAttacks bs t ∧ ¬ Between bs t wk ∧ ¬ Between bs t bk := by
  rw [attacks_bishop_iff (kingsBishopBoard_bishop wk bk bs c hw hb),
    kingsBishopBoard_bishop_blocked]
  tauto

theorem kingsBishopBoard_occupiedBy_white (wk bk bs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_bs : wk ≠ bs) (_hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).occupiedBy .white =
      match c with
      | .white => {wk, bs}
      | .black => {wk} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsBishopBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsBishopBoard
    split_ifs <;> simp_all

theorem kingsBishopBoard_occupiedBy_black (wk bk bs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_bs : wk ≠ bs) (_hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).occupiedBy .black =
      match c with
      | .white => {bk}
      | .black => {bk, bs} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsBishopBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsBishopBoard
    split_ifs <;> simp_all

theorem kingsBishopBoard_kingSquares_white (wk bk bs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_bs : wk ≠ bs) (_hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsBishopBoard
  split_ifs <;> simp_all

theorem kingsBishopBoard_kingSquares_black (wk bk bs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_bs : wk ≠ bs) (_hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsBishopBoard
  split_ifs <;> simp_all

theorem kingsBishopBoard_occupied (wk bk bs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_bs : wk ≠ bs) (_hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).occupied = {wk, bk, bs} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsBishopBoard
  split_ifs <;> simp_all

theorem kingsBishopBoard_black_piece {wk bk bs s : Square} {c : Color}
    (h : (kingsBishopBoard wk bk bs c s).map (·.color) = some .black) :
    s = bk ∨ (c = .black ∧ s = bs) := by
  unfold kingsBishopBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopBoard_white_piece {wk bk bs s : Square} {c : Color}
    (h : (kingsBishopBoard wk bk bs c s).map (·.color) = some .white) :
    s = wk ∨ (c = .white ∧ s = bs) := by
  unfold kingsBishopBoard at h
  split_ifs at h <;> simp_all

theorem kingsBishopBoard_kingIsAttacked_white (wk bk bs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨
        (c = .black ∧ BishopAttacks bs wk ∧ ¬ Between bs wk bk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBishopBoard_kingSquares_white wk bk bs c hwk_bk hwk_bs hbk_bs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsBishopBoard_black_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsBishopBoard_black wk bk bs c hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsBishopBoard_attacks_bishop_iff (t := wk) (c := Color.black)
        hwk_bs hbk_bs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.2⟩
  · intro h
    rcases h with hk | ⟨hc, hB, hnb⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopBoard_black wk bk bs c hwk_bk]
      · rw [attacks_king (kingsBishopBoard_black wk bk bs c hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨bs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsBishopBoard_bishop wk bk bs Color.black hwk_bs hbk_bs]
      · subst hc
        rw [kingsBishopBoard_attacks_bishop_iff (t := wk) (c := Color.black)
          hwk_bs hbk_bs]
        exact ⟨hB, fun hBet => (hBet.2.1 rfl).elim, hnb⟩

theorem kingsBishopBoard_kingIsAttacked_black (wk bk bs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs) :
    (kingsBishopBoard wk bk bs c).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨
        (c = .white ∧ BishopAttacks bs bk ∧ ¬ Between bs bk wk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBishopBoard_kingSquares_black wk bk bs c hwk_bk hwk_bs hbk_bs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsBishopBoard_white_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsBishopBoard_white wk bk bs c)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsBishopBoard_attacks_bishop_iff (t := bk) (c := Color.white)
        hwk_bs hbk_bs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.1⟩
  · intro h
    rcases h with hk | ⟨hc, hB, hnb⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsBishopBoard_white]
      · rw [attacks_king (kingsBishopBoard_white wk bk bs c)]
        exact decide_eq_true hk
    · refine ⟨bs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsBishopBoard_bishop wk bk bs Color.white hwk_bs hbk_bs]
      · subst hc
        rw [kingsBishopBoard_attacks_bishop_iff (t := bk) (c := Color.white)
          hwk_bs hbk_bs]
        exact ⟨hB, hnb, fun hBet => (hBet.2.1 rfl).elim⟩

theorem relocate_kingsBishopBoard_white (wk bk bs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwb : wk ≠ bs) (_hbb : bk ≠ bs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hds : dst ≠ bs) :
    (kingsBishopBoard wk bk bs c).relocate wk dst { color := .white, kind := .king } =
      kingsBishopBoard dst bk bs c := by
  funext s
  unfold relocate kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_kingsBishopBoard_black (wk bk bs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwb : wk ≠ bs) (_hbb : bk ≠ bs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hds : dst ≠ bs) :
    (kingsBishopBoard wk bk bs c).relocate bk dst { color := .black, kind := .king } =
      kingsBishopBoard wk dst bs c := by
  funext s
  unfold relocate kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_kingsBishopBoard_bishop (wk bk bs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwb : wk ≠ bs) (_hbb : bk ≠ bs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hds : dst ≠ bs) :
    (kingsBishopBoard wk bk bs c).relocate bs dst { color := c, kind := .bishop } =
      kingsBishopBoard wk bk dst c := by
  funext s
  unfold relocate kingsBishopBoard
  split_ifs <;> simp_all

theorem relocate_capture_bishop_white (wk bk bs : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ bs) (_hbb : bk ≠ bs) :
    (kingsBishopBoard wk bk bs .black).relocate wk bs
      { color := .white, kind := .king } =
      kingsBoard bs bk := by
  funext s
  unfold relocate kingsBishopBoard kingsBoard
  split_ifs <;> simp_all

theorem relocate_capture_bishop_black (wk bk bs : Square)
    (_hne : wk ≠ bk) (_hwb : wk ≠ bs) (_hbb : bk ≠ bs) :
    (kingsBishopBoard wk bk bs .white).relocate bk bs
      { color := .black, kind := .king } =
      kingsBoard wk bs := by
  funext s
  unfold relocate kingsBishopBoard kingsBoard
  split_ifs <;> simp_all

end Board

namespace Position

/-- Square of the king that does not own the bishop. -/
def kbLone (wk bk : Square) (c : Color) : Square :=
  match c with
  | .white => bk
  | .black => wk

/-- Square of the king that owns the bishop. -/
def kbSupport (wk bk : Square) (c : Color) : Square :=
  match c with
  | .white => wk
  | .black => bk

/-- Orthogonal flight square for the lone king. -/
def kbEscape (wk bk : Square) (c : Color) : Square :=
  kingOrthoEscape (kbLone wk bk c) (kbSupport wk bk c)

/-- `p` contains only two kings and one bishop, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingAndBishop (p : Position) : Prop :=
  ∃ wk bk bs : Square, ∃ c : Color,
    wk ≠ bk ∧
      wk ≠ bs ∧
      bk ≠ bs ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsBishopBoard wk bk bs c ∧
      p.castling = ∅ ∧
      p.enPassant = none

theorem some_bishop_ne_rook {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .bishop } : Option Piece) =
      some { color := c₂, kind := .rook }) : False := by
  simp at h

theorem some_bishop_ne_pawn {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .bishop } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

theorem boardAfter_bishop (p : Position) (m : Move) {c : Color}
    (hpromo : m.promotion = none) :
    p.boardAfter m { color := c, kind := .bishop } =
      p.board.relocate m.src m.dst { color := c, kind := .bishop } := by
  unfold boardAfter
  simp [hpromo]

theorem enPassantAfter_bishop (m : Move) (c : Color) (b : Board) :
    enPassantAfter m { color := c, kind := .bishop } b = none := by
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

theorem IsKingAndBishop.bishopToMove_not_inCheck {p : Position}
    {wk bk bs : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (ht : p.toMove = c) :
    p.inCheck = false := by
  unfold inCheck
  rw [hboard, ht]
  cases hc : c with
  | .white =>
    have hiff := Board.kingsBishopBoard_kingIsAttacked_white wk bk bs .white
      hwk_bk hwk_bs hbk_bs
    cases hAtt : (Board.kingsBishopBoard wk bk bs Color.white).kingIsAttacked Color.white
    · rfl
    · have hP := hiff.mp hAtt
      rcases hP with hk | ⟨hcb, _⟩
      · exact (hna (kingAttacks_symmetric.mp hk)).elim
      · exact nomatch hcb
  | .black =>
    have hiff := Board.kingsBishopBoard_kingIsAttacked_black wk bk bs .black
      hwk_bk hwk_bs hbk_bs
    cases hAtt : (Board.kingsBishopBoard wk bk bs Color.black).kingIsAttacked Color.black
    · rfl
    · have hP := hiff.mp hAtt
      rcases hP with hk | ⟨hcb, _⟩
      · exact (hna hk).elim
      · exact nomatch hcb

theorem IsKingAndBishop.inCheck_bishopAttacks {p : Position}
    {wk bk bs : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (ht : p.toMove = c.other)
    (hchk : p.inCheck = true) :
    BishopAttacks bs (kbLone wk bk c) := by
  unfold inCheck at hchk
  rw [hboard, ht] at hchk
  cases c with
  | .white =>
    have hiff := Board.kingsBishopBoard_kingIsAttacked_black wk bk bs .white
      hwk_bk hwk_bs hbk_bs
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna hk).elim
    · exact h.2.1
  | .black =>
    have hiff := Board.kingsBishopBoard_kingIsAttacked_white wk bk bs .black
      hwk_bk hwk_bs hbk_bs
    have hP := hiff.mp hchk
    rcases hP with hk | h
    · exact (hna (kingAttacks_symmetric.mp hk)).elim
    · exact h.2.1

theorem kbEscape_ortho (wk bk : Square) (c : Color) :
    OrthogonalAdjacent (kbLone wk bk c) (kbEscape wk bk c) :=
  kingOrthoEscape_ortho _ _

theorem kbEscape_not_kingAttacks (wk bk : Square) (c : Color)
    (hne : wk ≠ bk) (hna : ¬ KingAttacks wk bk) :
    ¬ KingAttacks (kbSupport wk bk c) (kbEscape wk bk c) := by
  cases c with
  | .white =>
    exact kingOrthoEscape_not_kingAttacks bk wk hne hna
  | .black =>
    exact kingOrthoEscape_not_kingAttacks wk bk hne.symm
      (mt kingAttacks_symmetric.mp hna)

theorem kbEscape_ne_lone (wk bk : Square) (c : Color) :
    kbEscape wk bk c ≠ kbLone wk bk c :=
  kingOrthoEscape_ne_self _ _

theorem kbEscape_ne_support (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    kbEscape wk bk c ≠ kbSupport wk bk c := by
  cases c with
  | .white => exact kingOrthoEscape_ne_other bk wk hna
  | .black =>
    exact kingOrthoEscape_ne_other wk bk (mt kingAttacks_symmetric.mp hna)

theorem kbEscape_ne_bishop {wk bk bs : Square} {c : Color}
    (hatt : BishopAttacks bs (kbLone wk bk c)) :
    kbEscape wk bk c ≠ bs := by
  intro heq
  have hcol : (kbEscape wk bk c).color = (kbLone wk bk c).color.other :=
    orthoAdj_color (kbEscape_ortho wk bk c)
  rw [heq] at hcol
  have hsame : bs.color = (kbLone wk bk c).color :=
    bishopAttacks_same_color hatt
  rw [hsame] at hcol
  exact Color.other_ne _ hcol.symm

theorem kbEscape_ne_wk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    kbEscape wk bk c ≠ wk := by
  cases c with
  | .white => exact kbEscape_ne_support wk bk .white hna
  | .black => exact kbEscape_ne_lone wk bk .black

theorem kbEscape_ne_bk (wk bk : Square) (c : Color)
    (hna : ¬ KingAttacks wk bk) :
    kbEscape wk bk c ≠ bk := by
  cases c with
  | .white => exact kbEscape_ne_lone wk bk .white
  | .black => exact kbEscape_ne_support wk bk .black hna

theorem kingBishop_escape_src {p : Position} {wk bk bs : Square} {c : Color}
    (hwk_bk : wk ≠ bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (ht : p.toMove = c.other) :
    p.board (kbLone wk bk c) = some { color := p.toMove, kind := .king } := by
  rw [hboard, ht]
  cases c with
  | .white =>
    simpa [kbLone] using Board.kingsBishopBoard_black wk bk bs Color.white hwk_bk
  | .black =>
    simpa [kbLone] using Board.kingsBishopBoard_white wk bk bs Color.black

theorem kingBishop_escape_dst {p : Position} {wk bk bs : Square} {c : Color}
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (hattB : BishopAttacks bs (kbLone wk bk c)) :
    p.board (kbEscape wk bk c) = none := by
  rw [hboard]
  exact Board.kingsBishopBoard_other wk bk bs (kbEscape wk bk c) c
    (kbEscape_ne_wk wk bk c hna)
    (kbEscape_ne_bk wk bk c hna)
    (kbEscape_ne_bishop hattB)

theorem kingBishop_play_escape_board_white {p : Position} {wk bk bs : Square}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs .white)
    (ht : p.toMove = .black)
    (hattB : BishopAttacks bs bk)
    (hsrc : m.src = bk)
    (hdst : m.dst = kbEscape wk bk .white)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .black = none)
    (hsrcP : p.board m.src = some { color := .black, kind := .king }) :
    (p.play m).board =
      Board.kingsBishopBoard wk (kbEscape wk bk .white) bs .white := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .black) hside hpromo
  have htne_wk := kbEscape_ne_wk wk bk .white hna
  have htne_bk := kbEscape_ne_bk wk bk .white hna
  have htne_bs : kbEscape wk bk .white ≠ bs :=
    kbEscape_ne_bishop (wk := wk) (bk := bk) (c := Color.white)
      (show BishopAttacks bs (kbLone wk bk Color.white) from hattB)
  have hrel := Board.relocate_kingsBishopBoard_black wk bk bs (kbEscape wk bk .white)
    Color.white hwk_bk hwk_bs hbk_bs htne_wk htne_bk htne_bs
  calc (p.play m).board
      = p.boardAfter m { color := .black, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
    _ = (Board.kingsBishopBoard wk bk bs .white).relocate
          bk (kbEscape wk bk .white) { color := .black, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsBishopBoard wk (kbEscape wk bk .white) bs .white := hrel

theorem kingBishop_play_escape_board_black {p : Position} {wk bk bs : Square}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs .black)
    (ht : p.toMove = .white)
    (hattB : BishopAttacks bs wk)
    (hsrc : m.src = wk)
    (hdst : m.dst = kbEscape wk bk .black)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? .white = none)
    (hsrcP : p.board m.src = some { color := .white, kind := .king }) :
    (p.play m).board =
      Board.kingsBishopBoard (kbEscape wk bk .black) bk bs .black := by
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m (c := .white) hside hpromo
  have htne_wk := kbEscape_ne_wk wk bk .black hna
  have htne_bk := kbEscape_ne_bk wk bk .black hna
  have htne_bs : kbEscape wk bk .black ≠ bs :=
    kbEscape_ne_bishop (wk := wk) (bk := bk) (c := Color.black)
      (show BishopAttacks bs (kbLone wk bk Color.black) from hattB)
  have hrel := Board.relocate_kingsBishopBoard_white wk bk bs (kbEscape wk bk .black)
    Color.black hwk_bk hwk_bs hbk_bs htne_wk htne_bk htne_bs
  calc (p.play m).board
      = p.boardAfter m { color := .white, kind := .king } := by
        rw [hplay, ht]
    _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
    _ = (Board.kingsBishopBoard wk bk bs .black).relocate
          wk (kbEscape wk bk .black) { color := .white, kind := .king } := by
        rw [hboard, hsrc, hdst]
    _ = Board.kingsBishopBoard (kbEscape wk bk .black) bk bs .black := hrel

theorem kingBishop_escape_safe {p : Position} {wk bk bs : Square} {c : Color}
    {m : Move}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (ht : p.toMove = c.other)
    (hattB : BishopAttacks bs (kbLone wk bk c))
    (hsrc : m.src = kbLone wk bk c)
    (hdst : m.dst = kbEscape wk bk c)
    (hpromo : m.promotion = none)
    (hside : m.castlingSide? p.toMove = none)
    (hsrcP : p.board m.src = some { color := p.toMove, kind := .king }) :
    (p.play m).board.kingIsAttacked p.toMove = false := by
  have ho := kbEscape_ortho wk bk c
  have hnk := kbEscape_not_kingAttacks wk bk c hwk_bk hna
  have hnbish : ¬ BishopAttacks bs (kbEscape wk bk c) :=
    orthoAdj_not_bishopAttacks ho hattB
  cases c with
  | .white =>
    have hnb := kingBishop_play_escape_board_white hwk_bk hwk_bs hbk_bs hna
      hboard ht hattB hsrc hdst hpromo (by simpa [ht] using hside)
      (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_wk := kbEscape_ne_wk wk bk .white hna
    have hiff := Board.kingsBishopBoard_kingIsAttacked_black wk
      (kbEscape wk bk .white) bs .white htne_wk.symm hwk_bs
      (kbEscape_ne_bishop (wk := wk) (bk := bk) (c := Color.white) hattB)
    cases hAtt :
      (Board.kingsBishopBoard wk (kbEscape wk bk .white) bs .white).kingIsAttacked
        .black
    · simpa [Color.other] using hAtt
    · rcases hiff.mp hAtt with hk | ⟨_, hB, _⟩
      · exact (hnk hk).elim
      · exact (hnbish hB).elim
  | .black =>
    have hnb := kingBishop_play_escape_board_black hwk_bk hwk_bs hbk_bs hna
      hboard ht hattB hsrc hdst hpromo (by simpa [ht] using hside)
      (by simpa [ht] using hsrcP)
    rw [hnb, ht]
    have htne_bs : kbEscape wk bk .black ≠ bs :=
      kbEscape_ne_bishop (wk := wk) (bk := bk) (c := Color.black) hattB
    have hiff := Board.kingsBishopBoard_kingIsAttacked_white
      (kbEscape wk bk .black) bk bs .black
      (kbEscape_ne_bk wk bk .black hna) htne_bs hbk_bs
    cases hAtt :
      (Board.kingsBishopBoard (kbEscape wk bk .black) bk bs .black).kingIsAttacked
        .white
    · simpa [Color.other] using hAtt
    · rcases hiff.mp hAtt with hk | ⟨_, hB, _⟩
      · exact (hnk hk).elim
      · exact (hnbish hB).elim

theorem kingBishop_escape_isLegalMove {p : Position} {wk bk bs : Square} {c : Color}
    (hwk_bk : wk ≠ bk) (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (ht : p.toMove = c.other)
    (hchk : p.inCheck = true) :
    isLegalMove p (Move.std (kbLone wk bk c) (kbEscape wk bk c)) = true := by
  let m := Move.std (kbLone wk bk c) (kbEscape wk bk c)
  have hattB := IsKingAndBishop.inCheck_bishopAttacks
    hwk_bk hwk_bs hbk_bs hna hboard ht hchk
  have hsrcP : p.board (kbLone wk bk c) =
      some { color := p.toMove, kind := .king } :=
    kingBishop_escape_src hwk_bk hboard ht
  have hdstNone := kingBishop_escape_dst hna hboard hattB
  have ho := kbEscape_ortho wk bk c
  have hside := castlingSide_none_of_ortho p.toMove ho
  have hgeo : p.board.attacks (kbLone wk bk c) (kbEscape wk bk c) = true := by
    have hsk : Board.kingsBishopBoard wk bk bs c (kbLone wk bk c) =
        some { color := p.toMove, kind := .king } := by
      simpa [hboard] using hsrcP
    rw [hboard, Board.attacks_king hsk]
    exact decide_eq_true (orthoAdj_kingAttacks ho)
  have hsrcP' : p.board m.src = some { color := p.toMove, kind := .king } := hsrcP
  have hsafe := kingBishop_escape_safe hwk_bk hwk_bs hbk_bs hna hboard ht hattB
    (rfl : m.src = kbLone wk bk c) (rfl : m.dst = kbEscape wk bk c) rfl hside hsrcP'
  unfold isLegalMove
  rw [hsrcP']
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := m) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std (kbLone wk bk c) (kbEscape wk bk c)).castlingSide?
      p.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool
    (p.board.attacks (kbLone wk bk c) (kbEscape wk bk c))
    ((Move.std (kbLone wk bk c) (kbEscape wk bk c)).promotion == none)
    ((p.play m).board.kingIsAttacked p.toMove)
    hgeo rfl hsafe

theorem IsKingAndBishop.not_inCheckmate {p : Position} (h : IsKingAndBishop p) :
    p.inCheckmate = false := by
  set_option maxRecDepth 1024 in
  obtain ⟨wk, bk, bs, c, hwk_bk, hwk_bs, hbk_bs, hna, hboard, _, _⟩ := h
  by_cases ht : p.toMove = c
  · exact not_inCheck_not_inCheckmate
      (IsKingAndBishop.bishopToMove_not_inCheck hwk_bk hwk_bs hbk_bs hna hboard ht)
  · have ht' : p.toMove = c.other := eq_other_of_ne_color ht
    have hsplit := bool_eq_false_or_true p.inCheck
    cases hsplit with
    | inl hIn => exact not_inCheck_not_inCheckmate hIn
    | inr hIn =>
      have hleg := kingBishop_escape_isLegalMove hwk_bk hwk_bs hbk_bs hna
        hboard ht' hIn
      have hmem :
          Move.std (kbLone wk bk c) (kbEscape wk bk c) ∈ p.legalMoves :=
        (mem_legalMoves p _).mpr hleg
      have hne : p.legalMoves.card ≠ 0 :=
        mt Finset.card_eq_zero.mp (Finset.ne_empty_of_mem hmem)
      unfold inCheckmate
      rw [hIn]
      simp only [Bool.true_and]
      exact beq_eq_false_iff_ne.mpr hne

theorem IsKingAndBishop.not_InCheckmate {p : Position} (h : IsKingAndBishop p) :
    ¬ InCheckmate p :=
  mt (inCheckmate_eq_true_iff p).mpr
    (Eq.trans_ne h.not_inCheckmate Bool.false_ne_true)

theorem destOk_kingsBishopBoard {p : Position} {m : Move} {wk bk bs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = bs := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsBishopBoard wk bk bs c m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsBishopBoard at hdst
    split_ifs at hdst with h1 h2 h3
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr h3

theorem kingBishop_legalMove_core {p : Position} {m : Move} {wk bk bs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = bs) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .bishop) ∧
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
    have hdstOr := destOk_kingsBishopBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsBishopBoard wk bk bs c m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .bishop := by
      have hsrc' := hsrc
      unfold Board.kingsBishopBoard at hsrc'
      split_ifs at hsrc' with _h1 _h2 _h3
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inl rfl
      · cases hsrc'; exact Or.inr rfl
    have hpawn : (piece.kind == PieceKind.pawn) = false := by
      cases hkind with
      | inl hk => simp [hk]
      | inr hb => simp [hb]
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
      | inr hb =>
        have hifs' : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
          simpa [hpawn, hb, Bool.and_eq_true, beq_iff_eq] using hifs
        exact hifs'.2
    exact ⟨hpromo, hdestOk, hdstOr, hsafe, piece, rfl, hcol', hkind, hside⟩

theorem destOk_toMove_of_dst_bishop {p : Position} {m : Move}
    {wk bk bs : Square} {c : Color}
    (hboard : p.board = Board.kingsBishopBoard wk bk bs c)
    (hwk_bs : wk ≠ bs) (hbk_bs : bk ≠ bs)
    (hdst : m.dst = bs) (hok : p.destOk m = true) :
    p.toMove = c.other := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem piece_eq_of_eq_some {p : Position} {s : Square} {piece q : Piece}
    (h1 : p.board s = some piece) (h2 : p.board s = some q) : piece = q :=
  Option.some.inj (h1.symm.trans h2)

theorem some_king_ne_bishop {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .bishop }) : False := by
  simp at h

theorem IsKingAndBishop.of_play {p : Position} {m : Move}
    (h : IsKingAndBishop p) (hm : LegalMove p m) :
    IsKingAndBishop (p.play m) ∨ IsTwoKings (p.play m) := by
  obtain ⟨wk, bk, bs, c, hwk_bk, hwk_bs, hbk_bs, hna, hboard, hcstl, _hep⟩ := h
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, piece, hsrcP, hcol', hkind, hside⟩ :=
    kingBishop_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = bs :=
    (Board.kingsBishopBoard_isSome wk bk bs m.src c).mp (by
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
    | inr hb =>
      have hpiece : piece = { color := p.toMove, kind := .bishop } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_bishop p m (c := p.toMove) hpromo, hcstl]
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
    | inr hb =>
      have hpiece : piece = { color := p.toMove, kind := .bishop } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .bishop }
              (p.boardAfter m { color := p.toMove, kind := .bishop }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_bishop _ _ _
  rcases hdstOr with hdstNone | hdstBs
  · -- Empty destination: the three pieces remain.
    have hdstW : m.dst ≠ wk := by
      intro heq; rw [heq, hboard, Board.kingsBishopBoard_white] at hdstNone; cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsBishopBoard_black wk bk bs c hwk_bk] at hdstNone
      cases hdstNone
    have hdstS : m.dst ≠ bs := by
      intro heq
      rw [heq, hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs] at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · -- White king moves.
      have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsBishopBoard_white])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsBishopBoard_white wk bk bs m.dst c
        hwk_bk hwk_bs hbk_bs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsBishopBoard m.dst bk bs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsBishopBoard wk bk bs c).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsBishopBoard m.dst bk bs c := hrel
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by simpa [ht] using hsafe
        have hiff := Board.kingsBishopBoard_kingIsAttacked_white m.dst bk bs c
          hdstB hdstS hbk_bs
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨m.dst, bk, bs, c, hdstB, hdstS, hbk_bs, hna', hboard', hcast', hep'⟩
    · -- Black king moves.
      have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopBoard_black wk bk bs c hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsBishopBoard_black wk bk bs m.dst c
        hwk_bk hwk_bs hbk_bs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsBishopBoard wk m.dst bs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsBishopBoard wk bk bs c).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsBishopBoard wk m.dst bs c := hrel
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by simpa [ht] using hsafe
        have hiff := Board.kingsBishopBoard_kingIsAttacked_black wk m.dst bs c
          hdstW.symm hwk_bs hdstS
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨wk, m.dst, bs, c, hdstW.symm, hwk_bs, hdstS, hna', hboard', hcast', hep'⟩
    · -- Bishop moves.
      have hpiece : piece = { color := c, kind := .bishop } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcS, hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs])
      have ht : p.toMove = c := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_bishop p m (c := c) hpromo
      have hrel := Board.relocate_kingsBishopBoard_bishop wk bk bs m.dst c
        hwk_bk hwk_bs hbk_bs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsBishopBoard wk bk m.dst c := by
        calc (p.play m).board
            = p.boardAfter m { color := c, kind := .bishop } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := c, kind := .bishop } := hba
          _ = (Board.kingsBishopBoard wk bk bs c).relocate bs m.dst
                { color := c, kind := .bishop } := by
              rw [hboard, hsrcS]
          _ = Board.kingsBishopBoard wk bk m.dst c := hrel
      exact Or.inl ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep'⟩
  · -- Capture on the bishop's square: two kings remain.
    have hbish : p.board bs = some { color := c, kind := .bishop } := by
      rw [hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs]
    have ht : p.toMove = c.other :=
      destOk_toMove_of_dst_bishop hboard hwk_bs hbk_bs hdstBs hdestOk
    have hsrcNeBs : m.src ≠ bs := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hbish] at hsrcP'
      have hpc : c = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      exact Color.other_ne c hpc.symm
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · -- White king captures the black bishop.
      have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsBishopBoard_white])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.black := by
        have : c.other = Color.white := ht.symm.trans htW
        cases c
        · simp [Color.other] at this
        · rfl
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [htW] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_bishop_white wk bk bs hwk_bk hwk_bs hbk_bs
      have hboard' : (p.play m).board = Board.kingsBoard bs bk := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsBishopBoard wk bk bs .black).relocate wk bs
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstBs, hc]
          _ = Board.kingsBoard bs bk := hrel
      have hna' : ¬ KingAttacks bs bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [htW] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_white bs bk hbk_bs.symm] at hsafe'
        exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
      exact Or.inr ⟨bs, bk, hbk_bs.symm, hna', hboard', hcast', hep'⟩
    · -- Black king captures the white bishop.
      have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsBishopBoard_black wk bk bs c hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.white := by
        have : c.other = Color.black := ht.symm.trans htB
        cases c
        · rfl
        · simp [Color.other] at this
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [htB] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_bishop_black wk bk bs hwk_bk hwk_bs hbk_bs
      have hboard' : (p.play m).board = Board.kingsBoard wk bs := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsBishopBoard wk bk bs .white).relocate bk bs
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstBs, hc]
          _ = Board.kingsBoard wk bs := hrel
      have hna' : ¬ KingAttacks wk bs := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [htB] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_black wk bs hwk_bs] at hsafe'
        exact of_decide_eq_false hsafe'
      exact Or.inr ⟨wk, bs, hwk_bs, hna', hboard', hcast', hep'⟩
    · exact (hsrcNeBs hsrcS).elim

theorem IsKingAndBishop.of_reachable {p q : Position}
    (h : IsKingAndBishop p) (hr : Reachable p q) :
    IsKingAndBishop q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    cases ih with
    | inl hkb => exact hkb.of_play hleg
    | inr htk => exact Or.inr (htk.of_play hleg)

/-- A valid position with exactly three occupied squares, one of them a
bishop, holds only the two kings and that bishop, with the kings not
adjacent. -/
theorem isKingAndBishop_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hbish : ∃ s c, p.board s = some { color := c, kind := .bishop }) :
    IsKingAndBishop p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨bs, c, hbs⟩ := hbish
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_bs : wk ≠ bs := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hbs)
  have hbk_bs : bk ≠ bs := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_bishop (hking.symm.trans hbs)
  have hoccEq : p.board.occupied = {wk, bk, bs} := by
    have hsub : ({wk, bk, bs} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hbs]
    have hcard : ({wk, bk, bs} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_bs]
      · simp [hwk_bk, hwk_bs]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsBishopBoard wk bk bs c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsBishopBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsBishopBoard_black wk bk bs c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = bs
        · rw [hs, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs]
          exact hbs
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsBishopBoard_other wk bk bs s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | .white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsBishopBoard_kingIsAttacked_black wk bk bs c
          hwk_bk hwk_bs hbk_bs).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | .black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsBishopBoard_kingIsAttacked_white wk bk bs c
          hwk_bk hwk_bs hbk_bs).mpr (Or.inl (kingAttacks_symmetric.mp hk))
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
    · rw [hsq, hboard, Board.kingsBishopBoard_white] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsBishopBoard_black wk bk bs c hwk_bk] at hrook
      exact some_king_ne_rook hrook
    · rw [hsq, hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs] at hrook
      exact some_bishop_ne_rook hrook
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
      · rw [hsq, hboard, Board.kingsBishopBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsBishopBoard_black wk bk bs c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsBishopBoard_bishop wk bk bs c hwk_bs hbk_bs] at hpawn
        cases some_bishop_ne_pawn hpawn
  exact ⟨wk, bk, bs, c, hwk_bk, hwk_bs, hbk_bs, hna, hboard, hc, he⟩

theorem not_inCheckmate_of_kb_or_tk {q : Position}
    (h : IsKingAndBishop q ∨ IsTwoKings q) : q.inCheckmate = false := by
  cases h with
  | inl hkb => exact hkb.not_inCheckmate
  | inr htk => exact htk.not_inCheckmate

theorem not_InCheckmate_of_kb_or_tk {q : Position}
    (h : IsKingAndBishop q ∨ IsTwoKings q) : ¬ InCheckmate q := by
  cases h with
  | inl hkb => exact hkb.not_InCheckmate
  | inr htk => exact htk.not_InCheckmate

/-- A valid king-and-bishop versus king position is never checkmate. -/
theorem kingBishop_not_inCheckmate {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hbish : ∃ s c, p.board s = some { color := c, kind := .bishop }) :
    p.inCheckmate = false :=
  (isKingAndBishop_of_valid hv hocc hbish).not_inCheckmate

/-- From a valid position with only two kings and one bishop, every
legally reachable position is still not checkmate. -/
theorem kingBishop_reachable_not_inCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hbish : ∃ s c, p.board s = some { color := c, kind := .bishop })
    (hr : Reachable p q) : q.inCheckmate = false :=
  not_inCheckmate_of_kb_or_tk
    (IsKingAndBishop.of_reachable (isKingAndBishop_of_valid hv hocc hbish) hr)

/-- From a valid position with only two kings and one bishop, no
sequence of legal moves produces checkmate. -/
theorem kingBishop_legalSeq_not_inCheckmate {p : Position} {ms : List Move}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hbish : ∃ s c, p.board s = some { color := c, kind := .bishop })
    (hms : LegalSeq p ms) :
    (playSeq p ms).inCheckmate = false :=
  kingBishop_reachable_not_inCheckmate hv hocc hbish (legalSeq_reachable hms)

theorem kingBishop_reachable_not_InCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 3)
    (hbish : ∃ s c, p.board s = some { color := c, kind := .bishop })
    (hr : Reachable p q) : ¬ InCheckmate q :=
  not_InCheckmate_of_kb_or_tk
    (IsKingAndBishop.of_reachable (isKingAndBishop_of_valid hv hocc hbish) hr)

/-! ### Example: kings on `e1` and `e8`, bishop on `c3` -/

/-- White king on `e1`, black king on `e8`, black bishop on `c3`, White
to move. -/
def kingAndBishop : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.c3 then some { color := .black, kind := .bishop }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingAndBishop_isValid : isValid kingAndBishop = true := by
  native_decide

theorem kingAndBishop_occupied_card : kingAndBishop.board.occupied.card = 3 := by
  native_decide

theorem kingAndBishop_has_bishop :
    ∃ s c, kingAndBishop.board s = some { color := c, kind := .bishop } :=
  ⟨Square.c3, Color.black, by native_decide⟩

theorem kingAndBishop_not_inCheckmate : kingAndBishop.inCheckmate = false :=
  kingBishop_not_inCheckmate
    ((isValid_eq_true_iff kingAndBishop).mp kingAndBishop_isValid)
    kingAndBishop_occupied_card
    kingAndBishop_has_bishop

/-- White's `e1–e2` is a legal flight from the bishop check. -/
theorem kingAndBishop_e1e2_legal :
    isLegalMove kingAndBishop (Move.std Square.e1 Square.e2) = true := by
  native_decide

/-- After `e1–e2`, the position is still not checkmate. -/
theorem kingAndBishop_play_e1e2_not_inCheckmate :
    (kingAndBishop.play (Move.std Square.e1 Square.e2)).inCheckmate = false := by
  native_decide

end Position

end Chess
