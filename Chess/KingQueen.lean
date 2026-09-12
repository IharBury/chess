import Chess.KingRook

/-!
# King and queen versus king

A valid position whose board holds only the two kings and one queen is
king-and-queen versus king. Unlike king versus king, or king-and-bishop
versus king, checkmate is possible: the classic picture is the lone king
on the edge, the supporting king two squares away, and the queen checking
from the same rank or file (or delivering the known `h7` mate).

Checkmate is not *always* reachable. If the lone king is to move in
stalemate, or its only legal move is to capture an unprotected queen, the
position is dead: every continuation is either that same dead position or
a two-king position, from which checkmate is unreachable. When the queen
side is to move they are never in check (the only enemy piece is the
lone king, and adjacent kings are illegal), so they always have a legal
queen move and the position is not dead.

This module shows that from every other legal king-and-queen versus king
position, checkmate is reachable by cooperative play (a helpmate, not a
forced win). The two sides steer into one known mating picture:

* white king on `g6`, black king on `h8` or `g8`,
* white queen on the eighth rank (typically `a8`) or on `h7`,
* Black to move, in check, with no flight.

A potential `KQState.mu` measures the distance of the three pieces from
that picture (a route for the black king that avoids the white king's
neighborhood, a penalty for parking the queen on `a1` where it checks
`h8` along the long diagonal, and a bonus for being in check). The main
theorem shows every legal state is checkmate, is dead, or reaches by a
short legal sequence a non-dead state of strictly smaller potential.
Strong induction on the potential gives `CheckmateReachable` for every
non-dead state.

The exhaustive check is the Boolean `KQState.checkAll`, verified by
`native_decide`. It examines each of the `2 · 64³` three-piece
placements once; it is not a search for mate. Captures of the queen are
excluded from the policy: they leave two kings.

States are stored in a *white-queen frame*: White owns the queen. A
position in which Black owns the queen is reduced by a 180° rotation and
a color swap. `kingQueenCheckmateReachable` decides `CheckmateReachable`
for a valid king-and-queen versus king position, and `kingQueenMatingLine`
produces a concrete mating sequence (or `[]` when the position is dead
or not of this material).
-/

namespace Chess


namespace Board

/-- White king on `wk`, black king on `bk`, and a queen of color `c` on
`qs`. -/
def kingsQueenBoard (wk bk qs : Square) (c : Color) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = qs then some { color := c, kind := .queen }
  else none

theorem kingsQueenBoard_white (wk bk qs : Square) (c : Color) :
    kingsQueenBoard wk bk qs c wk = some { color := .white, kind := .king } := by
  simp [kingsQueenBoard]

theorem kingsQueenBoard_black (wk bk qs : Square) (c : Color) (h : wk ≠ bk) :
    kingsQueenBoard wk bk qs c bk = some { color := .black, kind := .king } := by
  simp [kingsQueenBoard, h.symm]

theorem kingsQueenBoard_queen (wk bk qs : Square) (c : Color)
    (hw : wk ≠ qs) (hb : bk ≠ qs) :
    kingsQueenBoard wk bk qs c qs = some { color := c, kind := .queen } := by
  simp [kingsQueenBoard, hw.symm, hb.symm]

theorem kingsQueenBoard_other (wk bk qs s : Square) (c : Color)
    (hw : s ≠ wk) (hb : s ≠ bk) (hqs : s ≠ qs) :
    kingsQueenBoard wk bk qs c s = none := by
  simp [kingsQueenBoard, hw, hb, hqs]

theorem kingsQueenBoard_eq_white_king {wk bk qs s : Square} {c : Color}
    (h : kingsQueenBoard wk bk qs c s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsQueenBoard at h
  split_ifs at h <;> simp_all

theorem kingsQueenBoard_eq_black_king {wk bk qs s : Square} {c : Color}
    (h : kingsQueenBoard wk bk qs c s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsQueenBoard at h
  split_ifs at h <;> simp_all

theorem kingsQueenBoard_eq_queen {wk bk qs s : Square} {c : Color}
    (h : kingsQueenBoard wk bk qs c s = some { color := c, kind := .queen }) :
    s = qs := by
  unfold kingsQueenBoard at h
  split_ifs at h <;> simp_all

theorem kingsQueenBoard_isSome (wk bk qs s : Square) (c : Color) :
    ((kingsQueenBoard wk bk qs c) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = qs := by
  unfold kingsQueenBoard
  split_ifs <;> simp_all

theorem attacks_queen_iff {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .queen }) :
    b.attacks s t = true ↔
      QueenAttacks s t ∧
        ¬ ∃ u : Square, Between s t u ∧ (b u).isSome = true := by
  unfold attacks
  rw [h]
  simp only [PieceKind.queen_isSlider, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not]

theorem kingsQueenBoard_queen_blocked {wk bk qs t : Square} {c : Color} :
    (∃ u : Square, Between qs t u ∧
        ((kingsQueenBoard wk bk qs c) u).isSome = true) ↔
      Between qs t wk ∨ Between qs t bk := by
  constructor
  · intro ⟨u, hB, hocc⟩
    have hu : u = wk ∨ u = bk ∨ u = qs :=
      (kingsQueenBoard_isSome wk bk qs u c).mp hocc
    rcases hu with hu | hu | hu
    · subst u; exact Or.inl hB
    · subst u; exact Or.inr hB
    · subst u
      exact (hB.1 rfl).elim
  · intro h
    cases h with
    | inl hB =>
      exact ⟨wk, hB, (kingsQueenBoard_isSome wk bk qs wk c).mpr (Or.inl rfl)⟩
    | inr hB =>
      exact ⟨bk, hB, (kingsQueenBoard_isSome wk bk qs bk c).mpr (Or.inr (Or.inl rfl))⟩

theorem kingsQueenBoard_attacks_queen_iff {wk bk qs t : Square} {c : Color}
    (hw : wk ≠ qs) (hb : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).attacks qs t = true ↔
      QueenAttacks qs t ∧ ¬ Between qs t wk ∧ ¬ Between qs t bk := by
  rw [attacks_queen_iff (kingsQueenBoard_queen wk bk qs c hw hb),
    kingsQueenBoard_queen_blocked]
  tauto

theorem kingsQueenBoard_occupiedBy_white (wk bk qs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_qs : wk ≠ qs) (_hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).occupiedBy .white =
      match c with
      | .white => {wk, qs}
      | .black => {wk} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsQueenBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsQueenBoard
    split_ifs <;> simp_all

theorem kingsQueenBoard_occupiedBy_black (wk bk qs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_qs : wk ≠ qs) (_hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).occupiedBy .black =
      match c with
      | .white => {bk}
      | .black => {bk, qs} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsQueenBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsQueenBoard
    split_ifs <;> simp_all

theorem kingsQueenBoard_kingSquares_white (wk bk qs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_qs : wk ≠ qs) (_hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsQueenBoard
  split_ifs <;> simp_all

theorem kingsQueenBoard_kingSquares_black (wk bk qs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_qs : wk ≠ qs) (_hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsQueenBoard
  split_ifs <;> simp_all

theorem kingsQueenBoard_occupied (wk bk qs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_qs : wk ≠ qs) (_hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).occupied = {wk, bk, qs} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsQueenBoard
  split_ifs <;> simp_all

theorem kingsQueenBoard_black_piece {wk bk qs s : Square} {c : Color}
    (h : (kingsQueenBoard wk bk qs c s).map (·.color) = some .black) :
    s = bk ∨ (c = .black ∧ s = qs) := by
  unfold kingsQueenBoard at h
  split_ifs at h <;> simp_all

theorem kingsQueenBoard_white_piece {wk bk qs s : Square} {c : Color}
    (h : (kingsQueenBoard wk bk qs c s).map (·.color) = some .white) :
    s = wk ∨ (c = .white ∧ s = qs) := by
  unfold kingsQueenBoard at h
  split_ifs at h <;> simp_all

theorem kingsQueenBoard_kingIsAttacked_white (wk bk qs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_qs : wk ≠ qs) (hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨
        (c = .black ∧ QueenAttacks qs wk ∧ ¬ Between qs wk bk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsQueenBoard_kingSquares_white wk bk qs c hwk_bk hwk_qs hbk_qs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsQueenBoard_black_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsQueenBoard_black wk bk qs c hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsQueenBoard_attacks_queen_iff (t := wk) (c := Color.black)
        hwk_qs hbk_qs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.2⟩
  · intro h
    rcases h with hk | ⟨hc, hR, hnb⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsQueenBoard_black wk bk qs c hwk_bk]
      · rw [attacks_king (kingsQueenBoard_black wk bk qs c hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨qs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsQueenBoard_queen wk bk qs Color.black hwk_qs hbk_qs]
      · subst hc
        rw [kingsQueenBoard_attacks_queen_iff (t := wk) (c := Color.black)
          hwk_qs hbk_qs]
        exact ⟨hR, fun hBet => (hBet.2.1 rfl).elim, hnb⟩

theorem kingsQueenBoard_kingIsAttacked_black (wk bk qs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_qs : wk ≠ qs) (hbk_qs : bk ≠ qs) :
    (kingsQueenBoard wk bk qs c).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨
        (c = .white ∧ QueenAttacks qs bk ∧ ¬ Between qs bk wk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsQueenBoard_kingSquares_black wk bk qs c hwk_bk hwk_qs hbk_qs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsQueenBoard_white_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsQueenBoard_white wk bk qs c)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsQueenBoard_attacks_queen_iff (t := bk) (c := Color.white)
        hwk_qs hbk_qs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.1⟩
  · intro h
    rcases h with hk | ⟨hc, hR, hnb⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsQueenBoard_white]
      · rw [attacks_king (kingsQueenBoard_white wk bk qs c)]
        exact decide_eq_true hk
    · refine ⟨qs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsQueenBoard_queen wk bk qs Color.white hwk_qs hbk_qs]
      · subst hc
        rw [kingsQueenBoard_attacks_queen_iff (t := bk) (c := Color.white)
          hwk_qs hbk_qs]
        exact ⟨hR, hnb, fun hBet => (hBet.2.1 rfl).elim⟩

theorem relocate_kingsQueenBoard_white (wk bk qs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ qs) (_hbr : bk ≠ qs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ qs) :
    (kingsQueenBoard wk bk qs c).relocate wk dst { color := .white, kind := .king } =
      kingsQueenBoard dst bk qs c := by
  funext s
  unfold relocate kingsQueenBoard
  split_ifs <;> simp_all

theorem relocate_kingsQueenBoard_black (wk bk qs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ qs) (_hbr : bk ≠ qs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ qs) :
    (kingsQueenBoard wk bk qs c).relocate bk dst { color := .black, kind := .king } =
      kingsQueenBoard wk dst qs c := by
  funext s
  unfold relocate kingsQueenBoard
  split_ifs <;> simp_all

theorem relocate_kingsQueenBoard_queen (wk bk qs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ qs) (_hbr : bk ≠ qs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ qs) :
    (kingsQueenBoard wk bk qs c).relocate qs dst { color := c, kind := .queen } =
      kingsQueenBoard wk bk dst c := by
  funext s
  unfold relocate kingsQueenBoard
  split_ifs <;> simp_all

theorem relocate_capture_queen_black (wk bk qs : Square)
    (_hne : wk ≠ bk) (_hwr : wk ≠ qs) (_hbr : bk ≠ qs) :
    (kingsQueenBoard wk bk qs .white).relocate bk qs
      { color := .black, kind := .king } =
      kingsBoard wk qs := by
  funext s
  unfold relocate kingsQueenBoard kingsBoard
  split_ifs <;> simp_all

theorem relocate_capture_queen_white (wk bk qs : Square)
    (_hne : wk ≠ bk) (_hwr : wk ≠ qs) (_hbr : bk ≠ qs) :
    (kingsQueenBoard wk bk qs .black).relocate wk qs
      { color := .white, kind := .king } =
      kingsBoard qs bk := by
  funext s
  unfold relocate kingsQueenBoard kingsBoard
  split_ifs <;> simp_all

theorem rot180_kingsQueenBoard_white (wk bk qs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) :
    (kingsQueenBoard wk bk qs .white).rot180 =
      kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 .black := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_qs : wk.rot180 ≠ qs.rot180 := mt rot180_injective h2
  have hbk_qs : bk.rot180 ≠ qs.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsQueenBoard_white wk bk qs Color.white]
    change some { color := Color.black, kind := .king } =
      kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.black wk.rot180
    rw [kingsQueenBoard_black bk.rot180 wk.rot180 qs.rot180 Color.black hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsQueenBoard_black wk bk qs Color.white h1]
      change some { color := Color.white, kind := .king } =
        kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.black bk.rot180
      rw [kingsQueenBoard_white bk.rot180 wk.rot180 qs.rot180 Color.black]
    · by_cases hR : s.rot180 = qs
      · have hs : s = qs.rot180 := rot180_eq_iff.mp hR
        rw [hR, hs, kingsQueenBoard_queen wk bk qs Color.white h2 h3]
        change some { color := Color.black, kind := .queen } =
          kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.black qs.rot180
        rw [kingsQueenBoard_queen bk.rot180 wk.rot180 qs.rot180 Color.black hbk_qs hwk_qs]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsR : s ≠ qs.rot180 := fun h => hR (rot180_eq_iff.mpr h)
        rw [kingsQueenBoard_other wk bk qs s.rot180 Color.white hA hB hR]
        change none = kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.black s
        rw [kingsQueenBoard_other bk.rot180 wk.rot180 qs.rot180 s Color.black hsB hsW hsR]

theorem rot180_kingsQueenBoard_black (wk bk qs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) :
    (kingsQueenBoard wk bk qs .black).rot180 =
      kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 .white := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_qs : wk.rot180 ≠ qs.rot180 := mt rot180_injective h2
  have hbk_qs : bk.rot180 ≠ qs.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsQueenBoard_white wk bk qs Color.black]
    change some { color := Color.black, kind := .king } =
      kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.white wk.rot180
    rw [kingsQueenBoard_black bk.rot180 wk.rot180 qs.rot180 Color.white hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsQueenBoard_black wk bk qs Color.black h1]
      change some { color := Color.white, kind := .king } =
        kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.white bk.rot180
      rw [kingsQueenBoard_white bk.rot180 wk.rot180 qs.rot180 Color.white]
    · by_cases hR : s.rot180 = qs
      · have hs : s = qs.rot180 := rot180_eq_iff.mp hR
        rw [hR, hs, kingsQueenBoard_queen wk bk qs Color.black h2 h3]
        change some { color := Color.white, kind := .queen } =
          kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.white qs.rot180
        rw [kingsQueenBoard_queen bk.rot180 wk.rot180 qs.rot180 Color.white hbk_qs hwk_qs]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsR : s ≠ qs.rot180 := fun h => hR (rot180_eq_iff.mpr h)
        rw [kingsQueenBoard_other wk bk qs s.rot180 Color.black hA hB hR]
        change none = kingsQueenBoard bk.rot180 wk.rot180 qs.rot180 Color.white s
        rw [kingsQueenBoard_other bk.rot180 wk.rot180 qs.rot180 s Color.white hsB hsW hsR]


end Board

namespace Position

/-- Board after a non-promoting queen move. -/
theorem boardAfter_queen (p : Position) (m : Move) {c : Color}
    (hpromo : m.promotion = none) :
    p.boardAfter m { color := c, kind := .queen } =
      p.board.relocate m.src m.dst { color := c, kind := .queen } := by
  unfold boardAfter
  simp [hpromo]

theorem enPassantAfter_queen (m : Move) (c : Color) (b : Board) :
    enPassantAfter m { color := c, kind := .queen } b = none := by
  unfold enPassantAfter
  simp

theorem some_queen_ne_pawn {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .queen } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

theorem some_queen_ne_king {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .queen } : Option Piece) =
      some { color := c₂, kind := .king }) : False := by
  simp at h

theorem some_king_ne_queen {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .queen }) : False := by
  simp at h

/-- `p` contains only two kings and one queen, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingAndQueen (p : Position) : Prop :=
  ∃ wk bk qs : Square, ∃ c : Color,
    wk ≠ bk ∧
      wk ≠ qs ∧
      bk ≠ qs ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsQueenBoard wk bk qs c ∧
      p.castling = ∅ ∧
      p.enPassant = none


theorem destOk_kingsQueenBoard {p : Position} {m : Move} {wk bk qs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsQueenBoard wk bk qs c)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = qs := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsQueenBoard wk bk qs c m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsQueenBoard at hdst
    split_ifs at hdst with h1 h2 h3
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr h3

theorem destOk_toMove_of_dst_queen {p : Position} {m : Move}
    {wk bk qs : Square} {c : Color}
    (hboard : p.board = Board.kingsQueenBoard wk bk qs c)
    (hwk_qs : wk ≠ qs) (hbk_qs : bk ≠ qs)
    (hdst : m.dst = qs) (hok : p.destOk m = true) :
    p.toMove = c.other := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem kingQueen_legalMove_core {p : Position} {m : Move} {wk bk qs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsQueenBoard wk bk qs c)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = qs) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      p.board.attacks m.src m.dst = true ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .queen) ∧
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
    have hdstOr := destOk_kingsQueenBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsQueenBoard wk bk qs c m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .queen := by
      have hsrc' := hsrc
      unfold Board.kingsQueenBoard at hsrc'
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
    have hgeo : p.board.attacks m.src m.dst = true ∧ m.promotion = none := by
      cases hkind with
      | inl hk =>
        have hsnone := hside hk
        simpa [hpawn, hk, hsnone, Bool.and_eq_true, beq_iff_eq] using hifs
      | inr hb =>
        simpa [hpawn, hb, Bool.and_eq_true, beq_iff_eq] using hifs
    exact ⟨hgeo.2, hdestOk, hdstOr, hsafe, hgeo.1, piece, rfl, hcol', hkind, hside⟩

end Position


/-! ## Three-piece states (white-queen frame) -/

/-- A king-and-queen versus king position by the squares of its three
pieces and the side to move. White owns the queen. -/
structure KQState where
  /-- The side to move. -/
  toMove : Color
  /-- White king (the queen's support). -/
  wk : Square
  /-- Black king (the lone king). -/
  bk : Square
  /-- White queen. -/
  qs : Square
deriving DecidableEq, Repr

/-- A move of the side to move: the white king, the black king, or the
queen goes to `dst`. Captures are not represented. -/
inductive KQMove where
  | king (dst : Square)
  | queen (dst : Square)
deriving DecidableEq, Repr

namespace KQState

/-- All 64 squares. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f => (List.finRange 8).map fun r => ⟨f, r⟩

theorem mem_allSquares (x : Square) : x ∈ allSquares := by
  rcases x with ⟨f, r⟩
  simp [allSquares, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- Index of a square in a 64-entry table. -/
def idx (q : Square) : Nat := q.file.val * 8 + q.rank.val

/-- The square `dx` files and `dy` ranks away from `k`, if on the board. -/
def shift (k : Square) (dx dy : Int) : Option Square :=
  let x := (k.file.val : Int) + dx
  let y := (k.rank.val : Int) + dy
  if h : 0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 then
    some ⟨⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩⟩
  else none

/-- The eight king steps. -/
def kingOffsets : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

/-- Squares a king on `k` can step to, by computation. -/
def kingNeighborsOf (k : Square) : List Square :=
  kingOffsets.filterMap fun p => shift k p.1 p.2

/-- Squares along a ray from `b`, nearest first. -/
def ray (b : Square) (dx dy : Int) : List Square :=
  go 1 7
where
  go (i : Int) : Nat → List Square
    | 0 => []
    | fuel + 1 =>
      match shift b (dx * i) (dy * i) with
      | some d => d :: go (i + 1) fuel
      | none => []

/-- Squares a queen on `q` can move to on an empty board, by computation. -/
def queenDestsOf (q : Square) : List Square :=
  ray q 1 0 ++ ray q (-1) 0 ++ ray q 0 1 ++ ray q 0 (-1) ++
    ray q 1 1 ++ ray q 1 (-1) ++ ray q (-1) 1 ++ ray q (-1) (-1)

/-- King steps of every square, indexed by `idx`. -/
def kingNeighborsTable : Array (List Square) := (allSquares.map kingNeighborsOf).toArray

/-- Queen destinations of every square, indexed by `idx`. -/
def queenDestsTable : Array (List Square) := (allSquares.map queenDestsOf).toArray

/-- Squares a king on `k` can step to. -/
def kingNeighbors (k : Square) : List Square := kingNeighborsTable.getD (idx k) []

/-- Squares a queen on `q` can move to on an empty board. -/
def queenDests (q : Square) : List Square := queenDestsTable.getD (idx q) []

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Chebyshev distance. -/
def cheb (x y x' y' : Nat) : Nat := max (dist x x') (dist y y')

/-- `u` lies strictly between `s` and `t` on a queen ray. -/
def queenBetween (s t u : Square) : Bool :=
  decide (Between s t u)

/-- The queen on `qs` checks the square `d`, the only possible blocker being
the white king `wk`. -/
def queenChecks (qs d wk : Square) : Bool :=
  decide (QueenAttacks qs d) && !queenBetween qs d wk

/-- The black king on `bk` is attacked by the white king `wk` or the queen
`qs`. -/
def kingAttackedBlack (wk bk qs : Square) : Bool :=
  decide (KingAttacks wk bk) || queenChecks qs bk wk

/-- The white king on `wk` is attacked by the black king `bk`. -/
def kingAttackedWhite (wk bk : Square) : Bool :=
  decide (KingAttacks wk bk)

/-- The king of `c` among `wk`, `bk`. -/
def king (s : KQState) : Color → Square
  | .white => s.wk
  | .black => s.bk

/-- The king of `c` is attacked. -/
def inCheckB (s : KQState) (c : Color) : Bool :=
  match c with
  | .white => kingAttackedWhite s.wk s.bk
  | .black => kingAttackedBlack s.wk s.bk s.qs

/-- Geometric legality of the white king step `wk → d`. Captures are
excluded. -/
def fastKingW (wk d bk qs : Square) : Bool :=
  decide (KingAttacks wk d) && d != bk && d != qs && !decide (KingAttacks bk d)

/-- Geometric legality of the black king step `bk → d`, including capture
of an unprotected queen. -/
def fastKingB (wk d bk qs : Square) : Bool :=
  decide (KingAttacks bk d) && d != wk &&
    (if d == qs then !decide (KingAttacks wk d)
      else !decide (KingAttacks wk d) && !queenChecks qs d wk)

/-- Geometric legality of the queen move `qs → d`. Captures are excluded. -/
def fastQueen (wk d bk qs : Square) : Bool :=
  decide (QueenAttacks qs d) && d != wk && d != bk &&
    !queenBetween qs d wk && !queenBetween qs d bk

/-- The state describes a legal three-piece position: distinct squares,
kings not adjacent, and the side not to move not in check. -/
def okB (s : KQState) : Bool :=
  s.wk != s.bk && s.wk != s.qs && s.bk != s.qs &&
    !decide (KingAttacks s.wk s.bk) && !s.inCheckB s.toMove.other

/-- Geometric legality of a (non-capturing) move in an `okB` state. -/
def fastLegal (s : KQState) : KQMove → Bool
  | .king d =>
    match s.toMove with
    | .white => fastKingW s.wk d s.bk s.qs
    | .black => d != s.qs && fastKingB s.wk d s.bk s.qs
  | .queen d =>
    s.toMove == .white && fastQueen s.wk d s.bk s.qs

/-- The state after a move. -/
def apply (s : KQState) : KQMove → KQState
  | .king d =>
    match s.toMove with
    | .white => { s with toMove := .black, wk := d }
    | .black => { s with toMove := .white, bk := d }
  | .queen d =>
    { s with toMove := .black, qs := d }

/-- The side to move is checkmated: Black is in check and every king
step is onto the white king, onto an attacked square, or onto the
protected queen. -/
def mateB (s : KQState) : Bool :=
  s.toMove == .black && kingAttackedBlack s.wk s.bk s.qs &&
    (kingNeighbors s.bk).all fun d =>
      d == s.wk || decide (KingAttacks s.wk d) ||
        (d != s.qs && queenChecks s.qs d s.wk)

/-- Whether some non-capturing move is geometrically legal. -/
def hasNoncaptureLegal (s : KQState) : Bool :=
  match s.toMove with
  | .white =>
    (kingNeighbors s.wk).any (fun d => fastKingW s.wk d s.bk s.qs) ||
      (queenDests s.qs).any (fun d => fastQueen s.wk d s.bk s.qs)
  | .black =>
    (kingNeighbors s.bk).any (fun d => d != s.qs && fastKingB s.wk d s.bk s.qs)

/-- The state is dead for helpmate: not checkmate, and the only legal
continuations (if any) capture the queen. -/
def deadB (s : KQState) : Bool :=
  !s.mateB && !s.hasNoncaptureLegal

/-- The chess position of the state. -/
def toPosition (s : KQState) : Position where
  board := Board.kingsQueenBoard s.wk s.bk s.qs .white
  toMove := s.toMove
  castling := ∅
  enPassant := none

/-- The chess move of a state move. -/
def move (s : KQState) : KQMove → Move
  | .king d => Move.std (s.king s.toMove) d
  | .queen d => Move.std s.qs d

/-! ### Potential -/

/-- Weighted route length for the black king to `h8` avoiding the
neighborhood of `g6`, indexed by `file * 8 + rank`. -/
def bkDistTable : Array Nat :=
  #[9, 8, 7, 7, 7, 7, 7, 7, 9, 8, 7, 6, 6, 6, 6, 6, 9, 8, 7, 6, 5, 5, 5, 5, 9, 8, 7, 6, 5, 4, 4,
    4, 9, 8, 7, 6, 5, 4, 3, 3, 9, 8, 7, 6, 8, 7, 5, 2, 9, 8, 7, 7, 10, 8, 4, 1, 9, 8, 8, 8, 11, 8,
    4, 0]

/-- Black-king route length to `h8`. -/
def bkDist (q : Square) : Nat := bkDistTable.getD (idx q) 0

/-- Penalty keeping the white king out of Black's corner. -/
def zoneW (wk : Square) : Nat :=
  if wk.file.val == 7 && wk.rank.val == 7 then 4
  else if (wk.file.val == 7 && wk.rank.val == 6) || (wk.file.val == 6 && wk.rank.val == 7) then 1
  else 0

/-- White king distance to `g6`. -/
def workWk (wk : Square) : Nat :=
  4 * cheb wk.file.val wk.rank.val 6 5 + dist wk.file.val 6 + dist wk.rank.val 5 + zoneW wk

/-- The queen is adjacent to the black king and not protected by the white
king. -/
def hangingQueen (s : KQState) : Bool :=
  decide (KingAttacks s.bk s.qs) && !decide (KingAttacks s.wk s.qs)

/-- Queen distance to the mating file/rank, with a penalty for occupying
`a1` (which checks `h8` along the long diagonal). -/
def queenWork (s : KQState) : Nat :=
  let hang := if s.hangingQueen then 8 else 0
  let x := s.qs.file.val
  let y := s.qs.rank.val
  let base :=
    if x == 0 && y == 7 then
      if (s.bk.file.val == 7 && s.bk.rank.val == 7) ||
          (s.bk.file.val == 6 && s.bk.rank.val == 7) then 0
      else 4
    else if y == 7 && x < 7 then
      if s.bk.rank.val < 7 then 4 else 1
    else if x == 0 then
      -- `a1` checks `h8` along the long diagonal; a rook there would not.
      if y == 0 then 6 else 1
    else 2
  let hfile := if x == 7 && !(s.bk.file.val == 7 && s.bk.rank.val == 7) then 3 else 0
  hang + base + hfile

/-- Black king distance to `h8`. -/
def workBk (s : KQState) : Nat :=
  let block := (if decide (KingAttacks s.bk s.qs) then 1 else 0) +
    (if decide (KingAttacks s.bk s.wk) &&
        cheb s.wk.file.val s.wk.rank.val 7 7 < cheb s.bk.file.val s.bk.rank.val 7 7 then 1
      else 0)
  4 * bkDist s.bk + dist s.bk.file.val 7 + dist s.bk.rank.val 7 + block

/-- Extra cost when the white king sits on `h8` and the black king is
cut off behind it. -/
def cornerBlock (s : KQState) : Nat :=
  if s.wk.file.val == 7 && s.wk.rank.val == 7 &&
      ((s.bk.file.val == 7 && s.bk.rank.val == 5) ||
        (s.bk.file.val == 5 && s.bk.rank.val == 7)) then 5
  else 0

/-- White's contribution to the potential. -/
def whitePart (s : KQState) : Nat := workWk s.wk + queenWork s

/-- Black's contribution to the potential. -/
def blackPart (s : KQState) : Nat := workBk s

/-- Tempo: the side that has finished its work must still move. -/
def tempo (s : KQState) (w b : Nat) : Nat :=
  match s.toMove with
  | .white => if w == 0 then 1 else 0
  | .black => if b == 0 then 1 else 0

/-- Potential without the check bonus. -/
def muBase (s : KQState) : Nat :=
  let c := s.cornerBlock
  let w := s.whitePart
  let b := s.blackPart
  2 * (w + b + c) + tempo s (w + c) (b + c)

/-- Bonus so that fleeing check lowers the potential. -/
def checkBonus (s : KQState) : Nat := if s.inCheckB s.toMove then 80 else 0

/-- Lyapunov potential of the state. -/
def mu (s : KQState) : Nat := s.muBase + s.checkBonus

/-! ### Scripted policy -/

/-- The move is legal, leads to a legal state, and does not enter a dead
position unless it mates. -/
def oneOk (s : KQState) (m : KQMove) : Bool :=
  s.fastLegal m &&
    let s1 := s.apply m
    s1.okB && (s1.mateB || !s1.deadB)

/-- The move is legal and mates or lowers the potential without entering
a dead position (`x` is the current potential). -/
def progressMove (s : KQState) (x : Nat) (m : KQMove) : Bool :=
  s.fastLegal m &&
    let s1 := s.apply m
    s1.okB && (s1.mateB || (s1.mu < x && !s1.deadB))

/-- Score of a move: `0` for mate, otherwise one more than the new potential
without the check bonus. -/
def score (s : KQState) (m : KQMove) : Nat :=
  let s1 := s.apply m
  if s1.mateB then 0 else s1.muBase + 1

/-- The legal non-dead move with the smallest score, first wins ties. -/
def bestOf (s : KQState) (ms : List KQMove) : Option KQMove :=
  let best := ms.foldl (init := (none : Option (KQMove × Nat))) fun best m =>
    if s.oneOk m then
      let sc := s.score m
      match best with
      | none => some (m, sc)
      | some (_, bsc) => if sc < bsc then some (m, sc) else best
    else best
  best.map (·.1)

/-- First legal move that does not raise the potential and does not
stalemate. -/
def waitMove (s : KQState) : Option KQMove :=
  let x := s.mu
  match s.toMove with
  | .white =>
    match (queenDests s.qs).find? fun d =>
        let m := KQMove.queen d
        s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x && !(s.apply m).deadB with
    | some d => some (.queen d)
    | none =>
      (kingNeighbors s.wk).findSome? fun d =>
        let m := KQMove.king d
        if s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x && !(s.apply m).deadB then
          some m
        else none
  | .black =>
    (kingNeighbors s.bk).findSome? fun d =>
      let m := KQMove.king d
      if d != s.qs && s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x &&
          !(s.apply m).deadB then
        some m
      else none

/-- Unhang the queen if it is hanging and White is to move. -/
def unhangQueen (s : KQState) : Option KQMove :=
  if s.toMove == .white && s.hangingQueen then
    let x := s.mu
    match (queenDests s.qs).find? fun d => s.progressMove x (.queen d) with
    | some d => some (.queen d)
    | none =>
      (queenDests s.qs).findSome? fun d =>
        if s.fastLegal (.queen d) && (s.apply (.queen d)).okB &&
            !decide (KingAttacks s.bk d) && !(s.apply (.queen d)).deadB then
          some (.queen d)
        else none
  else none

/-- The queen checks `h8` while Black is not yet in the corner, cutting
off the engineered route. -/
def cutsH8 (s : KQState) : Bool :=
  let cornered :=
    (s.bk.file.val == 7 && s.bk.rank.val == 7) ||
      (s.bk.file.val == 6 && s.bk.rank.val == 7)
  !cornered && queenChecks s.qs Square.h8 s.wk

/-- Move the queen off the `h8` check so the black king can enter the
corner. -/
def uncutQueen (s : KQState) : Option KQMove :=
  if s.toMove == .white && s.cutsH8 then
    let x := s.mu
    match (queenDests s.qs).find? fun d =>
        s.progressMove x (.queen d) && !queenChecks d Square.h8 s.wk with
    | some d => some (.queen d)
    | none =>
      (queenDests s.qs).findSome? fun d =>
        if s.fastLegal (.queen d) && (s.apply (.queen d)).okB &&
            !(s.apply (.queen d)).deadB &&
            !queenChecks d Square.h8 (s.apply (.queen d)).wk then
          some (.queen d)
        else none
  else none

/-- The scripted move. In check: the king step with the best score.
Otherwise the king or queen move that mates or lowers the potential
(Black chooses the progress move of least remaining potential), else a
waiting move, else the legal move with the best score. White unhangs or
uncuts `h8` first. -/
def scriptMove (s : KQState) : Option KQMove :=
  match s.unhangQueen with
  | some m => some m
  | none =>
    match s.uncutQueen with
    | some m => some m
    | none =>
      let x := s.mu
      match s.toMove with
      | .black =>
        let kingMoves := (kingNeighbors s.bk).filterMap fun d =>
          if d == s.qs then none else some (KQMove.king d)
        if s.inCheckB .black then s.bestOf kingMoves
        else
          match s.bestOf (kingMoves.filter fun m => s.progressMove x m) with
          | some m => some m
          | none =>
            match s.waitMove with
            | some m => some m
            | none => s.bestOf kingMoves
      | .white =>
        let kingMoves := (kingNeighbors s.wk).map KQMove.king
        let queenMoves := (queenDests s.qs).map KQMove.queen
        if s.inCheckB .white then s.bestOf kingMoves
        else
          match (kingNeighbors s.wk).find? fun d => s.progressMove x (.king d) with
          | some d => some (.king d)
          | none =>
            match (queenDests s.qs).find? fun d => s.progressMove x (.queen d) with
            | some d => some (.queen d)
            | none =>
              match s.waitMove with
              | some m => some m
              | none => s.bestOf (kingMoves ++ queenMoves)

/-- The state has reached the goal relative to `s0`: it is checkmate, or
its potential is below that of `s0` and it is not dead. -/
def goal (s0 s : KQState) : Bool :=
  s.mateB || (s.mu < s0.mu && !s.deadB)

/-- Within `n` plies of scripted play from `s`, the goal relative to `s0`
is reached. Each ply first probes a waiting move, then follows the
script. Every played move is checked with `oneOk`. -/
def chain (s0 : KQState) : KQState → Nat → Bool
  | _, 0 => false
  | s, n + 1 =>
    (match s.waitMove with
      | some m => s.oneOk m && goal s0 (s.apply m)
      | none => false) ||
    match s.scriptMove with
    | none => false
    | some m =>
      s.oneOk m &&
      let s1 := s.apply m
      (goal s0 s1 || chain s0 s1 n)

/-- Plies of scripted play allowed to lower the potential. -/
def window : Nat := 14

/-- A state passes: it is illegal, checkmate, dead, or the script lowers
its potential. -/
def checkState (s : KQState) : Bool :=
  !s.okB || s.mateB || s.deadB || chain s s window

/-- Every placement of the three pieces, with either side to move, is
covered. -/
def checkAll : Bool :=
  allSquares.all fun wk =>
    allSquares.all fun bk =>
      allSquares.all fun qs =>
        checkState ⟨.white, wk, bk, qs⟩ && checkState ⟨.black, wk, bk, qs⟩

/-! ### The mating line -/

/-- The moves of a successful `chain` from `s` relative to `s0`, if any. -/
def chainPath (s0 : KQState) : KQState → Nat → Option (List KQMove)
  | _, 0 => none
  | s, n + 1 =>
    let viaWait : Option (List KQMove) :=
      match s.waitMove with
      | some m => if s.oneOk m && goal s0 (s.apply m) then some [m] else none
      | none => none
    match viaWait with
    | some ms => some ms
    | none =>
      match s.scriptMove with
      | none => none
      | some m =>
        if s.oneOk m then
          let s1 := s.apply m
          if goal s0 s1 then some [m] else (chainPath s0 s1 n).map (m :: ·)
        else none

/-- The state after a sequence of moves. -/
def applyAll (s : KQState) (ms : List KQMove) : KQState :=
  ms.foldl apply s

/-- The mating line in state moves; `fuel` bounds the number of rounds. -/
def matingLineAux : KQState → Nat → List KQMove
  | _, 0 => []
  | s, fuel + 1 =>
    if s.mateB || s.deadB then []
    else
      match chainPath s s window with
      | some ms => ms ++ matingLineAux (s.applyAll ms) fuel
      | none => []

/-- The chess moves of a sequence of state moves. -/
def toMoves : KQState → List KQMove → List Move
  | _, [] => []
  | s, m :: ms => s.move m :: toMoves (s.apply m) ms

/-- The engineered mating line from `s`, as chess moves. Every round
lowers the potential or mates, so `2 * s.mu + 2` rounds suffice. -/
def matingLine (s : KQState) : List Move :=
  s.toMoves (matingLineAux s (2 * s.mu + 2))

/-- The three-piece state of a white-queen position, if the board holds
exactly those pieces in a legal arrangement. -/
def ofPositionWhite? (p : Position) : Option KQState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .white, kind := .queen }) with
  | some wk, some bk, some qs =>
    if (⟨p.toMove, wk, bk, qs⟩ : KQState).okB && (allSquares.all fun q =>
          p.board q == Board.kingsQueenBoard wk bk qs .white q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove, wk, bk, qs⟩
    else none
  | _, _, _ => none

/-- The three-piece state of a black-queen position, rotated into the
white-queen frame. -/
def ofPositionBlack? (p : Position) : Option KQState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .queen }) with
  | some wk, some bk, some qs =>
    if (⟨p.toMove.other, bk.rot180, wk.rot180, qs.rot180⟩ : KQState).okB &&
        (allSquares.all fun q =>
          p.board q == Board.kingsQueenBoard wk bk qs .black q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove.other, bk.rot180, wk.rot180, qs.rot180⟩
    else none
  | _, _, _ => none

/-- The white-queen-frame state of a king-and-queen versus king position. -/
def ofPosition? (p : Position) : Option KQState :=
  match ofPositionWhite? p with
  | some s => some s
  | none => ofPositionBlack? p

/-! ## Soundness -/

open Position

theorem kingAttacks_ne {s t : Square} (h : KingAttacks s t) : s ≠ t := h.1

theorem queenAttacks_ne {s t : Square} (h : QueenAttacks s t) : s ≠ t := by
  cases h with
  | inl hB => exact hB.1
  | inr hR => exact hR.1

theorem queenBetween_eq {s t : Square} (_h : QueenAttacks s t) (u : Square) :
    queenBetween s t u = decide (Between s t u) := rfl

theorem mem_kingNeighbors {k d : Square} (h : KingAttacks k d) :
    d ∈ kingNeighbors k := by
  revert k d
  native_decide

theorem mem_queenDests {q d : Square} (h : QueenAttacks q d) :
    d ∈ queenDests q := by
  revert q d
  native_decide

theorem castlingSide_none_of_kingAttacks (c : Color) {s t : Square}
    (h : KingAttacks s t) : (Move.std s t).castlingSide? c = none := by
  revert c s t
  native_decide

theorem queenChecks_iff (qs d wk : Square) :
    queenChecks qs d wk = true ↔ QueenAttacks qs d ∧ ¬ Between qs d wk := by
  unfold queenChecks
  by_cases hR : QueenAttacks qs d
  · rw [queenBetween_eq hR]
    simp [hR]
  · simp [hR]

theorem kingAttackedBlack_iff (wk bk qs : Square) :
    kingAttackedBlack wk bk qs = true ↔
      KingAttacks wk bk ∨ (QueenAttacks qs bk ∧ ¬ Between qs bk wk) := by
  simp [kingAttackedBlack, queenChecks_iff, Bool.or_eq_true]

theorem okB_iff (s : KQState) :
    s.okB = true ↔
      s.wk ≠ s.bk ∧ s.wk ≠ s.qs ∧ s.bk ≠ s.qs ∧
        ¬ KingAttacks s.wk s.bk ∧ s.inCheckB s.toMove.other = false := by
  simp [okB, and_assoc]

theorem kingIsAttacked_white_eq (wk bk qs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) :
    (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .white =
      kingAttackedWhite wk bk := by
  rw [Bool.eq_iff_iff, Board.kingsQueenBoard_kingIsAttacked_white wk bk qs .white h1 h2 h3]
  simp [kingAttackedWhite, kingAttacks_symmetric]

theorem kingIsAttacked_black_eq (wk bk qs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) :
    (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .black =
      kingAttackedBlack wk bk qs := by
  rw [Bool.eq_iff_iff, Board.kingsQueenBoard_kingIsAttacked_black wk bk qs .white h1 h2 h3]
  simp [kingAttackedBlack_iff]

theorem kingIsAttacked_eq (s : KQState) (hok : s.okB = true) (c : Color) :
    s.toPosition.board.kingIsAttacked c = s.inCheckB c := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  cases c with
  | white => exact kingIsAttacked_white_eq _ _ _ h1 h2 h3
  | black => exact kingIsAttacked_black_eq _ _ _ h1 h2 h3

theorem fastKingW_iff (wk d bk qs : Square) :
    fastKingW wk d bk qs = true ↔
      KingAttacks wk d ∧ d ≠ bk ∧ d ≠ qs ∧ ¬ KingAttacks bk d := by
  simp [fastKingW, and_assoc]

theorem fastQueen_iff (wk d bk qs : Square) :
    fastQueen wk d bk qs = true ↔
      QueenAttacks qs d ∧ d ≠ wk ∧ d ≠ bk ∧ queenBetween qs d wk = false ∧
        queenBetween qs d bk = false := by
  simp [fastQueen, and_assoc]

theorem fastKingB_iff (wk d bk qs : Square) :
    fastKingB wk d bk qs = true ↔
      KingAttacks bk d ∧ d ≠ wk ∧
        (d = qs ∧ ¬ KingAttacks wk d ∨
          d ≠ qs ∧ ¬ KingAttacks wk d ∧ queenChecks qs d wk = false) := by
  unfold fastKingB
  by_cases hd : d = qs
  · simp [hd, and_assoc]
  · simp [hd, and_assoc]

/-! ### Playing moves -/

theorem play_whiteKing {s : KQState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastKingW s.wk d s.bk s.qs = true) :
    isLegalMove s.toPosition (Move.std s.wk d) = true ∧
      s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdbk, hdqs, hsafe⟩ := (fastKingW_iff _ _ _ _).mp hm
  have hdwk : d ≠ s.wk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.wk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsQueenBoard s.wk s.bk s.qs .white s.wk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsQueenBoard_white _ _ _ _
  have hdstNone : s.toPosition.board (Move.std s.wk d).dst = none :=
    Board.kingsQueenBoard_other _ _ _ _ _ hdwk hdbk hdqs
  have hside : (Move.std s.wk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.wk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.wk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsQueenBoard d s.bk s.qs .white := by
    rw [hba]
    change (Board.kingsQueenBoard s.wk s.bk s.qs .white).relocate s.wk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsQueenBoard_white _ _ _ _ _ h1 h2 h3 hdwk hdbk hdqs
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
    change (Board.kingsQueenBoard d s.bk s.qs .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq d s.bk s.qs hdbk hdqs h3]
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

theorem play_blackKing {s : KQState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : d ≠ s.qs)
    (hmv : fastKingB s.wk d s.bk s.qs = true) :
    isLegalMove s.toPosition (Move.std s.bk d) = true ∧
      s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
  have hdbk : d ≠ s.bk := (kingAttacks_ne hka).symm
  have hdqs : d ≠ s.qs := hm
  have hsrcP : s.toPosition.board (Move.std s.bk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsQueenBoard s.wk s.bk s.qs .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsQueenBoard_black _ _ _ _ h1
  have hdstNone : s.toPosition.board (Move.std s.bk d).dst = none :=
    Board.kingsQueenBoard_other _ _ _ _ _ hdwk hdbk hdqs
  have hside : (Move.std s.bk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsQueenBoard s.wk d s.qs .white := by
    rw [hba]
    change (Board.kingsQueenBoard s.wk s.bk s.qs .white).relocate s.bk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsQueenBoard_black _ _ _ _ _ h1 h2 h3 hdwk hdbk hdqs
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
  have hnR : queenChecks s.qs d s.wk = false := by
    rcases hrest with ⟨heq, _⟩ | ⟨_, _, h⟩
    · exact (hm heq).elim
    · exact h
  have hsafe' : (s.toPosition.play (Move.std s.bk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .white, bk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsQueenBoard s.wk d s.qs .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk d s.qs hdwk.symm h2 hdqs]
    simp [kingAttackedBlack, hsafeK, hnR]
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

theorem play_queen {s : KQState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastQueen s.wk d s.bk s.qs = true) :
    isLegalMove s.toPosition (Move.std s.qs d) = true ∧
      s.toPosition.play (Move.std s.qs d) = (s.apply (.queen d)).toPosition := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  obtain ⟨hR, hdwk, hdbk, hnwk, hnbk⟩ := (fastQueen_iff _ _ _ _).mp hm
  have hdqs : d ≠ s.qs := (queenAttacks_ne hR).symm
  have hsrcP : s.toPosition.board (Move.std s.qs d).src =
      some { color := s.toPosition.toMove, kind := .queen } := by
    change Board.kingsQueenBoard s.wk s.bk s.qs .white s.qs =
      some { color := s.toMove, kind := .queen }
    rw [ht]
    exact Board.kingsQueenBoard_queen _ _ _ _ h2 h3
  have hdstNone : s.toPosition.board (Move.std s.qs d).dst = none :=
    Board.kingsQueenBoard_other _ _ _ _ _ hdwk hdbk hdqs
  have hplay := play_of_some s.toPosition (Move.std s.qs d) hsrcP
  have hboard' : s.toPosition.boardAfter (Move.std s.qs d)
      { color := s.toPosition.toMove, kind := .queen } =
      Board.kingsQueenBoard s.wk s.bk d .white := by
    rw [boardAfter_queen _ _ rfl]
    change (Board.kingsQueenBoard s.wk s.bk s.qs .white).relocate s.qs d
      { color := s.toMove, kind := .queen } = _
    rw [ht]
    exact Board.relocate_kingsQueenBoard_queen _ _ _ _ _ h1 h2 h3 hdwk hdbk hdqs
  have hplay' : s.toPosition.play (Move.std s.qs d) = (s.apply (.queen d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_queen]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.qs d).src (Move.std s.qs d).dst = true := by
    change (Board.kingsQueenBoard s.wk s.bk s.qs .white).attacks s.qs d = true
    rw [Board.kingsQueenBoard_attacks_queen_iff h2 h3]
    refine ⟨hR, ?_, ?_⟩
    · rw [queenBetween_eq hR] at hnwk
      exact of_decide_eq_false hnwk
    · rw [queenBetween_eq hR] at hnbk
      exact of_decide_eq_false hnbk
  have hsafe' : (s.toPosition.play (Move.std s.qs d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.queen d) = { s with toMove := .black, qs := d } := by
      simp [apply]
    rw [hplay', happ]
    change (Board.kingsQueenBoard s.wk s.bk d .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq s.wk s.bk d h1 hdwk.symm hdbk.symm]
    simp [kingAttackedWhite, hna]
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.qs d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.queen == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.queen == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem fastLegal_sound {s : KQState} {m : KQMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
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
      obtain ⟨hnqs, hmv⟩ := Bool.and_eq_true_iff.mp hm
      have hn : d ≠ s.qs := bne_iff_ne.mp hnqs
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.bk d) ▸
        play_blackKing hok ht hn hmv
  | queen d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      exact (by simp [move] : s.move (.queen d) = Move.std s.qs d) ▸
        play_queen hok ht hm
    | black =>
      simp [fastLegal, ht] at hm

theorem legalMove_of_fastLegal {s : KQState} {m : KQMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) : LegalMove s.toPosition (s.move m) :=
  (fastLegal_sound hok hm).1

theorem play_move_eq {s : KQState} {m : KQMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    s.toPosition.play (s.move m) = (s.apply m).toPosition :=
  (fastLegal_sound hok hm).2

theorem apply_okB_of_fastLegal {s : KQState} {m : KQMove}
    (hok : s.okB = true) (hm : s.fastLegal m = true) : (s.apply m).okB = true := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hka, hdbk, hdqs, hsafeK⟩ := (fastKingW_iff _ _ _ _).mp hm
      have hna' : ¬ KingAttacks d s.bk := mt kingAttacks_symmetric.mp hsafeK
      have happ : s.apply (.king d) = ⟨.black, d, s.bk, s.qs⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.black, d, s.bk, s.qs⟩).mpr
        ⟨hdbk, hdqs, h3, hna', by simpa [inCheckB, kingAttackedWhite] using hna'⟩
    | black =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hnqs, hmv⟩ := Bool.and_eq_true_iff.mp hm
      obtain ⟨hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
      have hdqs : d ≠ s.qs := bne_iff_ne.mp hnqs
      have hsafeK : ¬ KingAttacks s.wk d := by
        rcases hrest with ⟨_, h⟩ | ⟨_, h, _⟩ <;> exact h
      have hnR : queenChecks s.qs d s.wk = false := by
        rcases hrest with ⟨heq, _⟩ | ⟨_, _, h⟩
        · exact (hdqs heq).elim
        · exact h
      have happ : s.apply (.king d) = ⟨.white, s.wk, d, s.qs⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.white, s.wk, d, s.qs⟩).mpr
        ⟨hdwk.symm, h2, hdqs, hsafeK, by
          simp [inCheckB, kingAttackedBlack, hsafeK, hnR]⟩
  | queen d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hR, hdwk, hdbk, _, _⟩ := (fastQueen_iff _ _ _ _).mp hm
      have happ : s.apply (.queen d) = ⟨.black, s.wk, s.bk, d⟩ := by simp [apply]
      rw [happ]
      exact (okB_iff ⟨.black, s.wk, s.bk, d⟩).mpr
        ⟨h1, hdwk.symm, hdbk.symm, hna, by simpa [inCheckB, kingAttackedWhite] using hna⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem oneOk_iff (s : KQState) (m : KQMove) :
    s.oneOk m = true ↔
      s.fastLegal m = true ∧ (s.apply m).okB = true ∧
        ((s.apply m).mateB = true ∨ (s.apply m).deadB = false) := by
  simp [oneOk, Bool.and_eq_true, Bool.or_eq_true]

def Progress (s0 s1 : KQState) : Prop :=
  s1.okB = true ∧ Reachable s0.toPosition s1.toPosition ∧
    (s1.mateB = true ∨ (s1.mu < s0.mu ∧ s1.deadB = false))

theorem reachable_apply {s0 s : KQState} {m : KQMove}
    (hr : Reachable s0.toPosition s.toPosition) (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    Reachable s0.toPosition (s.apply m).toPosition := by
  have := Reachable.step (s.move m) hr (legalMove_of_fastLegal hok hm)
  rwa [play_move_eq hok hm] at this

theorem goal_sound {s0 s : KQState} (hok : s.okB = true)
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

theorem chain_sound {s0 : KQState} :
    ∀ (n : Nat) (s : KQState), s.okB = true → Reachable s0.toPosition s.toPosition →
      chain s0 s n = true → ∃ s1, Progress s0 s1 := by
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
        obtain ⟨hfl, hok1, _⟩ := (oneOk_iff s m).mp hone
        exact goal_sound hok1 (reachable_apply hr hok hfl) hg
      · cases h
    · split at h
      · cases h
      · rename_i m _
        simp only [Bool.and_eq_true, Bool.or_eq_true] at h
        obtain ⟨hone, hrest⟩ := h
        obtain ⟨hfl, hok1, _⟩ := (oneOk_iff s m).mp hone
        have hr1 := reachable_apply hr hok hfl
        rcases hrest with hg | hc
        · exact goal_sound hok1 hr1 hg
        · exact ih _ hok1 hr1 hc

theorem checkState_progress {s : KQState} (hok : s.okB = true)
    (h : s.checkState = true) :
    s.mateB = true ∨ s.deadB = true ∨ ∃ s1, Progress s s1 := by
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
      exact Or.inr (Or.inr (chain_sound window s hok Reachable.refl h))

theorem mateB_toMove {s : KQState} (hm : s.mateB = true) : s.toMove = .black := by
  simp only [mateB, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1

theorem mateB_checked {s : KQState} (hm : s.mateB = true) :
    kingAttackedBlack s.wk s.bk s.qs = true := by
  simp only [mateB, Bool.and_eq_true] at hm
  exact hm.1.2

theorem mateB_flight {s : KQState} (hm : s.mateB = true) {d : Square}
    (hd : d ∈ kingNeighbors s.bk) :
    (d == s.wk || decide (KingAttacks s.wk d) ||
      (d != s.qs && queenChecks s.qs d s.wk)) = true := by
  simp only [mateB, Bool.and_eq_true, List.all_eq_true] at hm
  exact hm.2 d hd

theorem ne_of_kingsQueenBoard_eq_none {wk bk qs s : Square} {c : Color}
    (h : Board.kingsQueenBoard wk bk qs c s = none) :
    s ≠ wk ∧ s ≠ bk ∧ s ≠ qs := by
  unfold Board.kingsQueenBoard at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- In a `mateB` state, Black has no legal move. -/
theorem mateB_black_no_legalMove {s : KQState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : s.mateB = true) (m : Move) :
    ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .black := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
      some ⟨.black, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.bk := Board.kingsQueenBoard_eq_black_king hsrc'
    have hka : KingAttacks s.bk m.dst := by
      have hatt' :
          (Board.kingsQueenBoard s.wk s.bk s.qs .white).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .black = none := ht ▸ hside rfl
    have hplay := play_of_some s.toPosition m hsrc
    have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hside' hpromo
    have hboard : (s.toPosition.play m).board =
        (Board.kingsQueenBoard s.wk s.bk s.qs .white).relocate s.bk m.dst
          { color := .black, kind := .king } := by
      rw [hplay, hba, hsq]
      rfl
    have hmem := mateB_flight hm (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hqs
    · obtain ⟨hdwk, hdbk, hdqs⟩ := ne_of_kingsQueenBoard_eq_none (by
        simpa [toPosition] using hempty)
      rw [hboard, Board.relocate_kingsQueenBoard_black s.wk s.bk s.qs m.dst .white
        h1 h2 h3 hdwk hdbk hdqs, kingIsAttacked_black_eq s.wk m.dst s.qs
        hdwk.symm h2 hdqs] at hsafe'
      have hwkB : (m.dst == s.wk) = false := by simp [hdwk]
      have hsafe'' : ¬ KingAttacks s.wk m.dst ∧
          KQState.queenChecks s.qs m.dst s.wk = false := by
        simpa [KQState.kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      have hkaF : decide (KingAttacks s.wk m.dst) = false := decide_eq_false hsafe''.1
      have hrF : KQState.queenChecks s.qs m.dst s.wk = false := hsafe''.2
      simp [hwkB, hkaF, hrF] at hmem
    · rw [hqs] at hmem hboard
      have hwkB : (s.qs == s.wk) = false := by simp [h2.symm]
      by_cases hprot : KingAttacks s.wk s.qs
      · rw [hboard, Board.relocate_capture_queen_black s.wk s.bk s.qs h1 h2 h3] at hsafe'
        rw [Board.kingsBoard_kingIsAttacked_black s.wk s.qs h2] at hsafe'
        exact of_decide_eq_false hsafe' hprot
      · have hkaF : decide (KingAttacks s.wk s.qs) = false := decide_eq_false hprot
        simp [hwkB, hkaF] at hmem
  · simp only at hk
    subst hk
    have hsrc'' := hsrc'
    unfold Board.kingsQueenBoard at hsrc''
    split_ifs at hsrc'' <;> cases hsrc''

/-- A `mateB` state of an `okB` state is a checkmate position. -/
theorem inCheckmate_of_mateB {s : KQState} (hok : s.okB = true) (hm : s.mateB = true) :
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

theorem hasNoncaptureLegal_of_fastLegal {s : KQState} {m : KQMove}
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
  | queen d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      have hR : QueenAttacks s.qs d := ((fastQueen_iff _ _ _ _).mp hm).1
      simp only [hasNoncaptureLegal, ht, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨d, mem_queenDests hR, hm⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem toPosition_isKingAndQueen {s : KQState} (hok : s.okB = true) :
    IsKingAndQueen s.toPosition := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  exact ⟨s.wk, s.bk, s.qs, .white, h1, h2, h3, hna, rfl, rfl, rfl⟩

end KQState

namespace Position

theorem IsKingAndQueen.of_play {p : Position} {m : Move}
    (h : IsKingAndQueen p) (hm : LegalMove p m) :
    IsKingAndQueen (p.play m) ∨ IsTwoKings (p.play m) := by
  obtain ⟨wk, bk, qs, c, hwk_bk, hwk_qs, hbk_qs, hna, hboard, hcstl, _hep⟩ := h
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrcP, hcol', hkind, hside⟩ :=
    kingQueen_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = qs :=
    (Board.kingsQueenBoard_isSome wk bk qs m.src c).mp (by
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
      have hpiece : piece = { color := p.toMove, kind := .queen } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_queen p m (c := p.toMove) hpromo, hcstl]
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
      have hpiece : piece = { color := p.toMove, kind := .queen } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .queen }
              (p.boardAfter m { color := p.toMove, kind := .queen }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_queen _ _ _
  rcases hdstOr with hdstNone | hdstRs
  · have hdstW : m.dst ≠ wk := by
      intro heq; rw [heq, hboard, Board.kingsQueenBoard_white] at hdstNone; cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsQueenBoard_black wk bk qs c hwk_bk] at hdstNone
      cases hdstNone
    have hdstS : m.dst ≠ qs := by
      intro heq
      rw [heq, hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs] at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsQueenBoard_white])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsQueenBoard_white wk bk qs m.dst c
        hwk_bk hwk_qs hbk_qs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsQueenBoard m.dst bk qs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsQueenBoard wk bk qs c).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsQueenBoard m.dst bk qs c := hrel
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by simpa [ht] using hsafe
        have hiff := Board.kingsQueenBoard_kingIsAttacked_white m.dst bk qs c
          hdstB hdstS hbk_qs
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨m.dst, bk, qs, c, hdstB, hdstS, hbk_qs, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsQueenBoard_black wk bk qs c hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsQueenBoard_black wk bk qs m.dst c
        hwk_bk hwk_qs hbk_qs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsQueenBoard wk m.dst qs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsQueenBoard wk bk qs c).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsQueenBoard wk m.dst qs c := hrel
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by simpa [ht] using hsafe
        have hiff := Board.kingsQueenBoard_kingIsAttacked_black wk m.dst qs c
          hdstW.symm hwk_qs hdstS
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨wk, m.dst, qs, c, hdstW.symm, hwk_qs, hdstS, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := c, kind := .queen } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcS, hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs])
      have ht : p.toMove = c := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_queen p m (c := c) hpromo
      have hrel := Board.relocate_kingsQueenBoard_queen wk bk qs m.dst c
        hwk_bk hwk_qs hbk_qs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsQueenBoard wk bk m.dst c := by
        calc (p.play m).board
            = p.boardAfter m { color := c, kind := .queen } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := c, kind := .queen } := hba
          _ = (Board.kingsQueenBoard wk bk qs c).relocate qs m.dst
                { color := c, kind := .queen } := by
              rw [hboard, hsrcS]
          _ = Board.kingsQueenBoard wk bk m.dst c := hrel
      exact Or.inl ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep'⟩
  · have hqueen : p.board qs = some { color := c, kind := .queen } := by
      rw [hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs]
    have ht : p.toMove = c.other :=
      destOk_toMove_of_dst_queen hboard hwk_qs hbk_qs hdstRs hdestOk
    have hsrcNeRs : m.src ≠ qs := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hqueen] at hsrcP'
      have hpc : c = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      exact Color.other_ne c hpc.symm
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsQueenBoard_white])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.black := by
        have : c.other = Color.white := ht.symm.trans htW
        cases c
        · simp [Color.other] at this
        · rfl
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [htW] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_queen_white wk bk qs hwk_bk hwk_qs hbk_qs
      have hboard' : (p.play m).board = Board.kingsBoard qs bk := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsQueenBoard wk bk qs .black).relocate wk qs
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstRs, hc]
          _ = Board.kingsBoard qs bk := hrel
      have hna' : ¬ KingAttacks qs bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [htW] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_white qs bk hbk_qs.symm] at hsafe'
        exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
      exact Or.inr ⟨qs, bk, hbk_qs.symm, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsQueenBoard_black wk bk qs c hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.white := by
        have : c.other = Color.black := ht.symm.trans htB
        cases c
        · rfl
        · simp [Color.other] at this
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [htB] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_queen_black wk bk qs hwk_bk hwk_qs hbk_qs
      have hboard' : (p.play m).board = Board.kingsBoard wk qs := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsQueenBoard wk bk qs .white).relocate bk qs
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstRs, hc]
          _ = Board.kingsBoard wk qs := hrel
      have hna' : ¬ KingAttacks wk qs := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [htB] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_black wk qs hwk_qs] at hsafe'
        exact of_decide_eq_false hsafe'
      exact Or.inr ⟨wk, qs, hwk_qs, hna', hboard', hcast', hep'⟩
    · exact (hsrcNeRs hsrcS).elim

theorem IsKingAndQueen.of_reachable {p q : Position}
    (h : IsKingAndQueen p) (hr : Reachable p q) :
    IsKingAndQueen q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    cases ih with
    | inl hkr => exact hkr.of_play hleg
    | inr htk => exact Or.inr (htk.of_play hleg)

end Position

namespace KQState

open Position

theorem destOk_capture_queen {s : KQState} (hok : s.okB = true)
    (ht : s.toMove = .black) :
    s.toPosition.destOk (Move.std s.bk s.qs) = true := by
  obtain ⟨_, h2, h3, _, _⟩ := (okB_iff s).mp hok
  unfold destOk
  change (match Board.kingsQueenBoard s.wk s.bk s.qs .white s.qs with
    | none => true
    | some q => (q.color != s.toPosition.toMove) && (q.kind != .king)) = true
  rw [Board.kingsQueenBoard_queen s.wk s.bk s.qs .white h2 h3]
  simp [toPosition, ht]

theorem play_blackCapture {s : KQState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hka : KingAttacks s.bk s.qs)
    (hprot : ¬ KingAttacks s.wk s.qs) :
    isLegalMove s.toPosition (Move.std s.bk s.qs) = true := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  have hsrcP : s.toPosition.board (Move.std s.bk s.qs).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsQueenBoard s.wk s.bk s.qs .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsQueenBoard_black _ _ _ _ h1
  have hside : (Move.std s.bk s.qs).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk s.qs) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk s.qs)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk s.qs)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsBoard s.wk s.qs := by
    rw [hba]
    change (Board.kingsQueenBoard s.wk s.bk s.qs .white).relocate s.bk s.qs
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_capture_queen_black _ _ _ h1 h2 h3
  have hgeo : s.toPosition.board.attacks (Move.std s.bk s.qs).src
      (Move.std s.bk s.qs).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.bk s.qs)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    rw [hplay, hboard']
    change (Board.kingsBoard s.wk s.qs).kingIsAttacked s.toMove = false
    rw [ht, Board.kingsBoard_kingIsAttacked_black s.wk s.qs h2]
    exact decide_eq_false hprot
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  have hdest : s.toPosition.destOk (Move.std s.bk s.qs) = true :=
    destOk_capture_queen hok ht
  rw [hdest]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.bk s.qs).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem deadB_mate_eq_false {s : KQState} (hd : s.deadB = true) :
    s.mateB = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.1

theorem deadB_hasNoncapture_eq_false {s : KQState} (hd : s.deadB = true) :
    s.hasNoncaptureLegal = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.2

theorem white_not_inCheck {s : KQState} (hok : s.okB = true) :
    s.inCheckB .white = false := by
  obtain ⟨_, _, _, hna, _⟩ := (okB_iff s).mp hok
  simp [inCheckB, kingAttackedWhite, hna]

theorem kingAttacks_of_mem_kingNeighbors {k d : Square}
    (h : d ∈ kingNeighbors k) : KingAttacks k d := by
  revert k d
  native_decide

theorem inCheckmate_implies_mateB {s : KQState} (hok : s.okB = true)
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
    have hchk' : kingAttackedBlack s.wk s.bk s.qs = true := by
      simpa [inCheckB] using hchk
    have hall : (kingNeighbors s.bk).all (fun d =>
        d == s.wk || decide (KingAttacks s.wk d) ||
          (d != s.qs && queenChecks s.qs d s.wk)) = true := by
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
      have h3 : (d != s.qs && queenChecks s.qs d s.wk) = false := by
        cases h : (d != s.qs && queenChecks s.qs d s.wk)
        · rfl
        · simp [h1, h2, h] at hf
      have hkaB : KingAttacks s.bk d := kingAttacks_of_mem_kingNeighbors hd
      have hkaW : ¬ KingAttacks s.wk d := of_decide_eq_false h2
      have hnoleg : ∀ mv : Move, ¬ LegalMove s.toPosition mv :=
        (InCheckmate_iff_forall_not_LegalMove s.toPosition).mp hm |>.2
      by_cases hqs : d = s.qs
      · subst hqs
        have hleg : LegalMove s.toPosition (Move.std s.bk s.qs) :=
          play_blackCapture hok ht hkaB hkaW
        exact hnoleg _ hleg
      · have hne : (d != s.qs) = true := bne_iff_ne.mpr hqs
        have hnR : queenChecks s.qs d s.wk = false := by simpa [hne] using h3
        have hdwk : d ≠ s.wk := bne_iff_ne.mp (by simpa using h1)
        have hmv : fastKingB s.wk d s.bk s.qs = true := by
          simp [fastKingB, hkaB, hdwk, hqs, hkaW, hnR]
        have hfl : s.fastLegal (.king d) = true := by
          simp [fastLegal, ht, bne_iff_ne.mpr hqs, hmv]
        exact hnoleg _ (legalMove_of_fastLegal hok hfl)
    simp [mateB, ht, hchk', hall]

theorem not_inCheckmate_of_deadB {s : KQState} (hok : s.okB = true)
    (hd : s.deadB = true) : ¬ InCheckmate s.toPosition := by
  intro hm
  have := inCheckmate_implies_mateB hok hm
  exact Bool.false_ne_true ((deadB_mate_eq_false hd).symm.trans this)

theorem fastLegal_of_legalMove_noncapture {s : KQState} {m : Move}
    (hok : s.okB = true) (hm : LegalMove s.toPosition m)
    (he : s.toPosition.board m.dst = none) :
    ∃ km, s.fastLegal km = true := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hpromo, _, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core rfl rfl hm
  obtain ⟨hdwk, hdbk, hdqs⟩ := ne_of_kingsQueenBoard_eq_none (by
    simpa [toPosition] using he)
  rcases piece with ⟨pc, pk⟩
  subst hpc
  rcases hkind with hk | hk
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcW : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
          some { color := .white, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.wk := Board.kingsQueenBoard_eq_white_king hsrcW
      have hattW : (Board.kingsQueenBoard s.wk s.bk s.qs .white).attacks m.src m.dst = true := by
        simpa [toPosition] using hatt
      have hka : KingAttacks s.wk m.dst := by
        rw [Board.attacks_king hsrcW, hsq] at hattW
        exact of_decide_eq_true hattW
      have hplay := play_of_some s.toPosition m hsrc
      have hsideW : m.castlingSide? Color.white = none := by
        simpa [toPosition, ht] using hside rfl
      have hba := boardAfter_king_no_castle s.toPosition m (c := .white) hsideW hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsQueenBoard m.dst s.bk s.qs .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.white := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsQueenBoard_white s.wk s.bk s.qs m.dst .white
          h1 h2 h3 hdwk hdbk hdqs
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .white = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_white_eq m.dst s.bk s.qs hdbk hdqs h3] at hsafe'
      have hsafeK : ¬ KingAttacks s.bk m.dst := by
        simpa [kingAttackedWhite, kingAttacks_symmetric] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, fastKingW, hka, hdbk, hdqs, hsafeK]
    | black =>
      have hsrcB : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
          some { color := .black, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.bk := Board.kingsQueenBoard_eq_black_king hsrcB
      have hattB : (Board.kingsQueenBoard s.wk s.bk s.qs .white).attacks m.src m.dst = true := by
        simpa [toPosition] using hatt
      have hka : KingAttacks s.bk m.dst := by
        rw [Board.attacks_king hsrcB, hsq] at hattB
        exact of_decide_eq_true hattB
      have hplay := play_of_some s.toPosition m hsrc
      have hsideB : m.castlingSide? Color.black = none := by
        simpa [toPosition, ht] using hside rfl
      have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsQueenBoard s.wk m.dst s.qs .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsQueenBoard_black s.wk s.bk s.qs m.dst .white
          h1 h2 h3 hdwk hdbk hdqs
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_black_eq s.wk m.dst s.qs hdwk.symm h2 hdqs] at hsafe'
      have hpair : decide (KingAttacks s.wk m.dst) = false ∧
          queenChecks s.qs m.dst s.wk = false := by
        simpa [kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, bne_iff_ne.mpr hdqs, fastKingB, hka, hdwk, hdqs,
        of_decide_eq_false hpair.1, hpair.2]
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcR : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
          some { color := .white, kind := .queen } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.qs := Board.kingsQueenBoard_eq_queen hsrcR
      have hatt0 :
          (Board.kingsQueenBoard s.wk s.bk s.qs .white).attacks s.qs m.dst = true := by
        simpa [toPosition, hsq] using hatt
      obtain ⟨hR, hnw, hnb⟩ := (Board.kingsQueenBoard_attacks_queen_iff h2 h3).mp hatt0
      refine ⟨.queen m.dst, ?_⟩
      simp [fastLegal, ht, fastQueen, hR, hdwk, hdbk, queenBetween_eq hR,
        decide_eq_false hnw, decide_eq_false hnb]
    | black =>
      have hsrc' : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
          some ⟨.black, .queen⟩ := by simpa [toPosition, ht] using hsrc
      unfold Board.kingsQueenBoard at hsrc'
      split_ifs at hsrc' <;> cases hsrc'

theorem twoKings_of_deadB_legal {s : KQState} {m : Move}
    (hok : s.okB = true) (hd : s.deadB = true) (hm : LegalMove s.toPosition m) :
    IsTwoKings (s.toPosition.play m) := by
  have hplay := (toPosition_isKingAndQueen hok).of_play hm
  cases hplay with
  | inr htk => exact htk
  | inl _ =>
    obtain ⟨_, _, hdstOr, _, _, _, _, _, _, _⟩ := kingQueen_legalMove_core rfl rfl hm
    cases hdstOr with
    | inl he =>
      obtain ⟨km, hfl⟩ := fastLegal_of_legalMove_noncapture hok hm he
      exact (Bool.false_ne_true
        ((deadB_hasNoncapture_eq_false hd).symm.trans
          (hasNoncaptureLegal_of_fastLegal hfl))).elim
    | inr hqs =>
      obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
      have ht : s.toMove = .black :=
        destOk_toMove_of_dst_queen (p := s.toPosition) (m := m) (wk := s.wk)
          (bk := s.bk) (qs := s.qs) (c := Color.white) rfl h2 h3 hqs
          (kingQueen_legalMove_core (p := s.toPosition) rfl rfl hm).2.1
      obtain ⟨hpromo, _, _, hsafe, _, piece, hsrc, hpc, hkind, hside⟩ :=
        kingQueen_legalMove_core rfl rfl hm
      rcases piece with ⟨pc, pk⟩
      have hpc' : pc = .black := hpc.trans ht
      subst hpc'
      cases hkind with
      | inr hrk =>
        subst hrk
        have hsrc' : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
            some ⟨.black, .queen⟩ := by simpa [toPosition, ht] using hsrc
        unfold Board.kingsQueenBoard at hsrc'
        split_ifs at hsrc' <;> cases hsrc'
      | inl hk =>
        subst hk
        have hsrcB : Board.kingsQueenBoard s.wk s.bk s.qs .white m.src =
            some { color := .black, kind := .king } := by
          simpa [toPosition, ht] using hsrc
        have hsq : m.src = s.bk := Board.kingsQueenBoard_eq_black_king hsrcB
        have hpl := play_of_some s.toPosition m hsrc
        have hsideB : m.castlingSide? Color.black = none := by
          simpa [toPosition, ht] using hside rfl
        have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
        have hboard : (s.toPosition.play m).board = Board.kingsBoard s.wk s.qs := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this, hba, hsq, hqs]
          exact Board.relocate_capture_queen_black s.wk s.bk s.qs h1 h2 h3
        have hcast : (s.toPosition.play m).castling = ∅ := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this, hba]; exact castlingAfter_empty _
        have hep : (s.toPosition.play m).enPassant = none := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this]
          simp [enPassantAfter]
        have hna' : ¬ KingAttacks s.wk s.qs := by
          have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false :=
            by simpa [ht, toPosition] using hsafe
          rw [hboard, Board.kingsBoard_kingIsAttacked_black s.wk s.qs h2] at hsafe'
          exact of_decide_eq_false hsafe'
        exact ⟨s.wk, s.qs, h2, hna', hboard, hcast, hep⟩

theorem reachable_from_deadB {s : KQState} {q : Position}
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

theorem not_CheckmateReachable_of_deadB {s : KQState} (hok : s.okB = true)
    (hd : s.deadB = true) : ¬ CheckmateReachable s.toPosition := by
  intro ⟨q, hr, hq⟩
  rcases reachable_from_deadB hok hd hr with h | h
  · subst h
    exact not_inCheckmate_of_deadB hok hd hq
  · exact h.not_InCheckmate hq

/-- Every white-king file is covered by the script. -/
def checkFile (f : Fin 8) : Bool :=
  (List.finRange 8).all fun r =>
    allSquares.all fun bk =>
      allSquares.all fun qs =>
        checkState ⟨.white, ⟨f, r⟩, bk, qs⟩ &&
          checkState ⟨.black, ⟨f, r⟩, bk, qs⟩

set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile0 : checkFile 0 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile1 : checkFile 1 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile2 : checkFile 2 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile3 : checkFile 3 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile4 : checkFile 4 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile5 : checkFile 5 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
theorem checkFile6 : checkFile 6 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KQ vs K states.
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

theorem progress_exists {s : KQState} (hok : s.okB = true) :
    s.mateB = true ∨ s.deadB = true ∨ ∃ s1, Progress s s1 := by
  have hcs : s.checkState = true := by
    rcases s with ⟨tm, wk, bk, qs⟩
    have hwk := (List.all_eq_true.mp checkAll_true) wk (mem_allSquares _)
    have hbk := (List.all_eq_true.mp hwk) bk (mem_allSquares _)
    have hqs := (List.all_eq_true.mp hbk) qs (mem_allSquares _)
    have hpair := Bool.and_eq_true_iff.mp hqs
    cases tm
    · exact hpair.1
    · exact hpair.2
  exact checkState_progress hok hcs

theorem dead_or_checkmate_of_okB_aux :
    ∀ n (s : KQState), s.okB = true → s.mu = n →
      s.deadB = true ∨ CheckmateReachable s.toPosition := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hok hn
    rcases progress_exists hok with hm | hd | ⟨s1, hok1, hr, hp⟩
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

theorem checkmateReachable_of_okB_of_not_dead {s : KQState}
    (hok : s.okB = true) (hnd : s.deadB = false) :
    CheckmateReachable s.toPosition := by
  have h := dead_or_checkmate_of_okB_aux s.mu s hok rfl
  cases h with
  | inl hd => exact (Bool.false_ne_true (hnd.symm.trans hd)).elim
  | inr hcr => exact hcr

theorem checkmateReachable_iff_not_dead {s : KQState} (hok : s.okB = true) :
    CheckmateReachable s.toPosition ↔ s.deadB = false := by
  constructor
  · intro h
    cases hd : s.deadB with
    | true => exact (not_CheckmateReachable_of_deadB hok hd h).elim
    | false => rfl
  · intro hnd
    exact checkmateReachable_of_okB_of_not_dead hok hnd

/-- White to move always has a non-capturing move in a legal state. -/
theorem white_okB_hasNoncapture {wk bk qs : Square} :
    okB ⟨.white, wk, bk, qs⟩ = true →
      hasNoncaptureLegal ⟨.white, wk, bk, qs⟩ = true := by
  revert wk bk qs
  native_decide

theorem not_deadB_of_white {s : KQState} (hok : s.okB = true)
    (ht : s.toMove = .white) : s.deadB = false := by
  rcases s with ⟨tm, wk, bk, qs⟩
  subst ht
  have h := white_okB_hasNoncapture hok
  simp [deadB, h]

/-- The queen side to move can always reach checkmate. -/
theorem checkmateReachable_of_okB_white {s : KQState} (hok : s.okB = true)
    (ht : s.toMove = .white) : CheckmateReachable s.toPosition :=
  checkmateReachable_of_okB_of_not_dead hok (not_deadB_of_white hok ht)

end KQState


namespace Position


theorem IsKingAndQueen.castling_eq {p : Position} (h : IsKingAndQueen p) :
    p.castling = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

theorem IsKingAndQueen.enPassant_eq {p : Position} (h : IsKingAndQueen p) :
    p.enPassant = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := h
  exact he

theorem IsKingAndQueen.rot180 {p : Position} (h : IsKingAndQueen p) :
    IsKingAndQueen p.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
  have h2' : wk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h2
  have h3' : bk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h3
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  cases c with
  | white =>
    refine ⟨bk.rot180, wk.rot180, qs.rot180, .black, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsQueenBoard_white wk bk qs h1 h2 h3]
  | black =>
    refine ⟨bk.rot180, wk.rot180, qs.rot180, .white, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsQueenBoard_black wk bk qs h1 h2 h3]

theorem IsKingAndQueen.not_IsTwoKings {p : Position} (h : IsKingAndQueen p) :
    ¬ IsTwoKings p := by
  intro htk
  obtain ⟨wk, bk, qs, c, h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', hne', _, hboard', _, _⟩ := htk
  have h3c : p.board.occupied.card = 3 := by
    rw [hboard, Board.kingsQueenBoard_occupied wk bk qs c h1 h2 h3]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [h3]
    · simp [h1, h2]
  have h2c : p.board.occupied.card = 2 := by
    rw [hboard', Board.kingsBoard_occupied wk' bk' hne']
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne']
  omega


theorem piece_of_kind_queen (piece : Piece) (hr : piece.kind = .queen) :
    piece = { color := piece.color, kind := .queen } := by
  rcases piece with ⟨pc, pk⟩
  subst hr
  rfl

theorem IsKingAndQueen.play_rot180 {p : Position} {m : Move}
    (h : IsKingAndQueen p) (hm : LegalMove p m) :
    (p.play m).rot180 = p.rot180.play m.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, _, hboard, hc, he⟩ := h
  obtain ⟨hpromo, _, _, _, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hplay := play_of_some p m hsrc
  have hplayR := play_of_some p.rot180 m.rot180 hsrcR
  cases hkind with
  | inl hk =>
    have hpiece := piece_of_kind_king piece hk
    have hs : m.castlingSide? piece.color = none := by
      simpa [hpc] using hside hk
    have hba := boardAfter_king_no_castle p m (c := piece.color) hs hpromo
    have hka : KingAttacks m.src m.dst := by
      have hatt' : p.board.attacks m.src m.dst = true := hatt
      rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
      exact of_decide_eq_true hatt'
    have hsR : m.rot180.castlingSide? piece.flip.color = none := by
      have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
        rcases m with ⟨s, d, pr⟩
        simp [Move.rot180, Move.std] at hpromo ⊢
        simp [hpromo]
      rw [hmstd]
      exact KQState.castlingSide_none_of_kingAttacks _
        ((Square.kingAttacks_rot180 _ _).mp hka)
    have hbaR := boardAfter_king_no_castle p.rot180 m.rot180
      (c := piece.flip.color) hsR (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_king m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_king m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.king } : Piece).flip =
          { color := piece.flip.color, kind := .king } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .king }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]
  | inr hr =>
    have hpiece := piece_of_kind_queen piece hr
    have hba := boardAfter_queen p m (c := piece.color) hpromo
    have hbaR := boardAfter_queen p.rot180 m.rot180 (c := piece.flip.color)
      (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_queen m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_queen m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.queen } : Piece).flip =
          { color := piece.flip.color, kind := .queen } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .queen }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]

theorem IsKingAndQueen.legalMove_rot180_of {p : Position} {m : Move}
    (h : IsKingAndQueen p) (hm : LegalMove p m) :
    LegalMove p.rot180 m.rot180 := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  obtain ⟨hpromo, hdestOk, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingQueen_legalMove_core hboard hc hm
  have hsrcR : p.rot180.board m.rot180.src = some piece.flip := by
    rw [rot180_board, Move.rot180_src]
    simp only [Board.rot180, Square.rot180_involutive, hsrc, Option.map_some]
  have hdestR : p.rot180.destOk m.rot180 = true := by
    rwa [← destOk_rot180]
  have hnpawn : (piece.flip.kind == PieceKind.pawn) = false := by
    cases hkind <;> simp [Piece.flip, ‹_›]
  have hka_of_king (hk : piece.kind = .king) : KingAttacks m.src m.dst := by
    have hpiece := piece_of_kind_king piece hk
    have hatt' : p.board.attacks m.src m.dst = true := hatt
    rw [Board.attacks_king (hpiece ▸ hsrc)] at hatt'
    exact of_decide_eq_true hatt'
  have hkingB : (piece.flip.kind == PieceKind.king &&
      (m.rot180.castlingSide? p.rot180.toMove).isSome) = false := by
    cases hkind with
    | inl hk =>
      have hs : m.rot180.castlingSide? p.rot180.toMove = none := by
        have hmstd : m.rot180 = Move.std m.src.rot180 m.dst.rot180 := by
          rcases m with ⟨s, d, pr⟩
          simp [Move.rot180, Move.std] at hpromo ⊢
          simp [hpromo]
        rw [hmstd]
        exact KQState.castlingSide_none_of_kingAttacks p.rot180.toMove
          ((Square.kingAttacks_rot180 _ _).mp (hka_of_king hk))
      simp [Piece.flip, hk, hs]
    | inr hr => simp [Piece.flip, hr]
  have hattR : p.rot180.board.attacks m.rot180.src m.rot180.dst = true := by
    rw [rot180_board, Move.rot180_src, Move.rot180_dst, ← Board.attacks_rot180, hatt]
  have hsafeR :
      (p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove = false := by
    have hpl := IsKingAndQueen.play_rot180
      (⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ : IsKingAndQueen p) hm
    rw [← hpl]
    change (p.play m).board.rot180.kingIsAttacked p.toMove.other = false
    rw [← Board.kingIsAttacked_rot180]
    exact hsafe
  unfold LegalMove isLegalMove
  rw [hsrcR]
  have hcolR : (piece.flip.color == p.rot180.toMove) = true := by
    simp [Piece.flip, hpc, rot180_toMove]
  simp only [hcolR, Bool.true_and]
  rw [hdestR]
  simp only [Bool.true_and]
  simp only [hnpawn, hkingB]
  exact legal_king_step_bool _ _ _
    hattR (by simp [Move.rot180, hpromo]) hsafeR

theorem IsKingAndQueen.legalMove_rot180 {p : Position} {m : Move}
    (h : IsKingAndQueen p) :
    LegalMove p m ↔ LegalMove p.rot180 m.rot180 := by
  constructor
  · exact legalMove_rot180_of h
  · intro hm
    have := legalMove_rot180_of h.rot180 (m := m.rot180) hm
    simpa [rot180_involutive h.castling_eq h.enPassant_eq, Move.rot180_involutive]
      using this

theorem IsKingAndQueen.inCheckmate_rot180 {p : Position} (h : IsKingAndQueen p)
    (hm : InCheckmate p) : InCheckmate p.rot180 := by
  rw [InCheckmate_iff_forall_not_LegalMove] at hm ⊢
  refine ⟨?_, ?_⟩
  · change (p.rot180).board.kingIsAttacked p.rot180.toMove = true
    have this : p.board.kingIsAttacked p.toMove = true := hm.1
    rw [Board.kingIsAttacked_rot180] at this
    simpa [rot180_board, rot180_toMove] using this
  · intro m hleg
    exact hm.2 m.rot180 ((h.legalMove_rot180 (m := m.rot180)).mpr (by
      simpa [Move.rot180_involutive] using hleg))

theorem IsKingAndQueen.reachable_rot180 {p : Position} (hp : IsKingAndQueen p)
    {q : Position} (hr : Reachable p q) (hq : IsKingAndQueen q) :
    Reachable p.rot180 q.rot180 := by
  refine Reachable.rec (motive := fun q _ => IsKingAndQueen q →
      Reachable p.rot180 q.rot180) ?_ ?_ hr hq
  · intro _hq
    exact Reachable.refl
  · intro q m hrq hleg ih hq'
    have hqKQ : IsKingAndQueen q := by
      rcases hp.of_reachable hrq with h | htk
      · exact h
      · exact (hq'.not_IsTwoKings (htk.of_play hleg)).elim
    have hstep := Reachable.step m.rot180 (ih hqKQ) (hqKQ.legalMove_rot180.mp hleg)
    rwa [← hqKQ.play_rot180 hleg] at hstep

theorem IsKingAndQueen.checkmateReachable_rot180 {p : Position}
    (h : IsKingAndQueen p) :
    CheckmateReachable p ↔ CheckmateReachable p.rot180 := by
  constructor
  · intro ⟨q, hr, hm⟩
    rcases h.of_reachable hr with hq | htk
    · exact ⟨q.rot180, h.reachable_rot180 hr hq, hq.inCheckmate_rot180 hm⟩
    · exact (htk.not_InCheckmate hm).elim
  · intro ⟨q, hr, hm⟩
    have h' := h.rot180
    rcases h'.of_reachable hr with hq | htk
    · have hr' := h'.reachable_rot180 hr hq
      have hm' := hq.inCheckmate_rot180 hm
      rw [rot180_involutive h.castling_eq h.enPassant_eq] at hr'
      exact ⟨q.rot180, hr', hm'⟩
    · exact (htk.not_InCheckmate hm).elim

/-- A valid position with exactly three occupied squares, one of them a
queen, and no remaining castling rights, holds only the two kings and that
queen, with the kings not adjacent. Castling rights are an extra hypothesis:
a queen on `a1`/`h1` with its king on `e1` could otherwise still have rights. -/
theorem isKingAndQueen_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hqueen : ∃ s c, p.board s = some { color := c, kind := .queen })
    (hcstl : p.castling = ∅) :
    IsKingAndQueen p := by
  obtain ⟨hbv, hopp, _, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨qs, c, hqs⟩ := hqueen
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_qs : wk ≠ qs := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_queen (hking.symm.trans hqs)
  have hbk_qs : bk ≠ qs := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_queen (hking.symm.trans hqs)
  have hoccEq : p.board.occupied = {wk, bk, qs} := by
    have hsub : ({wk, bk, qs} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hqs]
    have hcard : ({wk, bk, qs} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_qs]
      · simp [hwk_bk, hwk_qs]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsQueenBoard wk bk qs c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsQueenBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsQueenBoard_black wk bk qs c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = qs
        · rw [hs, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs]
          exact hqs
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsQueenBoard_other wk bk qs s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsQueenBoard_kingIsAttacked_black wk bk qs c
          hwk_bk hwk_qs hbk_qs).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsQueenBoard_kingIsAttacked_white wk bk qs c
          hwk_bk hwk_qs hbk_qs).mpr (Or.inl (kingAttacks_symmetric.mp hk))
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
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
      · rw [hsq, hboard, Board.kingsQueenBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsQueenBoard_black wk bk qs c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsQueenBoard_queen wk bk qs c hwk_qs hbk_qs] at hpawn
        cases some_queen_ne_pawn hpawn
  exact ⟨wk, bk, qs, c, hwk_bk, hwk_qs, hbk_qs, hna, hboard, hcstl, he⟩

theorem exists_kqState_white {p : Position} (hv : Valid p)
    {wk bk qs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .white)
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    ∃ s : KQState, s.okB = true ∧ s.toPosition = p := by
  refine ⟨⟨p.toMove, wk, bk, qs⟩, ?_, ?_⟩
  · rw [KQState.okB_iff]
    refine ⟨h1, h2, h3, hna, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .black =
          false := by simpa [ht] using hopp
      simpa [KQState.inCheckB, KQState.kingIsAttacked_black_eq wk bk qs h1 h2 h3] using hopp'
    | black =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .white).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      simpa [KQState.inCheckB, KQState.kingIsAttacked_white_eq wk bk qs h1 h2 h3] using hopp'
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

theorem exists_kqState_black {p : Position} (hv : Valid p)
    {wk bk qs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ qs) (h3 : bk ≠ qs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .black)
    (_hc : p.castling = ∅) (_he : p.enPassant = none) :
    ∃ s : KQState, s.okB = true ∧ s.toPosition = p.rot180 := by
  let s : KQState := ⟨p.toMove.other, bk.rot180, wk.rot180, qs.rot180⟩
  refine ⟨s, ?_, ?_⟩
  · have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
    have h2' : wk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h2
    have h3' : bk.rot180 ≠ qs.rot180 := mt Board.rot180_injective h3
    have hna' : ¬ KingAttacks bk.rot180 wk.rot180 :=
      fun hk => hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
    rw [KQState.okB_iff]
    refine ⟨h1', h3', h2', hna', ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have : s.toMove.other = .white := by simp [s, ht]
      rw [this]
      simpa [s, KQState.inCheckB, KQState.kingAttackedWhite] using hna'
    | black =>
      have hopp' : (Board.kingsQueenBoard wk bk qs .black).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      have hiff := Board.kingsQueenBoard_kingIsAttacked_white wk bk qs .black h1 h2 h3
      have hn : ¬ (KingAttacks bk wk ∨
          (Color.black = .black ∧ QueenAttacks qs wk ∧ ¬ Between qs wk bk)) := by
        intro h'
        exact Bool.false_ne_true (hopp'.symm.trans (hiff.mpr h'))
      have : s.toMove.other = .black := by simp [s, ht]
      rw [this]
      unfold KQState.inCheckB KQState.kingAttackedBlack
      simp only [Bool.or_eq_false_iff]
      refine ⟨decide_eq_false (by simpa [s] using hna'), ?_⟩
      cases hrc : KQState.queenChecks s.qs s.bk s.wk
      · rfl
      · have ⟨hR, hnb⟩ := (KQState.queenChecks_iff s.qs s.bk s.wk).mp hrc
        exact False.elim (hn (Or.inr ⟨rfl,
          (Square.queenAttacks_rot180 qs wk).mpr (by simpa [s] using hR),
          mt (Square.between_rot180 qs wk bk).mp (by simpa [s] using hnb)⟩))
  · simp [s, KQState.toPosition, rot180, hboard,
      Board.rot180_kingsQueenBoard_black wk bk qs h1 h2 h3]

theorem exists_kqState {p : Position} (hv : Valid p) (h : IsKingAndQueen p) :
    (∃ s : KQState, s.okB = true ∧ s.toPosition = p) ∨
      (∃ s : KQState, s.okB = true ∧ s.toPosition = p.rot180) := by
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  cases c with
  | white => exact Or.inl (exists_kqState_white hv h1 h2 h3 hna hboard hc he)
  | black => exact Or.inr (exists_kqState_black hv h1 h2 h3 hna hboard hc he)

theorem IsKingAndQueen.checkmateReachable_of_not_dead {p : Position}
    (_hv : Valid p) (h : IsKingAndQueen p) {s : KQState}
    (hok : s.okB = true) (hnd : s.deadB = false)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p := by
  have hcr := KQState.checkmateReachable_of_okB_of_not_dead hok hnd
  rcases hpos with hpos | hpos
  · rwa [hpos] at hcr
  · rw [h.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem IsKingAndQueen.checkmateReachable_iff_deadB {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p) {s : KQState}
    (hok : s.okB = true)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p ↔ s.deadB = false := by
  constructor
  · intro hcr
    have hiff := KQState.checkmateReachable_iff_not_dead hok
    rcases hpos with hpos | hpos
    · rw [← hpos] at hcr
      exact hiff.mp hcr
    · rw [h.checkmateReachable_rot180] at hcr
      rw [← hpos] at hcr
      exact hiff.mp hcr
  · intro hnd
    exact h.checkmateReachable_of_not_dead hv hok hnd hpos

/-- If the player to move owns the queen, checkmate is reachable. -/
theorem IsKingAndQueen.checkmateReachable_of_queenToMove {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p)
    (hr : ∃ s, p.board s = some { color := p.toMove, kind := .queen }) :
    CheckmateReachable p := by
  have hKQ : IsKingAndQueen p := h
  obtain ⟨wk, bk, qs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have ht : p.toMove = c := by
    obtain ⟨sq, hsq⟩ := hr
    have hsqb : Board.kingsQueenBoard wk bk qs c sq =
        some { color := p.toMove, kind := .queen } := by rwa [hboard] at hsq
    have hsqrs : sq = qs := by
      unfold Board.kingsQueenBoard at hsqb
      split_ifs at hsqb <;>
        first | cases some_king_ne_queen hsqb | assumption
    rw [hsqrs, Board.kingsQueenBoard_queen wk bk qs c h2 h3] at hsqb
    injection hsqb with hpiece
    injection hpiece with hcol _
    exact hcol.symm
  cases c with
  | white =>
    obtain ⟨s, hok, hpos⟩ := exists_kqState_white hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, ht]
    have hcr := KQState.checkmateReachable_of_okB_white hok this
    rwa [hpos] at hcr
  | black =>
    obtain ⟨s, hok, hpos⟩ := exists_kqState_black hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, rot180_toMove, ht]
      rfl
    have hcr := KQState.checkmateReachable_of_okB_white hok this
    rw [hKQ.checkmateReachable_rot180]
    rwa [hpos] at hcr


theorem kq_ofPositionWhite?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPositionWhite? p = some s) :
    s.okB = true ∧ s.toPosition = p := by
  unfold KQState.ofPositionWhite? at h
  split at h
  · rename_i wk bk qs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      have hboard : p.board = Board.kingsQueenBoard wk bk qs .white := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KQState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      rfl
  · cases h

theorem kq_ofPositionBlack?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPositionBlack? p = some s) :
    s.okB = true ∧ s.toPosition = p.rot180 := by
  unfold KQState.ofPositionBlack? at h
  split at h
  · rename_i wk bk qs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      obtain ⟨h1s, h2s, h3s, _, _⟩ := (KQState.okB_iff _).mp hok
      have hwk_bk : wk ≠ bk := fun heq => h1s (by simp [heq])
      have hwk_qs : wk ≠ qs := fun heq => h3s (by simp [heq])
      have hbk_qs : bk ≠ qs := fun heq => h2s (by simp [heq])
      have hboard : p.board = Board.kingsQueenBoard wk bk qs .black := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KQState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      simp [KQState.toPosition, rot180,
        Board.rot180_kingsQueenBoard_black wk bk qs hwk_bk hwk_qs hbk_qs]
  · cases h

theorem kq_ofPositionWhite?_of_eq {p : Position} {s : KQState}
    (hok : s.okB = true) (hpos : s.toPosition = p) :
    KQState.ofPositionWhite? p = some s := by
  have hboard : p.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
    rw [← hpos]; rfl
  have htm : p.toMove = s.toMove := by
    have : s.toPosition.toMove = p.toMove := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  have hcst : p.castling = ∅ := by
    have : s.toPosition.castling = p.castling := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  have hep : p.enPassant = none := by
    have : s.toPosition.enPassant = p.enPassant := by rw [hpos]
    simpa [KQState.toPosition] using this.symm
  obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
  have hwk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.wk := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsQueenBoard_white])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.bk := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_black s.wk s.bk s.qs .white h1])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .queen }) = some s.qs := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_queen s.wk s.bk s.qs .white h2 h3])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_queen (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KQState.allSquares.all fun q =>
      p.board q == Board.kingsQueenBoard s.wk s.bk s.qs .white q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove, s.wk, s.bk, s.qs⟩ : KQState) = s := by
    cases s
    simp [htm]
  unfold KQState.ofPositionWhite?
  rw [hwk, hbk, hqs]
  simp [hs, hok, hall, hcst, hep]

theorem kq_ofPositionBlack?_of_eq {p : Position} {s : KQState}
    (hok : s.okB = true) (hpos : s.toPosition = p.rot180)
    (hcst : p.castling = ∅) (hep : p.enPassant = none) :
    KQState.ofPositionBlack? p = some s := by
  obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
  have hboardR : p.rot180.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
    rw [← hpos]; rfl
  have hboard : p.board =
      Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180 .black := by
    have hrot := congrArg Board.rot180 hboardR
    rw [rot180_board, Board.board_rot180_involutive,
      Board.rot180_kingsQueenBoard_white s.wk s.bk s.qs h1 h2 h3] at hrot
    exact hrot
  have htm : p.toMove.other = s.toMove := by
    have : s.toPosition.toMove = p.rot180.toMove := by rw [hpos]
    simpa [KQState.toPosition, rot180_toMove] using this.symm
  have hneWB : s.bk.rot180 ≠ s.wk.rot180 := Ne.symm (mt Board.rot180_injective h1)
  have hneWR : s.wk.rot180 ≠ s.qs.rot180 := mt Board.rot180_injective h2
  have hneBR : s.bk.rot180 ≠ s.qs.rot180 := mt Board.rot180_injective h3
  have hwk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.bk.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsQueenBoard_white])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.wk.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_black s.bk.rot180 s.wk.rot180 s.qs.rot180
          .black hneWB])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .queen }) = some s.qs.rot180 := by
    refine find?_eq_some_of_unique (KQState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsQueenBoard_queen s.bk.rot180 s.wk.rot180 s.qs.rot180
          .black hneBR hneWR])
    · intro q _ hq
      exact Board.kingsQueenBoard_eq_queen (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KQState.allSquares.all fun q =>
      p.board q == Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180
        .black q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove.other, s.wk, s.bk, s.qs⟩ : KQState) = s := by
    cases s
    simp [htm]
  unfold KQState.ofPositionBlack?
  rw [hwk, hbk, hqs]
  simp [Square.rot180_involutive, hs, hok, hall, hcst, hep]

theorem kq_ofPositionWhite?_eq_none_of_black {p : Position} {wk bk qs : Square}
    (hboard : p.board = Board.kingsQueenBoard wk bk qs .black) :
    KQState.ofPositionWhite? p = none := by
  have hqs : KQState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .queen }) = none := by
    refine List.find?_eq_none.mpr ?_
    intro q _
    cases hb : (p.board q == some { color := .white, kind := .queen })
    · exact Bool.false_ne_true
    · have heq : p.board q = some { color := .white, kind := .queen } :=
        beq_iff_eq.mp hb
      rw [hboard] at heq
      unfold Board.kingsQueenBoard at heq
      split_ifs at heq <;> cases heq
  unfold KQState.ofPositionWhite?
  rw [hqs]
  split
  · rename_i _ _ _ heq
    cases heq
  · rfl

theorem kq_ofPosition?_eq_some {p : Position} {s : KQState}
    (h : KQState.ofPosition? p = some s) :
    s.okB = true ∧ (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  unfold KQState.ofPosition? at h
  split at h
  · rename_i s' hW
    injection h with hs
    subst hs
    have ⟨hok, hpos⟩ := kq_ofPositionWhite?_eq_some hW
    exact ⟨hok, Or.inl hpos⟩
  · have ⟨hok, hpos⟩ := kq_ofPositionBlack?_eq_some h
    exact ⟨hok, Or.inr hpos⟩

theorem kq_ofPosition?_complete {p : Position} (hv : Valid p) (h : IsKingAndQueen p) :
    ∃ s, KQState.ofPosition? p = some s ∧ s.okB = true ∧
      (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  rcases exists_kqState hv h with ⟨s, hok, hpos⟩ | ⟨s, hok, hpos⟩
  · refine ⟨s, ?_, hok, Or.inl hpos⟩
    unfold KQState.ofPosition?
    rw [kq_ofPositionWhite?_of_eq hok hpos]
  · refine ⟨s, ?_, hok, Or.inr hpos⟩
    obtain ⟨h1, h2, h3, _, _⟩ := (KQState.okB_iff s).mp hok
    have hboardR : p.rot180.board = Board.kingsQueenBoard s.wk s.bk s.qs .white := by
      rw [← hpos]; rfl
    have hboard : p.board =
        Board.kingsQueenBoard s.bk.rot180 s.wk.rot180 s.qs.rot180 .black := by
      have hrot := congrArg Board.rot180 hboardR
      rw [rot180_board, Board.board_rot180_involutive,
        Board.rot180_kingsQueenBoard_white s.wk s.bk s.qs h1 h2 h3] at hrot
      exact hrot
    unfold KQState.ofPosition?
    rw [kq_ofPositionWhite?_eq_none_of_black hboard,
      kq_ofPositionBlack?_of_eq hok hpos h.castling_eq h.enPassant_eq]

/-- The engineered mating line of a king-and-queen versus king position;
`[]` when the position is dead or not of this material. Black-queen
positions are rotated into the white-queen frame, and the resulting moves
are rotated back. -/
def kingQueenMatingLine (p : Position) : List Move :=
  match KQState.ofPositionWhite? p with
  | some s => s.matingLine
  | none =>
    match KQState.ofPositionBlack? p with
    | some s => s.matingLine.map Move.rot180
    | none => []

/-- Whether a king-and-queen versus king position is dead for helpmate
(`true` when the board is not of this material). -/
def kingQueenDead (p : Position) : Bool :=
  match KQState.ofPosition? p with
  | some s => s.deadB
  | none => true

/-- In a valid king-and-queen versus king position, checkmate is reachable
exactly when the corresponding three-piece state is not dead. -/
theorem IsKingAndQueen.checkmateReachable_iff {p : Position}
    (hv : Valid p) (h : IsKingAndQueen p) :
    CheckmateReachable p ↔ kingQueenDead p = false := by
  obtain ⟨s, hs, hok, hpos⟩ := kq_ofPosition?_complete hv h
  have hdeq : kingQueenDead p = s.deadB := by simp [kingQueenDead, hs]
  rw [hdeq]
  exact h.checkmateReachable_iff_deadB hv hok hpos

/-- Decides whether checkmate is reachable from a valid king-and-queen
versus king position: exactly when the corresponding three-piece state
is not dead. -/
def kingQueenCheckmateReachable (p : Position) (hv : Valid p)
    (h : IsKingAndQueen p) : Decidable (CheckmateReachable p) :=
  decidable_of_iff (kingQueenDead p = false) (h.checkmateReachable_iff hv).symm

/-! ### Example: kings on `e1` and `e8`, white queen on `a1` -/

/-- White king on `e1`, black king on `e8`, white queen on `a1`, White to
move. -/
def kingQueenStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.a1 then some { color := .white, kind := .queen }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingQueenStart_isValid : isValid kingQueenStart = true := by
  native_decide

theorem kingQueenStart_valid : Valid kingQueenStart :=
  (isValid_eq_true_iff _).mp kingQueenStart_isValid

theorem kingQueenStart_isKingAndQueen : IsKingAndQueen kingQueenStart :=
  isKingAndQueen_of_valid kingQueenStart_valid (by native_decide)
    ⟨Square.a1, Color.white, by native_decide⟩ (by native_decide)

theorem kingQueenStart_CheckmateReachable : CheckmateReachable kingQueenStart :=
  kingQueenStart_isKingAndQueen.checkmateReachable_of_queenToMove kingQueenStart_valid
    ⟨Square.a1, by native_decide⟩

theorem kingQueenStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingQueenStart)
      (kingQueenCheckmateReachable kingQueenStart kingQueenStart_valid
        kingQueenStart_isKingAndQueen) = true := by
  native_decide

theorem kingQueenStart_not_deadPosition : ¬ DeadPosition kingQueenStart :=
  not_deadPosition_of_checkmateReachable kingQueenStart_CheckmateReachable

theorem kingQueenStart_matingLine_legal :
    pathLegal kingQueenStart (kingQueenMatingLine kingQueenStart) = true := by
  native_decide

theorem kingQueenStart_matingLine_inCheckmate :
    (playSeq kingQueenStart (kingQueenMatingLine kingQueenStart)).inCheckmate = true := by
  native_decide

theorem kingQueenStart_CheckmateReachable' : CheckmateReachable kingQueenStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingQueenStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingQueenStart_matingLine_inCheckmate)

/-- Forced capture of an unprotected queen: Black to move, in check, and
the only legal move takes the queen, leaving two kings. -/
def queenForcedCapture : Position where
  board := fun s =>
    if s = Square.c8 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .queen }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem queenForcedCapture_isValid : isValid queenForcedCapture = true := by
  native_decide

theorem queenForcedCapture_valid : Valid queenForcedCapture :=
  (isValid_eq_true_iff _).mp queenForcedCapture_isValid

theorem queenForcedCapture_isKingAndQueen : IsKingAndQueen queenForcedCapture :=
  isKingAndQueen_of_valid queenForcedCapture_valid (by native_decide)
    ⟨Square.a7, Color.white, by native_decide⟩ (by native_decide)

theorem queenForcedCapture_deadB : ∃ s : KQState, s.okB = true ∧
    s.toPosition = queenForcedCapture ∧ s.deadB = true := by
  refine ⟨⟨.black, Square.c8, Square.a8, Square.a7⟩, by native_decide, ?_,
    by native_decide⟩
  have hboard : Board.kingsQueenBoard Square.c8 Square.a8 Square.a7 .white =
      queenForcedCapture.board := by
    funext q
    simp [queenForcedCapture, Board.kingsQueenBoard]
  simp [KQState.toPosition, queenForcedCapture, hboard, CastlingRights.empty]

theorem queenForcedCapture_not_CheckmateReachable :
    ¬ CheckmateReachable queenForcedCapture := by
  obtain ⟨s, hok, hpos, hd⟩ := queenForcedCapture_deadB
  intro hcr
  have := (queenForcedCapture_isKingAndQueen.checkmateReachable_iff_deadB
    queenForcedCapture_valid hok (Or.inl hpos)).mp hcr
  exact Bool.false_ne_true (this.symm.trans hd)

theorem queenForcedCapture_decide_CheckmateReachable :
    @decide (CheckmateReachable queenForcedCapture)
      (kingQueenCheckmateReachable queenForcedCapture queenForcedCapture_valid
        queenForcedCapture_isKingAndQueen) = false := by
  native_decide

theorem queenStalemate_isKingAndQueen : IsKingAndQueen queenStalemate :=
  isKingAndQueen_of_valid
    ((isValid_eq_true_iff queenStalemate).mp queenStalemate_isValid)
    (by native_decide) ⟨Square.f7, Color.white, by native_decide⟩ (by native_decide)

theorem queenStalemate_not_CheckmateReachable :
    ¬ CheckmateReachable queenStalemate :=
  not_CheckmateReachable_of_InStalemate
    ((inStalemate_eq_true_iff _).mp queenStalemate_inStalemate)

theorem queenStalemate_decide_CheckmateReachable :
    @decide (CheckmateReachable queenStalemate)
      (kingQueenCheckmateReachable queenStalemate
        ((isValid_eq_true_iff queenStalemate).mp queenStalemate_isValid)
        queenStalemate_isKingAndQueen) = false := by
  native_decide

theorem queenStalemate_deadPosition : DeadPosition queenStalemate :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr
    queenStalemate_not_CheckmateReachable

/-- The known `h7` mate is king-and-queen versus king, already checkmate. -/
theorem queenMate_isKingAndQueen : IsKingAndQueen queenMate :=
  isKingAndQueen_of_valid
    ((isValid_eq_true_iff queenMate).mp queenMate_isValid)
    (by native_decide) ⟨Square.h7, Color.white, by native_decide⟩ (by native_decide)

theorem queenMate_CheckmateReachable : CheckmateReachable queenMate :=
  checkmateReachable_of_inCheckmate
    ((inCheckmate_eq_true_iff _).mp queenMate_inCheckmate)

theorem queenMate_decide_CheckmateReachable :
    @decide (CheckmateReachable queenMate)
      (kingQueenCheckmateReachable queenMate
        ((isValid_eq_true_iff queenMate).mp queenMate_isValid)
        queenMate_isKingAndQueen) = true := by
  native_decide

theorem queenMate_matingLine_legal :
    pathLegal queenMate (kingQueenMatingLine queenMate) = true := by
  native_decide

theorem queenMate_matingLine_inCheckmate :
    (playSeq queenMate (kingQueenMatingLine queenMate)).inCheckmate = true := by
  native_decide

end Position

end Chess



