import Chess.KingBishop
import Chess.EndsGame

/-!
# King and rook versus king

A valid position whose board holds only the two kings and one rook is
king-and-rook versus king. Unlike king versus king, or king-and-bishop
versus king, checkmate is possible: the classic picture is the lone king
on the edge, the supporting king two squares away, and the rook checking
from the same rank or file, covering the flights.

Checkmate is not *always* reachable. If the lone king is to move in
stalemate, or its only legal move is to capture an unprotected rook, the
position is dead: every continuation is either that same dead position or
a two-king position, from which checkmate is unreachable. When the rook
side is to move they are never in check (the only enemy piece is the
lone king, and adjacent kings are illegal), so they always have a legal
rook move and the position is not dead.

This module shows that from every other legal king-and-rook versus king
position, checkmate is reachable by cooperative play (a helpmate, not a
forced win). The two sides steer into one known mating picture:

* white king on `g6`, black king on `h8` or `g8`,
* white rook on the eighth rank (typically `a8`),
* Black to move, in check, with no flight.

A potential `KRState.mu` measures the distance of the three pieces from
that picture (a route for the black king that avoids the white king's
neighborhood, a penalty for parking the rook on `a8` before Black has
reached the eighth rank, and a bonus for being in check). The main
theorem shows every legal state is checkmate, is dead, or reaches by a
short legal sequence a non-dead state of strictly smaller potential.
Strong induction on the potential gives `CheckmateReachable` for every
non-dead state.

The exhaustive check is the Boolean `KRState.checkAll`, verified by
`native_decide`. It examines each of the `2 · 64³` three-piece
placements once; it is not a search for mate. Captures of the rook are
excluded from the policy: they leave two kings.

States are stored in a *white-rook frame*: White owns the rook. A
position in which Black owns the rook is reduced by a 180° rotation and
a color swap. `kingRookCheckmateReachable` decides `CheckmateReachable`
for a valid king-and-rook versus king position, and `kingRookMatingLine`
produces a concrete mating sequence (or `[]` when the position is dead
or not of this material).
-/

namespace Chess

namespace Square

/-- 180° rotation of the board: `a1` maps to `h8`. -/
def rot180 (s : Square) : Square :=
  ⟨⟨7 - s.file.val, by
      have := Nat.le_of_lt_succ s.file.isLt
      omega⟩,
    ⟨7 - s.rank.val, by
      have := Nat.le_of_lt_succ s.rank.isLt
      omega⟩⟩

@[simp] theorem rot180_involutive (s : Square) : s.rot180.rot180 = s := by
  rcases s with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [rot180]
  constructor <;> omega

theorem kingAttacks_rot180 (s t : Square) :
    KingAttacks s t ↔ KingAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem rookAttacks_rot180 (s t : Square) :
    RookAttacks s t ↔ RookAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem between_rot180 (s t u : Square) :
    Between s t u ↔ Between s.rot180 t.rot180 u.rot180 := by
  revert s t u
  native_decide

theorem bishopAttacks_rot180 (s t : Square) :
    BishopAttacks s t ↔ BishopAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem knightAttacks_rot180 (s t : Square) :
    KnightAttacks s t ↔ KnightAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem queenAttacks_rot180 (s t : Square) :
    QueenAttacks s t ↔ QueenAttacks s.rot180 t.rot180 := by
  revert s t
  native_decide

theorem pawnAttacks_rot180 (c : Color) (s t : Square) :
    PawnAttacks c s t ↔ PawnAttacks c.other s.rot180 t.rot180 := by
  revert c s t
  native_decide

end Square

namespace Piece

/-- Swap the owner of a piece, keeping its kind. -/
def flip (p : Piece) : Piece :=
  { color := p.color.other, kind := p.kind }

@[simp] theorem flip_flip (p : Piece) : p.flip.flip = p := by
  rcases p with ⟨c, k⟩
  cases c <;> rfl

@[simp] theorem flip_color (p : Piece) : p.flip.color = p.color.other := rfl

@[simp] theorem flip_kind (p : Piece) : p.flip.kind = p.kind := rfl

end Piece

namespace Board

/-- White king on `wk`, black king on `bk`, and a rook of color `c` on
`rs`. -/
def kingsRookBoard (wk bk rs : Square) (c : Color) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else if s = rs then some { color := c, kind := .rook }
  else none

theorem kingsRookBoard_white (wk bk rs : Square) (c : Color) :
    kingsRookBoard wk bk rs c wk = some { color := .white, kind := .king } := by
  simp [kingsRookBoard]

theorem kingsRookBoard_black (wk bk rs : Square) (c : Color) (h : wk ≠ bk) :
    kingsRookBoard wk bk rs c bk = some { color := .black, kind := .king } := by
  simp [kingsRookBoard, h.symm]

theorem kingsRookBoard_rook (wk bk rs : Square) (c : Color)
    (hw : wk ≠ rs) (hb : bk ≠ rs) :
    kingsRookBoard wk bk rs c rs = some { color := c, kind := .rook } := by
  simp [kingsRookBoard, hw.symm, hb.symm]

theorem kingsRookBoard_other (wk bk rs s : Square) (c : Color)
    (hw : s ≠ wk) (hb : s ≠ bk) (hrs : s ≠ rs) :
    kingsRookBoard wk bk rs c s = none := by
  simp [kingsRookBoard, hw, hb, hrs]

theorem kingsRookBoard_eq_white_king {wk bk rs s : Square} {c : Color}
    (h : kingsRookBoard wk bk rs c s = some { color := .white, kind := .king }) :
    s = wk := by
  unfold kingsRookBoard at h
  split_ifs at h <;> simp_all

theorem kingsRookBoard_eq_black_king {wk bk rs s : Square} {c : Color}
    (h : kingsRookBoard wk bk rs c s = some { color := .black, kind := .king }) :
    s = bk := by
  unfold kingsRookBoard at h
  split_ifs at h <;> simp_all

theorem kingsRookBoard_eq_rook {wk bk rs s : Square} {c : Color}
    (h : kingsRookBoard wk bk rs c s = some { color := c, kind := .rook }) :
    s = rs := by
  unfold kingsRookBoard at h
  split_ifs at h <;> simp_all

theorem kingsRookBoard_isSome (wk bk rs s : Square) (c : Color) :
    ((kingsRookBoard wk bk rs c) s).isSome = true ↔
      s = wk ∨ s = bk ∨ s = rs := by
  unfold kingsRookBoard
  split_ifs <;> simp_all

theorem attacks_rook_iff {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .rook }) :
    b.attacks s t = true ↔
      RookAttacks s t ∧
        ¬ ∃ u : Square, Between s t u ∧ (b u).isSome = true := by
  unfold attacks
  rw [h]
  simp only [PieceKind.rook_isSlider, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_iff, decide_eq_false_iff_not]

theorem kingsRookBoard_rook_blocked {wk bk rs t : Square} {c : Color} :
    (∃ u : Square, Between rs t u ∧
        ((kingsRookBoard wk bk rs c) u).isSome = true) ↔
      Between rs t wk ∨ Between rs t bk := by
  constructor
  · intro ⟨u, hB, hocc⟩
    have hu : u = wk ∨ u = bk ∨ u = rs :=
      (kingsRookBoard_isSome wk bk rs u c).mp hocc
    rcases hu with hu | hu | hu
    · subst u; exact Or.inl hB
    · subst u; exact Or.inr hB
    · subst u
      exact (hB.1 rfl).elim
  · intro h
    cases h with
    | inl hB =>
      exact ⟨wk, hB, (kingsRookBoard_isSome wk bk rs wk c).mpr (Or.inl rfl)⟩
    | inr hB =>
      exact ⟨bk, hB, (kingsRookBoard_isSome wk bk rs bk c).mpr (Or.inr (Or.inl rfl))⟩

theorem kingsRookBoard_attacks_rook_iff {wk bk rs t : Square} {c : Color}
    (hw : wk ≠ rs) (hb : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).attacks rs t = true ↔
      RookAttacks rs t ∧ ¬ Between rs t wk ∧ ¬ Between rs t bk := by
  rw [attacks_rook_iff (kingsRookBoard_rook wk bk rs c hw hb),
    kingsRookBoard_rook_blocked]
  tauto

theorem kingsRookBoard_occupiedBy_white (wk bk rs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_rs : wk ≠ rs) (_hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).occupiedBy .white =
      match c with
      | .white => {wk, rs}
      | .black => {wk} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsRookBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsRookBoard
    split_ifs <;> simp_all

theorem kingsRookBoard_occupiedBy_black (wk bk rs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_rs : wk ≠ rs) (_hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).occupiedBy .black =
      match c with
      | .white => {bk}
      | .black => {bk, rs} := by
  cases c <;> ext s
  · simp only [mem_occupiedBy, Finset.mem_singleton]
    unfold kingsRookBoard
    split_ifs <;> simp_all
  · simp only [mem_occupiedBy, Finset.mem_insert, Finset.mem_singleton]
    unfold kingsRookBoard
    split_ifs <;> simp_all

theorem kingsRookBoard_kingSquares_white (wk bk rs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_rs : wk ≠ rs) (_hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsRookBoard
  split_ifs <;> simp_all

theorem kingsRookBoard_kingSquares_black (wk bk rs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_rs : wk ≠ rs) (_hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  unfold kingsRookBoard
  split_ifs <;> simp_all

theorem kingsRookBoard_occupied (wk bk rs : Square) (c : Color)
    (_hwk_bk : wk ≠ bk) (_hwk_rs : wk ≠ rs) (_hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).occupied = {wk, bk, rs} := by
  ext s
  simp only [mem_occupied, Finset.mem_insert, Finset.mem_singleton]
  unfold kingsRookBoard
  split_ifs <;> simp_all

theorem kingsRookBoard_black_piece {wk bk rs s : Square} {c : Color}
    (h : (kingsRookBoard wk bk rs c s).map (·.color) = some .black) :
    s = bk ∨ (c = .black ∧ s = rs) := by
  unfold kingsRookBoard at h
  split_ifs at h <;> simp_all

theorem kingsRookBoard_white_piece {wk bk rs s : Square} {c : Color}
    (h : (kingsRookBoard wk bk rs c s).map (·.color) = some .white) :
    s = wk ∨ (c = .white ∧ s = rs) := by
  unfold kingsRookBoard at h
  split_ifs at h <;> simp_all

theorem kingsRookBoard_kingIsAttacked_white (wk bk rs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_rs : wk ≠ rs) (hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).kingIsAttacked .white = true ↔
      KingAttacks bk wk ∨
        (c = .black ∧ RookAttacks rs wk ∧ ¬ Between rs wk bk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsRookBoard_kingSquares_white wk bk rs c hwk_bk hwk_rs hbk_rs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsRookBoard_black_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsRookBoard_black wk bk rs c hwk_bk)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsRookBoard_attacks_rook_iff (t := wk) (c := Color.black)
        hwk_rs hbk_rs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.2⟩
  · intro h
    rcases h with hk | ⟨hc, hR, hnb⟩
    · refine ⟨bk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsRookBoard_black wk bk rs c hwk_bk]
      · rw [attacks_king (kingsRookBoard_black wk bk rs c hwk_bk)]
        exact decide_eq_true hk
    · refine ⟨rs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsRookBoard_rook wk bk rs Color.black hwk_rs hbk_rs]
      · subst hc
        rw [kingsRookBoard_attacks_rook_iff (t := wk) (c := Color.black)
          hwk_rs hbk_rs]
        exact ⟨hR, fun hBet => (hBet.2.1 rfl).elim, hnb⟩

theorem kingsRookBoard_kingIsAttacked_black (wk bk rs : Square) (c : Color)
    (hwk_bk : wk ≠ bk) (hwk_rs : wk ≠ rs) (hbk_rs : bk ≠ rs) :
    (kingsRookBoard wk bk rs c).kingIsAttacked .black = true ↔
      KingAttacks wk bk ∨
        (c = .white ∧ RookAttacks rs bk ∧ ¬ Between rs bk wk) := by
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsRookBoard_kingSquares_black wk bk rs c hwk_bk hwk_rs hbk_rs,
    Finset.mem_singleton, exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hpiece := kingsRookBoard_white_piece hcol
    rcases hpiece with hseq | ⟨hc, hseq⟩
    · rw [hseq] at hatt
      rw [attacks_king (kingsRookBoard_white wk bk rs c)] at hatt
      exact Or.inl (of_decide_eq_true hatt)
    · rw [hseq, hc] at hatt
      rw [kingsRookBoard_attacks_rook_iff (t := bk) (c := Color.white)
        hwk_rs hbk_rs] at hatt
      exact Or.inr ⟨hc, hatt.1, hatt.2.1⟩
  · intro h
    rcases h with hk | ⟨hc, hR, hnb⟩
    · refine ⟨wk, ?_⟩
      rw [mem_attackers]
      constructor
      · simp [kingsRookBoard_white]
      · rw [attacks_king (kingsRookBoard_white wk bk rs c)]
        exact decide_eq_true hk
    · refine ⟨rs, ?_⟩
      rw [mem_attackers]
      constructor
      · subst hc
        simp [kingsRookBoard_rook wk bk rs Color.white hwk_rs hbk_rs]
      · subst hc
        rw [kingsRookBoard_attacks_rook_iff (t := bk) (c := Color.white)
          hwk_rs hbk_rs]
        exact ⟨hR, hnb, fun hBet => (hBet.2.1 rfl).elim⟩

theorem relocate_kingsRookBoard_white (wk bk rs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ rs) (_hbr : bk ≠ rs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ rs) :
    (kingsRookBoard wk bk rs c).relocate wk dst { color := .white, kind := .king } =
      kingsRookBoard dst bk rs c := by
  funext s
  unfold relocate kingsRookBoard
  split_ifs <;> simp_all

theorem relocate_kingsRookBoard_black (wk bk rs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ rs) (_hbr : bk ≠ rs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ rs) :
    (kingsRookBoard wk bk rs c).relocate bk dst { color := .black, kind := .king } =
      kingsRookBoard wk dst rs c := by
  funext s
  unfold relocate kingsRookBoard
  split_ifs <;> simp_all

theorem relocate_kingsRookBoard_rook (wk bk rs dst : Square) (c : Color)
    (_hne : wk ≠ bk) (_hwr : wk ≠ rs) (_hbr : bk ≠ rs)
    (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) (_hdr : dst ≠ rs) :
    (kingsRookBoard wk bk rs c).relocate rs dst { color := c, kind := .rook } =
      kingsRookBoard wk bk dst c := by
  funext s
  unfold relocate kingsRookBoard
  split_ifs <;> simp_all

theorem relocate_capture_rook_black (wk bk rs : Square)
    (_hne : wk ≠ bk) (_hwr : wk ≠ rs) (_hbr : bk ≠ rs) :
    (kingsRookBoard wk bk rs .white).relocate bk rs
      { color := .black, kind := .king } =
      kingsBoard wk rs := by
  funext s
  unfold relocate kingsRookBoard kingsBoard
  split_ifs <;> simp_all

theorem relocate_capture_rook_white (wk bk rs : Square)
    (_hne : wk ≠ bk) (_hwr : wk ≠ rs) (_hbr : bk ≠ rs) :
    (kingsRookBoard wk bk rs .black).relocate wk rs
      { color := .white, kind := .king } =
      kingsBoard rs bk := by
  funext s
  unfold relocate kingsRookBoard kingsBoard
  split_ifs <;> simp_all

/-- Rotate the board 180° and swap colors. -/
def rot180 (b : Board) : Board :=
  fun s => (b s.rot180).map Piece.flip

theorem rot180_eq_iff {s t : Square} : s.rot180 = t ↔ s = t.rot180 := by
  constructor
  · intro h
    rw [← Square.rot180_involutive s, h]
  · intro h
    rw [h, Square.rot180_involutive]

theorem rot180_injective {s t : Square} (h : s.rot180 = t.rot180) : s = t := by
  rw [← Square.rot180_involutive s, h, Square.rot180_involutive]

theorem rot180_kingsRookBoard_white (wk bk rs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) :
    (kingsRookBoard wk bk rs .white).rot180 =
      kingsRookBoard bk.rot180 wk.rot180 rs.rot180 .black := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_rs : wk.rot180 ≠ rs.rot180 := mt rot180_injective h2
  have hbk_rs : bk.rot180 ≠ rs.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsRookBoard_white wk bk rs Color.white]
    change some { color := Color.black, kind := .king } =
      kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.black wk.rot180
    rw [kingsRookBoard_black bk.rot180 wk.rot180 rs.rot180 Color.black hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsRookBoard_black wk bk rs Color.white h1]
      change some { color := Color.white, kind := .king } =
        kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.black bk.rot180
      rw [kingsRookBoard_white bk.rot180 wk.rot180 rs.rot180 Color.black]
    · by_cases hR : s.rot180 = rs
      · have hs : s = rs.rot180 := rot180_eq_iff.mp hR
        rw [hR, hs, kingsRookBoard_rook wk bk rs Color.white h2 h3]
        change some { color := Color.black, kind := .rook } =
          kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.black rs.rot180
        rw [kingsRookBoard_rook bk.rot180 wk.rot180 rs.rot180 Color.black hbk_rs hwk_rs]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsR : s ≠ rs.rot180 := fun h => hR (rot180_eq_iff.mpr h)
        rw [kingsRookBoard_other wk bk rs s.rot180 Color.white hA hB hR]
        change none = kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.black s
        rw [kingsRookBoard_other bk.rot180 wk.rot180 rs.rot180 s Color.black hsB hsW hsR]

theorem rot180_kingsRookBoard_black (wk bk rs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) :
    (kingsRookBoard wk bk rs .black).rot180 =
      kingsRookBoard bk.rot180 wk.rot180 rs.rot180 .white := by
  funext s
  have hwk_bk : bk.rot180 ≠ wk.rot180 := mt rot180_injective (Ne.symm h1)
  have hwk_rs : wk.rot180 ≠ rs.rot180 := mt rot180_injective h2
  have hbk_rs : bk.rot180 ≠ rs.rot180 := mt rot180_injective h3
  unfold rot180 Piece.flip
  by_cases hA : s.rot180 = wk
  · have hs : s = wk.rot180 := rot180_eq_iff.mp hA
    rw [hA, hs, kingsRookBoard_white wk bk rs Color.black]
    change some { color := Color.black, kind := .king } =
      kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.white wk.rot180
    rw [kingsRookBoard_black bk.rot180 wk.rot180 rs.rot180 Color.white hwk_bk]
  · by_cases hB : s.rot180 = bk
    · have hs : s = bk.rot180 := rot180_eq_iff.mp hB
      rw [hB, hs, kingsRookBoard_black wk bk rs Color.black h1]
      change some { color := Color.white, kind := .king } =
        kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.white bk.rot180
      rw [kingsRookBoard_white bk.rot180 wk.rot180 rs.rot180 Color.white]
    · by_cases hR : s.rot180 = rs
      · have hs : s = rs.rot180 := rot180_eq_iff.mp hR
        rw [hR, hs, kingsRookBoard_rook wk bk rs Color.black h2 h3]
        change some { color := Color.white, kind := .rook } =
          kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.white rs.rot180
        rw [kingsRookBoard_rook bk.rot180 wk.rot180 rs.rot180 Color.white hbk_rs hwk_rs]
      · have hsW : s ≠ wk.rot180 := fun h => hA (rot180_eq_iff.mpr h)
        have hsB : s ≠ bk.rot180 := fun h => hB (rot180_eq_iff.mpr h)
        have hsR : s ≠ rs.rot180 := fun h => hR (rot180_eq_iff.mpr h)
        rw [kingsRookBoard_other wk bk rs s.rot180 Color.black hA hB hR]
        change none = kingsRookBoard bk.rot180 wk.rot180 rs.rot180 Color.white s
        rw [kingsRookBoard_other bk.rot180 wk.rot180 rs.rot180 s Color.white hsB hsW hsR]

theorem board_rot180_involutive (b : Board) : b.rot180.rot180 = b := by
  funext s
  unfold rot180
  rw [Square.rot180_involutive]
  cases h : b s with
  | none => simp
  | some p => simp [Piece.flip_flip]

theorem relocate_rot180 (b : Board) (src dst : Square) (p : Piece) :
    (b.relocate src dst p).rot180 =
      b.rot180.relocate src.rot180 dst.rot180 p.flip := by
  funext x
  have hiff : src = dst ↔ src.rot180 = dst.rot180 :=
    ⟨fun h => h ▸ rfl, rot180_injective⟩
  unfold relocate rot180
  by_cases h1 : x.rot180 = dst
  · have hx : x = dst.rot180 := rot180_eq_iff.mp h1
    simp [hx]
  · by_cases h2 : x.rot180 = src
    · have hx : x = src.rot180 := rot180_eq_iff.mp h2
      have hxdst : x ≠ dst.rot180 := fun h => h1 (rot180_eq_iff.mpr h)
      simp [hx, hiff]
    · have hxdst : x ≠ dst.rot180 := fun h => h1 (rot180_eq_iff.mpr h)
      have hxsrc : x ≠ src.rot180 := fun h => h2 (rot180_eq_iff.mpr h)
      simp [h1, h2, hxdst, hxsrc]

end Board

namespace Position

/-- Board after a non-promoting rook move. -/
theorem boardAfter_rook (p : Position) (m : Move) {c : Color}
    (hpromo : m.promotion = none) :
    p.boardAfter m { color := c, kind := .rook } =
      p.board.relocate m.src m.dst { color := c, kind := .rook } := by
  unfold boardAfter
  simp [hpromo]

theorem enPassantAfter_rook (m : Move) (c : Color) (b : Board) :
    enPassantAfter m { color := c, kind := .rook } b = none := by
  unfold enPassantAfter
  simp

theorem some_rook_ne_pawn {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .rook } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

theorem some_rook_ne_king {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .rook } : Option Piece) =
      some { color := c₂, kind := .king }) : False := by
  simp at h

/-- `p` contains only two kings and one rook, with the kings not
adjacent, no remaining castling rights, and no en passant target. -/
def IsKingAndRook (p : Position) : Prop :=
  ∃ wk bk rs : Square, ∃ c : Color,
    wk ≠ bk ∧
      wk ≠ rs ∧
      bk ≠ rs ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsRookBoard wk bk rs c ∧
      p.castling = ∅ ∧
      p.enPassant = none

/-- 180° rotation of a position: pieces move with the board and swap
color, and the side to move is flipped. Castling rights and en passant
are cleared (they are already empty on king-and-rook positions). -/
def rot180 (p : Position) : Position where
  board := p.board.rot180
  toMove := p.toMove.other
  castling := ∅
  enPassant := none

theorem rot180_board (p : Position) : p.rot180.board = p.board.rot180 := rfl

theorem rot180_toMove (p : Position) : p.rot180.toMove = p.toMove.other := rfl

theorem rot180_involutive {p : Position}
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    p.rot180.rot180 = p := by
  rcases p with ⟨b, tm, cst, ep⟩
  refine Position.ext ?_ ?_ ?_ ?_
  · simp [rot180, Board.board_rot180_involutive]
  · simp [rot180]
  · simpa [rot180] using hc.symm
  · simpa [rot180] using he.symm

theorem destOk_kingsRookBoard {p : Position} {m : Move} {wk bk rs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsRookBoard wk bk rs c)
    (hok : p.destOk m = true) :
    p.board m.dst = none ∨ m.dst = rs := by
  unfold destOk at hok
  rw [hboard] at hok
  cases hdst : Board.kingsRookBoard wk bk rs c m.dst with
  | none =>
    exact Or.inl (by rw [hboard, hdst])
  | some q =>
    simp only [hdst, Bool.and_eq_true] at hok
    have hneK : q.kind ≠ PieceKind.king := bne_iff_ne.mp hok.2
    unfold Board.kingsRookBoard at hdst
    split_ifs at hdst with h1 h2 h3
    · cases hdst; exact (hneK rfl).elim
    · cases hdst; exact (hneK rfl).elim
    · exact Or.inr h3

theorem destOk_toMove_of_dst_rook {p : Position} {m : Move}
    {wk bk rs : Square} {c : Color}
    (hboard : p.board = Board.kingsRookBoard wk bk rs c)
    (hwk_rs : wk ≠ rs) (hbk_rs : bk ≠ rs)
    (hdst : m.dst = rs) (hok : p.destOk m = true) :
    p.toMove = c.other := by
  unfold destOk at hok
  rw [hdst, hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs] at hok
  simp only [Bool.and_eq_true, bne_iff_ne] at hok
  exact eq_other_of_ne_color (Ne.symm hok.1)

theorem kingRook_legalMove_core {p : Position} {m : Move} {wk bk rs : Square}
    {c : Color}
    (hboard : p.board = Board.kingsRookBoard wk bk rs c)
    (hcstl : p.castling = ∅)
    (hm : LegalMove p m) :
    m.promotion = none ∧
      p.destOk m = true ∧
      (p.board m.dst = none ∨ m.dst = rs) ∧
      (p.play m).board.kingIsAttacked p.toMove = false ∧
      p.board.attacks m.src m.dst = true ∧
      ∃ piece, p.board m.src = some piece ∧ piece.color = p.toMove ∧
        (piece.kind = .king ∨ piece.kind = .rook) ∧
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
    have hdstOr := destOk_kingsRookBoard hboard hdestOk
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    have hsrc : Board.kingsRookBoard wk bk rs c m.src = some piece := by
      rw [← hboard, hsrcB]
    have hkind : piece.kind = .king ∨ piece.kind = .rook := by
      have hsrc' := hsrc
      unfold Board.kingsRookBoard at hsrc'
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

namespace Move

/-- 180° rotation of a move. -/
def rot180 (m : Move) : Move :=
  ⟨m.src.rot180, m.dst.rot180, m.promotion⟩

@[simp] theorem rot180_src (m : Move) : m.rot180.src = m.src.rot180 := rfl

@[simp] theorem rot180_dst (m : Move) : m.rot180.dst = m.dst.rot180 := rfl

@[simp] theorem rot180_promotion (m : Move) : m.rot180.promotion = m.promotion := rfl

@[simp] theorem rot180_involutive (m : Move) : m.rot180.rot180 = m := by
  rcases m with ⟨s, d, pr⟩
  simp [rot180]

@[simp] theorem rot180_std (s t : Square) :
    (Move.std s t).rot180 = Move.std s.rot180 t.rot180 := rfl

end Move

/-! ## Three-piece states (white-rook frame) -/

/-- A king-and-rook versus king position by the squares of its three
pieces and the side to move. White owns the rook. -/
structure KRState where
  /-- The side to move. -/
  toMove : Color
  /-- White king (the rook's support). -/
  wk : Square
  /-- Black king (the lone king). -/
  bk : Square
  /-- White rook. -/
  rs : Square
deriving DecidableEq, Repr

/-- A move of the side to move: the white king, the black king, or the
rook goes to `dst`. Captures are not represented. -/
inductive KRMove where
  | king (dst : Square)
  | rook (dst : Square)
deriving DecidableEq, Repr

namespace KRState

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

/-- Squares a rook on `r` can move to on an empty board, by computation. -/
def rookDestsOf (r : Square) : List Square :=
  ray r 1 0 ++ ray r (-1) 0 ++ ray r 0 1 ++ ray r 0 (-1)

/-- King steps of every square, indexed by `idx`. -/
def kingNeighborsTable : Array (List Square) := (allSquares.map kingNeighborsOf).toArray

/-- Rook destinations of every square, indexed by `idx`. -/
def rookDestsTable : Array (List Square) := (allSquares.map rookDestsOf).toArray

/-- Squares a king on `k` can step to. -/
def kingNeighbors (k : Square) : List Square := kingNeighborsTable.getD (idx k) []

/-- Squares a rook on `r` can move to on an empty board. -/
def rookDests (r : Square) : List Square := rookDestsTable.getD (idx r) []

/-- Distance of naturals. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Chebyshev distance. -/
def cheb (x y x' y' : Nat) : Nat := max (dist x x') (dist y y')

/-- `u` lies strictly between `s` and `t` on a rook ray. Agrees with
`Between s t u` whenever `RookAttacks s t`. -/
def orthoBetween (s t u : Square) : Bool :=
  s != u && u != t && (s.file == t.file || s.rank == t.rank) &&
    (s.file == u.file || s.rank == u.rank) &&
    dist s.file.val u.file.val + dist u.file.val t.file.val == dist s.file.val t.file.val &&
    dist s.rank.val u.rank.val + dist u.rank.val t.rank.val == dist s.rank.val t.rank.val

/-- The rook on `rs` checks the square `d`, the only possible blocker being
the white king `wk`. -/
def rookChecks (rs d wk : Square) : Bool :=
  decide (RookAttacks rs d) && !orthoBetween rs d wk

/-- The black king on `bk` is attacked by the white king `wk` or the rook
`rs`. -/
def kingAttackedBlack (wk bk rs : Square) : Bool :=
  decide (KingAttacks wk bk) || rookChecks rs bk wk

/-- The white king on `wk` is attacked by the black king `bk`. -/
def kingAttackedWhite (wk bk : Square) : Bool :=
  decide (KingAttacks wk bk)

/-- The king of `c` among `wk`, `bk`. -/
def king (s : KRState) : Color → Square
  | .white => s.wk
  | .black => s.bk

/-- The king of `c` is attacked. -/
def inCheckB (s : KRState) (c : Color) : Bool :=
  match c with
  | .white => kingAttackedWhite s.wk s.bk
  | .black => kingAttackedBlack s.wk s.bk s.rs

/-- Geometric legality of the white king step `wk → d`. Captures are
excluded. -/
def fastKingW (wk d bk rs : Square) : Bool :=
  decide (KingAttacks wk d) && d != bk && d != rs && !decide (KingAttacks bk d)

/-- Geometric legality of the black king step `bk → d`, including capture
of an unprotected rook. -/
def fastKingB (wk d bk rs : Square) : Bool :=
  decide (KingAttacks bk d) && d != wk &&
    (if d == rs then !decide (KingAttacks wk d)
      else !decide (KingAttacks wk d) && !rookChecks rs d wk)

/-- Geometric legality of the rook move `rs → d`. Captures are excluded. -/
def fastRook (wk d bk rs : Square) : Bool :=
  decide (RookAttacks rs d) && d != wk && d != bk &&
    !orthoBetween rs d wk && !orthoBetween rs d bk

/-- The state describes a legal three-piece position: distinct squares,
kings not adjacent, and the side not to move not in check. -/
def okB (s : KRState) : Bool :=
  s.wk != s.bk && s.wk != s.rs && s.bk != s.rs &&
    !decide (KingAttacks s.wk s.bk) && !s.inCheckB s.toMove.other

/-- Geometric legality of a (non-capturing) move in an `okB` state. -/
def fastLegal (s : KRState) : KRMove → Bool
  | .king d =>
    match s.toMove with
    | .white => fastKingW s.wk d s.bk s.rs
    | .black => d != s.rs && fastKingB s.wk d s.bk s.rs
  | .rook d =>
    s.toMove == .white && fastRook s.wk d s.bk s.rs

/-- The state after a move. -/
def apply (s : KRState) : KRMove → KRState
  | .king d =>
    match s.toMove with
    | .white => { s with toMove := .black, wk := d }
    | .black => { s with toMove := .white, bk := d }
  | .rook d =>
    { s with toMove := .black, rs := d }

/-- The side to move is checkmated: Black is in check and every king
step is onto the white king, onto an attacked square, or onto the
protected rook. -/
def mateB (s : KRState) : Bool :=
  s.toMove == .black && kingAttackedBlack s.wk s.bk s.rs &&
    (kingNeighbors s.bk).all fun d =>
      d == s.wk || decide (KingAttacks s.wk d) ||
        (d != s.rs && rookChecks s.rs d s.wk)

/-- Whether some non-capturing move is geometrically legal. -/
def hasNoncaptureLegal (s : KRState) : Bool :=
  match s.toMove with
  | .white =>
    (kingNeighbors s.wk).any (fun d => fastKingW s.wk d s.bk s.rs) ||
      (rookDests s.rs).any (fun d => fastRook s.wk d s.bk s.rs)
  | .black =>
    (kingNeighbors s.bk).any (fun d => d != s.rs && fastKingB s.wk d s.bk s.rs)

/-- The state is dead for helpmate: not checkmate, and the only legal
continuations (if any) capture the rook. -/
def deadB (s : KRState) : Bool :=
  !s.mateB && !s.hasNoncaptureLegal

/-- The chess position of the state. -/
def toPosition (s : KRState) : Position where
  board := Board.kingsRookBoard s.wk s.bk s.rs .white
  toMove := s.toMove
  castling := ∅
  enPassant := none

/-- The chess move of a state move. -/
def move (s : KRState) : KRMove → Move
  | .king d => Move.std (s.king s.toMove) d
  | .rook d => Move.std s.rs d

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

/-- The rook is adjacent to the black king and not protected by the white
king. -/
def hangingRook (s : KRState) : Bool :=
  decide (KingAttacks s.bk s.rs) && !decide (KingAttacks s.wk s.rs)

/-- Rook distance to the mating file/rank, with a penalty for occupying
`a8` before Black has reached `h8`/`g8`. -/
def rookWork (s : KRState) : Nat :=
  let hang := if s.hangingRook then 8 else 0
  let x := s.rs.file.val
  let y := s.rs.rank.val
  let base :=
    if x == 0 && y == 7 then
      if (s.bk.file.val == 7 && s.bk.rank.val == 7) ||
          (s.bk.file.val == 6 && s.bk.rank.val == 7) then 0
      else 4
    else if y == 7 && x < 7 then
      if s.bk.rank.val < 7 then 4 else 1
    else if x == 0 then 1
    else 2
  let hfile := if x == 7 && !(s.bk.file.val == 7 && s.bk.rank.val == 7) then 3 else 0
  hang + base + hfile

/-- Black king distance to `h8`. -/
def workBk (s : KRState) : Nat :=
  let block := (if decide (KingAttacks s.bk s.rs) then 1 else 0) +
    (if decide (KingAttacks s.bk s.wk) &&
        cheb s.wk.file.val s.wk.rank.val 7 7 < cheb s.bk.file.val s.bk.rank.val 7 7 then 1
      else 0)
  4 * bkDist s.bk + dist s.bk.file.val 7 + dist s.bk.rank.val 7 + block

/-- Extra cost when the white king sits on `h8` and the black king is
cut off behind it. -/
def cornerBlock (s : KRState) : Nat :=
  if s.wk.file.val == 7 && s.wk.rank.val == 7 &&
      ((s.bk.file.val == 7 && s.bk.rank.val == 5) ||
        (s.bk.file.val == 5 && s.bk.rank.val == 7)) then 5
  else 0

/-- White's contribution to the potential. -/
def whitePart (s : KRState) : Nat := workWk s.wk + rookWork s

/-- Black's contribution to the potential. -/
def blackPart (s : KRState) : Nat := workBk s

/-- Tempo: the side that has finished its work must still move. -/
def tempo (s : KRState) (w b : Nat) : Nat :=
  match s.toMove with
  | .white => if w == 0 then 1 else 0
  | .black => if b == 0 then 1 else 0

/-- Potential without the check bonus. -/
def muBase (s : KRState) : Nat :=
  let c := s.cornerBlock
  let w := s.whitePart
  let b := s.blackPart
  2 * (w + b + c) + tempo s (w + c) (b + c)

/-- Bonus so that fleeing check lowers the potential. -/
def checkBonus (s : KRState) : Nat := if s.inCheckB s.toMove then 80 else 0

/-- Lyapunov potential of the state. -/
def mu (s : KRState) : Nat := s.muBase + s.checkBonus

/-! ### Scripted policy -/

/-- The move is legal, leads to a legal state, and does not enter a dead
position unless it mates. -/
def oneOk (s : KRState) (m : KRMove) : Bool :=
  s.fastLegal m &&
    let s1 := s.apply m
    s1.okB && (s1.mateB || !s1.deadB)

/-- The move is legal and mates or lowers the potential without entering
a dead position (`x` is the current potential). -/
def progressMove (s : KRState) (x : Nat) (m : KRMove) : Bool :=
  s.fastLegal m &&
    let s1 := s.apply m
    s1.okB && (s1.mateB || (s1.mu < x && !s1.deadB))

/-- Score of a move: `0` for mate, otherwise one more than the new potential
without the check bonus. -/
def score (s : KRState) (m : KRMove) : Nat :=
  let s1 := s.apply m
  if s1.mateB then 0 else s1.muBase + 1

/-- The legal non-dead move with the smallest score, first wins ties. -/
def bestOf (s : KRState) (ms : List KRMove) : Option KRMove :=
  let best := ms.foldl (init := (none : Option (KRMove × Nat))) fun best m =>
    if s.oneOk m then
      let sc := s.score m
      match best with
      | none => some (m, sc)
      | some (_, bsc) => if sc < bsc then some (m, sc) else best
    else best
  best.map (·.1)

/-- First legal move that does not raise the potential and does not
stalemate. -/
def waitMove (s : KRState) : Option KRMove :=
  let x := s.mu
  match s.toMove with
  | .white =>
    match (rookDests s.rs).find? fun d =>
        let m := KRMove.rook d
        s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x && !(s.apply m).deadB with
    | some d => some (.rook d)
    | none =>
      (kingNeighbors s.wk).findSome? fun d =>
        let m := KRMove.king d
        if s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x && !(s.apply m).deadB then
          some m
        else none
  | .black =>
    (kingNeighbors s.bk).findSome? fun d =>
      let m := KRMove.king d
      if d != s.rs && s.fastLegal m && (s.apply m).okB && (s.apply m).mu ≤ x &&
          !(s.apply m).deadB then
        some m
      else none

/-- Unhang the rook if it is hanging and White is to move. -/
def unhangRook (s : KRState) : Option KRMove :=
  if s.toMove == .white && s.hangingRook then
    let x := s.mu
    match (rookDests s.rs).find? fun d => s.progressMove x (.rook d) with
    | some d => some (.rook d)
    | none =>
      (rookDests s.rs).findSome? fun d =>
        if s.fastLegal (.rook d) && (s.apply (.rook d)).okB &&
            !decide (KingAttacks s.bk d) && !(s.apply (.rook d)).deadB then
          some (.rook d)
        else none
  else none

/-- The scripted move. In check: the king step with the best score.
Otherwise the first king or rook move that mates or lowers the
potential, else a waiting move, else the legal move with the best score. -/
def scriptMove (s : KRState) : Option KRMove :=
  match s.unhangRook with
  | some m => some m
  | none =>
    let x := s.mu
    match s.toMove with
    | .black =>
      let kingMoves := (kingNeighbors s.bk).filterMap fun d =>
        if d == s.rs then none else some (KRMove.king d)
      if s.inCheckB .black then s.bestOf kingMoves
      else
        match (kingNeighbors s.bk).find? fun d => d != s.rs && s.progressMove x (.king d) with
        | some d => some (.king d)
        | none =>
          match s.waitMove with
          | some m => some m
          | none => s.bestOf kingMoves
    | .white =>
      let kingMoves := (kingNeighbors s.wk).map KRMove.king
      let rookMoves := (rookDests s.rs).map KRMove.rook
      if s.inCheckB .white then s.bestOf kingMoves
      else
        match (kingNeighbors s.wk).find? fun d => s.progressMove x (.king d) with
        | some d => some (.king d)
        | none =>
          match (rookDests s.rs).find? fun d => s.progressMove x (.rook d) with
          | some d => some (.rook d)
          | none =>
            match s.waitMove with
            | some m => some m
            | none => s.bestOf (kingMoves ++ rookMoves)

/-- The state has reached the goal relative to `s0`: it is checkmate, or
its potential is below that of `s0` and it is not dead. -/
def goal (s0 s : KRState) : Bool :=
  s.mateB || (s.mu < s0.mu && !s.deadB)

/-- Within `n` plies of scripted play from `s`, the goal relative to `s0`
is reached. Each ply first probes a waiting move, then follows the
script. Every played move is checked with `oneOk`. -/
def chain (s0 : KRState) : KRState → Nat → Bool
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
def window : Nat := 12

/-- A state passes: it is illegal, checkmate, dead, or the script lowers
its potential. -/
def checkState (s : KRState) : Bool :=
  !s.okB || s.mateB || s.deadB || chain s s window

/-- Every placement of the three pieces, with either side to move, is
covered. -/
def checkAll : Bool :=
  allSquares.all fun wk =>
    allSquares.all fun bk =>
      allSquares.all fun rs =>
        checkState ⟨.white, wk, bk, rs⟩ && checkState ⟨.black, wk, bk, rs⟩

-- `checkAll_true` is proved after the rest of the module type-checks.
-- theorem checkAll_true : checkAll = true := by native_decide

/-! ### The mating line -/

/-- The moves of a successful `chain` from `s` relative to `s0`, if any. -/
def chainPath (s0 : KRState) : KRState → Nat → Option (List KRMove)
  | _, 0 => none
  | s, n + 1 =>
    let viaWait : Option (List KRMove) :=
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
def applyAll (s : KRState) (ms : List KRMove) : KRState :=
  ms.foldl apply s

/-- The mating line in state moves; `fuel` bounds the number of rounds. -/
def matingLineAux : KRState → Nat → List KRMove
  | _, 0 => []
  | s, fuel + 1 =>
    if s.mateB || s.deadB then []
    else
      match chainPath s s window with
      | some ms => ms ++ matingLineAux (s.applyAll ms) fuel
      | none => []

/-- The chess moves of a sequence of state moves. -/
def toMoves : KRState → List KRMove → List Move
  | _, [] => []
  | s, m :: ms => s.move m :: toMoves (s.apply m) ms

/-- The engineered mating line from `s`, as chess moves. Every round
lowers the potential or mates, so `2 * s.mu + 2` rounds suffice. -/
def matingLine (s : KRState) : List Move :=
  s.toMoves (matingLineAux s (2 * s.mu + 2))

/-- The three-piece state of a white-rook position, if the board holds
exactly those pieces in a legal arrangement. -/
def ofPositionWhite? (p : Position) : Option KRState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .white, kind := .rook }) with
  | some wk, some bk, some rs =>
    if (⟨p.toMove, wk, bk, rs⟩ : KRState).okB && (allSquares.all fun q =>
          p.board q == Board.kingsRookBoard wk bk rs .white q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove, wk, bk, rs⟩
    else none
  | _, _, _ => none

/-- The three-piece state of a black-rook position, rotated into the
white-rook frame. -/
def ofPositionBlack? (p : Position) : Option KRState :=
  match allSquares.find? (fun q => p.board q == some { color := .white, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .king }),
      allSquares.find? (fun q => p.board q == some { color := .black, kind := .rook }) with
  | some wk, some bk, some rs =>
    if (⟨p.toMove.other, bk.rot180, wk.rot180, rs.rot180⟩ : KRState).okB &&
        (allSquares.all fun q =>
          p.board q == Board.kingsRookBoard wk bk rs .black q) &&
        decide (p.castling = ∅) && decide (p.enPassant = none) then
      some ⟨p.toMove.other, bk.rot180, wk.rot180, rs.rot180⟩
    else none
  | _, _, _ => none

/-- The white-rook-frame state of a king-and-rook versus king position. -/
def ofPosition? (p : Position) : Option KRState :=
  match ofPositionWhite? p with
  | some s => some s
  | none => ofPositionBlack? p

/-! ## Soundness -/

open Position

theorem kingAttacks_ne {s t : Square} (h : KingAttacks s t) : s ≠ t := h.1

theorem rookAttacks_ne {s t : Square} (h : RookAttacks s t) : s ≠ t := h.1

theorem orthoBetween_eq {s t : Square} (h : RookAttacks s t) (u : Square) :
    orthoBetween s t u = decide (Between s t u) := by
  revert s t u
  native_decide

theorem mem_kingNeighbors {k d : Square} (h : KingAttacks k d) :
    d ∈ kingNeighbors k := by
  revert k d
  native_decide

theorem mem_rookDests {r d : Square} (h : RookAttacks r d) :
    d ∈ rookDests r := by
  revert r d
  native_decide

theorem castlingSide_none_of_kingAttacks (c : Color) {s t : Square}
    (h : KingAttacks s t) : (Move.std s t).castlingSide? c = none := by
  revert c s t
  native_decide

theorem rookChecks_iff (rs d wk : Square) :
    rookChecks rs d wk = true ↔ RookAttacks rs d ∧ ¬ Between rs d wk := by
  unfold rookChecks
  by_cases hR : RookAttacks rs d
  · rw [orthoBetween_eq hR]
    simp [hR]
  · simp [hR]

theorem kingAttackedBlack_iff (wk bk rs : Square) :
    kingAttackedBlack wk bk rs = true ↔
      KingAttacks wk bk ∨ (RookAttacks rs bk ∧ ¬ Between rs bk wk) := by
  simp [kingAttackedBlack, rookChecks_iff, Bool.or_eq_true]

theorem okB_iff (s : KRState) :
    s.okB = true ↔
      s.wk ≠ s.bk ∧ s.wk ≠ s.rs ∧ s.bk ≠ s.rs ∧
        ¬ KingAttacks s.wk s.bk ∧ s.inCheckB s.toMove.other = false := by
  simp [okB, and_assoc]

theorem kingIsAttacked_white_eq (wk bk rs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) :
    (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .white =
      kingAttackedWhite wk bk := by
  rw [Bool.eq_iff_iff, Board.kingsRookBoard_kingIsAttacked_white wk bk rs .white h1 h2 h3]
  simp [kingAttackedWhite, kingAttacks_symmetric]

theorem kingIsAttacked_black_eq (wk bk rs : Square)
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) :
    (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .black =
      kingAttackedBlack wk bk rs := by
  rw [Bool.eq_iff_iff, Board.kingsRookBoard_kingIsAttacked_black wk bk rs .white h1 h2 h3]
  simp [kingAttackedBlack_iff]

theorem kingIsAttacked_eq (s : KRState) (hok : s.okB = true) (c : Color) :
    s.toPosition.board.kingIsAttacked c = s.inCheckB c := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  cases c with
  | white => exact kingIsAttacked_white_eq _ _ _ h1 h2 h3
  | black => exact kingIsAttacked_black_eq _ _ _ h1 h2 h3

theorem fastKingW_iff (wk d bk rs : Square) :
    fastKingW wk d bk rs = true ↔
      KingAttacks wk d ∧ d ≠ bk ∧ d ≠ rs ∧ ¬ KingAttacks bk d := by
  simp [fastKingW, and_assoc]

theorem fastRook_iff (wk d bk rs : Square) :
    fastRook wk d bk rs = true ↔
      RookAttacks rs d ∧ d ≠ wk ∧ d ≠ bk ∧ orthoBetween rs d wk = false ∧
        orthoBetween rs d bk = false := by
  simp [fastRook, and_assoc]

theorem fastKingB_iff (wk d bk rs : Square) :
    fastKingB wk d bk rs = true ↔
      KingAttacks bk d ∧ d ≠ wk ∧
        (d = rs ∧ ¬ KingAttacks wk d ∨
          d ≠ rs ∧ ¬ KingAttacks wk d ∧ rookChecks rs d wk = false) := by
  unfold fastKingB
  by_cases hd : d = rs
  · simp [hd, and_assoc]
  · simp [hd, and_assoc]

/-! ### Playing moves -/

theorem play_whiteKing {s : KRState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastKingW s.wk d s.bk s.rs = true) :
    isLegalMove s.toPosition (Move.std s.wk d) = true ∧
      s.toPosition.play (Move.std s.wk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdbk, hdrs, hsafe⟩ := (fastKingW_iff _ _ _ _).mp hm
  have hdwk : d ≠ s.wk := (kingAttacks_ne hka).symm
  have hsrcP : s.toPosition.board (Move.std s.wk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsRookBoard s.wk s.bk s.rs .white s.wk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsRookBoard_white _ _ _ _
  have hdstNone : s.toPosition.board (Move.std s.wk d).dst = none :=
    Board.kingsRookBoard_other _ _ _ _ _ hdwk hdbk hdrs
  have hside : (Move.std s.wk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.wk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.wk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.wk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsRookBoard d s.bk s.rs .white := by
    rw [hba]
    change (Board.kingsRookBoard s.wk s.bk s.rs .white).relocate s.wk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsRookBoard_white _ _ _ _ _ h1 h2 h3 hdwk hdbk hdrs
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
    change (Board.kingsRookBoard d s.bk s.rs .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq d s.bk s.rs hdbk hdrs h3]
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

theorem play_blackKing {s : KRState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : d ≠ s.rs)
    (hmv : fastKingB s.wk d s.bk s.rs = true) :
    isLegalMove s.toPosition (Move.std s.bk d) = true ∧
      s.toPosition.play (Move.std s.bk d) = (s.apply (.king d)).toPosition := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
  have hdbk : d ≠ s.bk := (kingAttacks_ne hka).symm
  have hdrs : d ≠ s.rs := hm
  have hsrcP : s.toPosition.board (Move.std s.bk d).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsRookBoard s.wk s.bk s.rs .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsRookBoard_black _ _ _ _ h1
  have hdstNone : s.toPosition.board (Move.std s.bk d).dst = none :=
    Board.kingsRookBoard_other _ _ _ _ _ hdwk hdbk hdrs
  have hside : (Move.std s.bk d).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk d) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk d)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk d)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsRookBoard s.wk d s.rs .white := by
    rw [hba]
    change (Board.kingsRookBoard s.wk s.bk s.rs .white).relocate s.bk d
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_kingsRookBoard_black _ _ _ _ _ h1 h2 h3 hdwk hdbk hdrs
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
  have hnR : rookChecks s.rs d s.wk = false := by
    rcases hrest with ⟨heq, _⟩ | ⟨_, _, h⟩
    · exact (hm heq).elim
    · exact h
  have hsafe' : (s.toPosition.play (Move.std s.bk d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.king d) = { s with toMove := .white, bk := d } := by
      simp [apply, ht]
    rw [hplay', happ]
    change (Board.kingsRookBoard s.wk d s.rs .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_black_eq s.wk d s.rs hdwk.symm h2 hdrs]
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

theorem play_rook {s : KRState} {d : Square} (hok : s.okB = true)
    (ht : s.toMove = .white) (hm : fastRook s.wk d s.bk s.rs = true) :
    isLegalMove s.toPosition (Move.std s.rs d) = true ∧
      s.toPosition.play (Move.std s.rs d) = (s.apply (.rook d)).toPosition := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  obtain ⟨hR, hdwk, hdbk, hnwk, hnbk⟩ := (fastRook_iff _ _ _ _).mp hm
  have hdrs : d ≠ s.rs := (rookAttacks_ne hR).symm
  have hsrcP : s.toPosition.board (Move.std s.rs d).src =
      some { color := s.toPosition.toMove, kind := .rook } := by
    change Board.kingsRookBoard s.wk s.bk s.rs .white s.rs =
      some { color := s.toMove, kind := .rook }
    rw [ht]
    exact Board.kingsRookBoard_rook _ _ _ _ h2 h3
  have hdstNone : s.toPosition.board (Move.std s.rs d).dst = none :=
    Board.kingsRookBoard_other _ _ _ _ _ hdwk hdbk hdrs
  have hplay := play_of_some s.toPosition (Move.std s.rs d) hsrcP
  have hboard' : s.toPosition.boardAfter (Move.std s.rs d)
      { color := s.toPosition.toMove, kind := .rook } =
      Board.kingsRookBoard s.wk s.bk d .white := by
    rw [boardAfter_rook _ _ rfl]
    change (Board.kingsRookBoard s.wk s.bk s.rs .white).relocate s.rs d
      { color := s.toMove, kind := .rook } = _
    rw [ht]
    exact Board.relocate_kingsRookBoard_rook _ _ _ _ _ h1 h2 h3 hdwk hdbk hdrs
  have hplay' : s.toPosition.play (Move.std s.rs d) = (s.apply (.rook d)).toPosition := by
    rw [hplay, hboard']
    simp [toPosition, apply, ht, castlingAfter_empty, enPassantAfter_rook]
  refine ⟨?_, hplay'⟩
  have hgeo : s.toPosition.board.attacks (Move.std s.rs d).src (Move.std s.rs d).dst = true := by
    change (Board.kingsRookBoard s.wk s.bk s.rs .white).attacks s.rs d = true
    rw [Board.kingsRookBoard_attacks_rook_iff h2 h3]
    refine ⟨hR, ?_, ?_⟩
    · rw [orthoBetween_eq hR] at hnwk
      exact of_decide_eq_false hnwk
    · rw [orthoBetween_eq hR] at hnbk
      exact of_decide_eq_false hnbk
  have hsafe' : (s.toPosition.play (Move.std s.rs d)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    have happ : s.apply (.rook d) = { s with toMove := .black, rs := d } := by
      simp [apply]
    rw [hplay', happ]
    change (Board.kingsRookBoard s.wk s.bk d .white).kingIsAttacked s.toMove = false
    rw [ht, kingIsAttacked_white_eq s.wk s.bk d h1 hdwk.symm hdbk.symm]
    simp [kingAttackedWhite, hna]
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  rw [destOk_of_empty (m := Move.std s.rs d) hdstNone]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.rook == PieceKind.pawn) = false := rfl
  have hnking : (PieceKind.rook == PieceKind.king) = false := rfl
  simp only [hnpawn, hnking, Bool.false_and]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem fastLegal_sound {s : KRState} {m : KRMove} (hok : s.okB = true)
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
      obtain ⟨hnrs, hmv⟩ := Bool.and_eq_true_iff.mp hm
      have hn : d ≠ s.rs := bne_iff_ne.mp hnrs
      exact (by simp [move, ht, king] : s.move (.king d) = Move.std s.bk d) ▸
        play_blackKing hok ht hn hmv
  | rook d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      exact (by simp [move] : s.move (.rook d) = Move.std s.rs d) ▸
        play_rook hok ht hm
    | black =>
      simp [fastLegal, ht] at hm

theorem legalMove_of_fastLegal {s : KRState} {m : KRMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) : LegalMove s.toPosition (s.move m) :=
  (fastLegal_sound hok hm).1

theorem play_move_eq {s : KRState} {m : KRMove} (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    s.toPosition.play (s.move m) = (s.apply m).toPosition :=
  (fastLegal_sound hok hm).2

theorem apply_okB_of_fastLegal {s : KRState} {m : KRMove}
    (hok : s.okB = true) (hm : s.fastLegal m = true) : (s.apply m).okB = true := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  cases m with
  | king d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hka, hdbk, hdrs, hsafeK⟩ := (fastKingW_iff _ _ _ _).mp hm
      have hna' : ¬ KingAttacks d s.bk := mt kingAttacks_symmetric.mp hsafeK
      have happ : s.apply (.king d) = ⟨.black, d, s.bk, s.rs⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.black, d, s.bk, s.rs⟩).mpr
        ⟨hdbk, hdrs, h3, hna', by simpa [inCheckB, kingAttackedWhite] using hna'⟩
    | black =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hnrs, hmv⟩ := Bool.and_eq_true_iff.mp hm
      obtain ⟨hka, hdwk, hrest⟩ := (fastKingB_iff _ _ _ _).mp hmv
      have hdrs : d ≠ s.rs := bne_iff_ne.mp hnrs
      have hsafeK : ¬ KingAttacks s.wk d := by
        rcases hrest with ⟨_, h⟩ | ⟨_, h, _⟩ <;> exact h
      have hnR : rookChecks s.rs d s.wk = false := by
        rcases hrest with ⟨heq, _⟩ | ⟨_, _, h⟩
        · exact (hdrs heq).elim
        · exact h
      have happ : s.apply (.king d) = ⟨.white, s.wk, d, s.rs⟩ := by simp [apply, ht]
      rw [happ]
      exact (okB_iff ⟨.white, s.wk, d, s.rs⟩).mpr
        ⟨hdwk.symm, h2, hdrs, hsafeK, by
          simp [inCheckB, kingAttackedBlack, hsafeK, hnR]⟩
  | rook d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      obtain ⟨hR, hdwk, hdbk, _, _⟩ := (fastRook_iff _ _ _ _).mp hm
      have happ : s.apply (.rook d) = ⟨.black, s.wk, s.bk, d⟩ := by simp [apply]
      rw [happ]
      exact (okB_iff ⟨.black, s.wk, s.bk, d⟩).mpr
        ⟨h1, hdwk.symm, hdbk.symm, hna, by simpa [inCheckB, kingAttackedWhite] using hna⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem oneOk_iff (s : KRState) (m : KRMove) :
    s.oneOk m = true ↔
      s.fastLegal m = true ∧ (s.apply m).okB = true ∧
        ((s.apply m).mateB = true ∨ (s.apply m).deadB = false) := by
  simp [oneOk, Bool.and_eq_true, Bool.or_eq_true]

def Progress (s0 s1 : KRState) : Prop :=
  s1.okB = true ∧ Reachable s0.toPosition s1.toPosition ∧
    (s1.mateB = true ∨ (s1.mu < s0.mu ∧ s1.deadB = false))

theorem reachable_apply {s0 s : KRState} {m : KRMove}
    (hr : Reachable s0.toPosition s.toPosition) (hok : s.okB = true)
    (hm : s.fastLegal m = true) :
    Reachable s0.toPosition (s.apply m).toPosition := by
  have := Reachable.step (s.move m) hr (legalMove_of_fastLegal hok hm)
  rwa [play_move_eq hok hm] at this

theorem goal_sound {s0 s : KRState} (hok : s.okB = true)
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

theorem chain_sound {s0 : KRState} :
    ∀ (n : Nat) (s : KRState), s.okB = true → Reachable s0.toPosition s.toPosition →
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

theorem checkState_progress {s : KRState} (hok : s.okB = true)
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

theorem mateB_toMove {s : KRState} (hm : s.mateB = true) : s.toMove = .black := by
  simp only [mateB, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1

theorem mateB_checked {s : KRState} (hm : s.mateB = true) :
    kingAttackedBlack s.wk s.bk s.rs = true := by
  simp only [mateB, Bool.and_eq_true] at hm
  exact hm.1.2

theorem mateB_flight {s : KRState} (hm : s.mateB = true) {d : Square}
    (hd : d ∈ kingNeighbors s.bk) :
    (d == s.wk || decide (KingAttacks s.wk d) ||
      (d != s.rs && rookChecks s.rs d s.wk)) = true := by
  simp only [mateB, Bool.and_eq_true, List.all_eq_true] at hm
  exact hm.2 d hd

theorem ne_of_kingsRookBoard_eq_none {wk bk rs s : Square} {c : Color}
    (h : Board.kingsRookBoard wk bk rs c s = none) :
    s ≠ wk ∧ s ≠ bk ∧ s ≠ rs := by
  unfold Board.kingsRookBoard at h
  split_ifs at h with h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- In a `mateB` state, Black has no legal move. -/
theorem mateB_black_no_legalMove {s : KRState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hm : s.mateB = true) (m : Move) :
    ¬ LegalMove s.toPosition m := by
  intro hlm
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core rfl rfl hlm
  have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := ht ▸ hsafe
  rcases piece with ⟨pc, pk⟩
  have hpc' : pc = .black := hpc.trans ht
  subst hpc'
  have hsrc' : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
      some ⟨.black, pk⟩ := hsrc
  rcases hkind with hk | hk
  · simp only at hk
    subst hk
    have hsq : m.src = s.bk := Board.kingsRookBoard_eq_black_king hsrc'
    have hka : KingAttacks s.bk m.dst := by
      have hatt' :
          (Board.kingsRookBoard s.wk s.bk s.rs .white).attacks m.src m.dst = true := hatt
      rw [Board.attacks_king hsrc', hsq] at hatt'
      exact of_decide_eq_true hatt'
    have hside' : m.castlingSide? .black = none := ht ▸ hside rfl
    have hplay := play_of_some s.toPosition m hsrc
    have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hside' hpromo
    have hboard : (s.toPosition.play m).board =
        (Board.kingsRookBoard s.wk s.bk s.rs .white).relocate s.bk m.dst
          { color := .black, kind := .king } := by
      rw [hplay, hba, hsq]
      rfl
    have hmem := mateB_flight hm (mem_kingNeighbors hka)
    rcases hdstOr with hempty | hrs
    · obtain ⟨hdwk, hdbk, hdrs⟩ := ne_of_kingsRookBoard_eq_none (by
        simpa [toPosition] using hempty)
      rw [hboard, Board.relocate_kingsRookBoard_black s.wk s.bk s.rs m.dst .white
        h1 h2 h3 hdwk hdbk hdrs, kingIsAttacked_black_eq s.wk m.dst s.rs
        hdwk.symm h2 hdrs] at hsafe'
      have hwkB : (m.dst == s.wk) = false := by simp [hdwk]
      have hsafe'' : ¬ KingAttacks s.wk m.dst ∧
          KRState.rookChecks s.rs m.dst s.wk = false := by
        simpa [KRState.kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      have hkaF : decide (KingAttacks s.wk m.dst) = false := decide_eq_false hsafe''.1
      have hrF : KRState.rookChecks s.rs m.dst s.wk = false := hsafe''.2
      simp [hwkB, hkaF, hrF] at hmem
    · rw [hrs] at hmem hboard
      have hwkB : (s.rs == s.wk) = false := by simp [h2.symm]
      by_cases hprot : KingAttacks s.wk s.rs
      · rw [hboard, Board.relocate_capture_rook_black s.wk s.bk s.rs h1 h2 h3] at hsafe'
        rw [Board.kingsBoard_kingIsAttacked_black s.wk s.rs h2] at hsafe'
        exact of_decide_eq_false hsafe' hprot
      · have hkaF : decide (KingAttacks s.wk s.rs) = false := decide_eq_false hprot
        simp [hwkB, hkaF] at hmem
  · simp only at hk
    subst hk
    have hsrc'' := hsrc'
    unfold Board.kingsRookBoard at hsrc''
    split_ifs at hsrc'' <;> cases hsrc''

/-- A `mateB` state of an `okB` state is a checkmate position. -/
theorem inCheckmate_of_mateB {s : KRState} (hok : s.okB = true) (hm : s.mateB = true) :
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

theorem hasNoncaptureLegal_of_fastLegal {s : KRState} {m : KRMove}
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
  | rook d =>
    cases ht : s.toMove with
    | white =>
      simp only [fastLegal, ht] at hm
      have hR : RookAttacks s.rs d := ((fastRook_iff _ _ _ _).mp hm).1
      simp only [hasNoncaptureLegal, ht, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨d, mem_rookDests hR, hm⟩
    | black =>
      simp [fastLegal, ht] at hm

theorem toPosition_isKingAndRook {s : KRState} (hok : s.okB = true) :
    IsKingAndRook s.toPosition := by
  obtain ⟨h1, h2, h3, hna, _⟩ := (okB_iff s).mp hok
  exact ⟨s.wk, s.bk, s.rs, .white, h1, h2, h3, hna, rfl, rfl, rfl⟩

end KRState

namespace Position

theorem IsKingAndRook.of_play {p : Position} {m : Move}
    (h : IsKingAndRook p) (hm : LegalMove p m) :
    IsKingAndRook (p.play m) ∨ IsTwoKings (p.play m) := by
  obtain ⟨wk, bk, rs, c, hwk_bk, hwk_rs, hbk_rs, hna, hboard, hcstl, _hep⟩ := h
  obtain ⟨hpromo, hdestOk, hdstOr, hsafe, hatt, piece, hsrcP, hcol', hkind, hside⟩ :=
    kingRook_legalMove_core hboard hcstl hm
  have hplay := play_of_some p m hsrcP
  have hsrcEq : m.src = wk ∨ m.src = bk ∨ m.src = rs :=
    (Board.kingsRookBoard_isSome wk bk rs m.src c).mp (by
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
      have hpiece : piece = { color := p.toMove, kind := .rook } := by
        cases piece; simp_all
      rw [hpiece, boardAfter_rook p m (c := p.toMove) hpromo, hcstl]
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
      have hpiece : piece = { color := p.toMove, kind := .rook } := by
        cases piece; simp_all
      calc (p.play m).enPassant
          = enPassantAfter m { color := p.toMove, kind := .rook }
              (p.boardAfter m { color := p.toMove, kind := .rook }) := by
            rw [hplay, hpiece]
        _ = none := enPassantAfter_rook _ _ _
  rcases hdstOr with hdstNone | hdstRs
  · have hdstW : m.dst ≠ wk := by
      intro heq; rw [heq, hboard, Board.kingsRookBoard_white] at hdstNone; cases hdstNone
    have hdstB : m.dst ≠ bk := by
      intro heq
      rw [heq, hboard, Board.kingsRookBoard_black wk bk rs c hwk_bk] at hdstNone
      cases hdstNone
    have hdstS : m.dst ≠ rs := by
      intro heq
      rw [heq, hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs] at hdstNone
      cases hdstNone
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsRookBoard_white])
      have ht : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsRookBoard_white wk bk rs m.dst c
        hwk_bk hwk_rs hbk_rs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsRookBoard m.dst bk rs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsRookBoard wk bk rs c).relocate wk m.dst
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW]
          _ = Board.kingsRookBoard m.dst bk rs c := hrel
      have hna' : ¬ KingAttacks m.dst bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by simpa [ht] using hsafe
        have hiff := Board.kingsRookBoard_kingIsAttacked_white m.dst bk rs c
          hdstB hdstS hbk_rs
        intro hk
        have : (p.play m).board.kingIsAttacked .white = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl (kingAttacks_symmetric.mp hk))
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨m.dst, bk, rs, c, hdstB, hdstS, hbk_rs, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsRookBoard_black wk bk rs c hwk_bk])
      have ht : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [ht] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_kingsRookBoard_black wk bk rs m.dst c
        hwk_bk hwk_rs hbk_rs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsRookBoard wk m.dst rs c := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece, ht]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsRookBoard wk bk rs c).relocate bk m.dst
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB]
          _ = Board.kingsRookBoard wk m.dst rs c := hrel
      have hna' : ¬ KingAttacks wk m.dst := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by simpa [ht] using hsafe
        have hiff := Board.kingsRookBoard_kingIsAttacked_black wk m.dst rs c
          hdstW.symm hwk_rs hdstS
        intro hk
        have : (p.play m).board.kingIsAttacked .black = true := by
          rw [hboard']
          exact hiff.mpr (Or.inl hk)
        exact Bool.false_ne_true (hsafe'.symm.trans this)
      exact Or.inl ⟨wk, m.dst, rs, c, hdstW.symm, hwk_rs, hdstS, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := c, kind := .rook } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcS, hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs])
      have ht : p.toMove = c := by simpa [hpiece] using hcol'.symm
      have hba := boardAfter_rook p m (c := c) hpromo
      have hrel := Board.relocate_kingsRookBoard_rook wk bk rs m.dst c
        hwk_bk hwk_rs hbk_rs hdstW hdstB hdstS
      have hboard' : (p.play m).board = Board.kingsRookBoard wk bk m.dst c := by
        calc (p.play m).board
            = p.boardAfter m { color := c, kind := .rook } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := c, kind := .rook } := hba
          _ = (Board.kingsRookBoard wk bk rs c).relocate rs m.dst
                { color := c, kind := .rook } := by
              rw [hboard, hsrcS]
          _ = Board.kingsRookBoard wk bk m.dst c := hrel
      exact Or.inl ⟨wk, bk, m.dst, c, hwk_bk, hdstW.symm, hdstB.symm, hna, hboard', hcast', hep'⟩
  · have hrook : p.board rs = some { color := c, kind := .rook } := by
      rw [hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs]
    have ht : p.toMove = c.other :=
      destOk_toMove_of_dst_rook hboard hwk_rs hbk_rs hdstRs hdestOk
    have hsrcNeRs : m.src ≠ rs := by
      intro heq
      have hsrcP' := hsrcP
      rw [heq, hrook] at hsrcP'
      have hpc : c = p.toMove := by
        injection hsrcP' with hpeq
        simpa [hcol'] using congrArg Piece.color hpeq
      rw [ht] at hpc
      exact Color.other_ne c hpc.symm
    rcases hsrcEq with hsrcW | hsrcB | hsrcS
    · have hpiece : piece = { color := .white, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by rw [hsrcW, hboard, Board.kingsRookBoard_white])
      have htW : p.toMove = .white := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.black := by
        have : c.other = Color.white := ht.symm.trans htW
        cases c
        · simp [Color.other] at this
        · rfl
      have hba := boardAfter_king_no_castle p m (c := .white)
        (by simpa [htW] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_rook_white wk bk rs hwk_bk hwk_rs hbk_rs
      have hboard' : (p.play m).board = Board.kingsBoard rs bk := by
        calc (p.play m).board
            = p.boardAfter m { color := .white, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .white, kind := .king } := hba
          _ = (Board.kingsRookBoard wk bk rs .black).relocate wk rs
                { color := .white, kind := .king } := by
              rw [hboard, hsrcW, hdstRs, hc]
          _ = Board.kingsBoard rs bk := hrel
      have hna' : ¬ KingAttacks rs bk := by
        have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
          simpa [htW] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_white rs bk hbk_rs.symm] at hsafe'
        exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
      exact Or.inr ⟨rs, bk, hbk_rs.symm, hna', hboard', hcast', hep'⟩
    · have hpiece : piece = { color := .black, kind := .king } :=
        piece_eq_of_eq_some hsrcP (by
          rw [hsrcB, hboard, Board.kingsRookBoard_black wk bk rs c hwk_bk])
      have htB : p.toMove = .black := by simpa [hpiece] using hcol'.symm
      have hc : c = Color.white := by
        have : c.other = Color.black := ht.symm.trans htB
        cases c
        · rfl
        · simp [Color.other] at this
      have hba := boardAfter_king_no_castle p m (c := .black)
        (by simpa [htB] using hside (by simp [hpiece])) hpromo
      have hrel := Board.relocate_capture_rook_black wk bk rs hwk_bk hwk_rs hbk_rs
      have hboard' : (p.play m).board = Board.kingsBoard wk rs := by
        calc (p.play m).board
            = p.boardAfter m { color := .black, kind := .king } := by
              rw [hplay, hpiece]
          _ = p.board.relocate m.src m.dst { color := .black, kind := .king } := hba
          _ = (Board.kingsRookBoard wk bk rs .white).relocate bk rs
                { color := .black, kind := .king } := by
              rw [hboard, hsrcB, hdstRs, hc]
          _ = Board.kingsBoard wk rs := hrel
      have hna' : ¬ KingAttacks wk rs := by
        have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
          simpa [htB] using hsafe
        rw [hboard', Board.kingsBoard_kingIsAttacked_black wk rs hwk_rs] at hsafe'
        exact of_decide_eq_false hsafe'
      exact Or.inr ⟨wk, rs, hwk_rs, hna', hboard', hcast', hep'⟩
    · exact (hsrcNeRs hsrcS).elim

theorem IsKingAndRook.of_reachable {p q : Position}
    (h : IsKingAndRook p) (hr : Reachable p q) :
    IsKingAndRook q ∨ IsTwoKings q := by
  induction hr with
  | refl => exact Or.inl h
  | step m _hm hleg ih =>
    cases ih with
    | inl hkr => exact hkr.of_play hleg
    | inr htk => exact Or.inr (htk.of_play hleg)

end Position

namespace KRState

open Position

theorem destOk_capture_rook {s : KRState} (hok : s.okB = true)
    (ht : s.toMove = .black) :
    s.toPosition.destOk (Move.std s.bk s.rs) = true := by
  obtain ⟨_, h2, h3, _, _⟩ := (okB_iff s).mp hok
  unfold destOk
  change (match Board.kingsRookBoard s.wk s.bk s.rs .white s.rs with
    | none => true
    | some q => (q.color != s.toPosition.toMove) && (q.kind != .king)) = true
  rw [Board.kingsRookBoard_rook s.wk s.bk s.rs .white h2 h3]
  simp [toPosition, ht]

theorem play_blackCapture {s : KRState} (hok : s.okB = true)
    (ht : s.toMove = .black) (hka : KingAttacks s.bk s.rs)
    (hprot : ¬ KingAttacks s.wk s.rs) :
    isLegalMove s.toPosition (Move.std s.bk s.rs) = true := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  have hsrcP : s.toPosition.board (Move.std s.bk s.rs).src =
      some { color := s.toPosition.toMove, kind := .king } := by
    change Board.kingsRookBoard s.wk s.bk s.rs .white s.bk =
      some { color := s.toMove, kind := .king }
    rw [ht]
    exact Board.kingsRookBoard_black _ _ _ _ h1
  have hside : (Move.std s.bk s.rs).castlingSide? s.toPosition.toMove = none :=
    castlingSide_none_of_kingAttacks _ hka
  have hplay := play_of_some s.toPosition (Move.std s.bk s.rs) hsrcP
  have hba := boardAfter_king_no_castle s.toPosition (Move.std s.bk s.rs)
    (c := s.toPosition.toMove) hside rfl
  have hboard' : s.toPosition.boardAfter (Move.std s.bk s.rs)
      { color := s.toPosition.toMove, kind := .king } =
      Board.kingsBoard s.wk s.rs := by
    rw [hba]
    change (Board.kingsRookBoard s.wk s.bk s.rs .white).relocate s.bk s.rs
      { color := s.toMove, kind := .king } = _
    rw [ht]
    exact Board.relocate_capture_rook_black _ _ _ h1 h2 h3
  have hgeo : s.toPosition.board.attacks (Move.std s.bk s.rs).src
      (Move.std s.bk s.rs).dst = true := by
    rw [Board.attacks_king hsrcP]
    exact decide_eq_true hka
  have hsafe' : (s.toPosition.play (Move.std s.bk s.rs)).board.kingIsAttacked
      s.toPosition.toMove = false := by
    rw [hplay, hboard']
    change (Board.kingsBoard s.wk s.rs).kingIsAttacked s.toMove = false
    rw [ht, Board.kingsBoard_kingIsAttacked_black s.wk s.rs h2]
    exact decide_eq_false hprot
  unfold isLegalMove
  rw [hsrcP]
  simp only [beq_self_eq_true, Bool.true_and]
  have hdest : s.toPosition.destOk (Move.std s.bk s.rs) = true :=
    destOk_capture_rook hok ht
  rw [hdest]
  simp only [Bool.true_and]
  have hnpawn : (PieceKind.king == PieceKind.pawn) = false := rfl
  have hsome : ((Move.std s.bk s.rs).castlingSide? s.toPosition.toMove).isSome = false := by
    rw [hside]; rfl
  simp only [hnpawn, hsome]
  exact legal_king_step_bool _ _ _ hgeo rfl hsafe'

theorem deadB_mate_eq_false {s : KRState} (hd : s.deadB = true) :
    s.mateB = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.1

theorem deadB_hasNoncapture_eq_false {s : KRState} (hd : s.deadB = true) :
    s.hasNoncaptureLegal = false := by
  simp only [deadB, Bool.and_eq_true] at hd
  simpa using hd.2

theorem white_not_inCheck {s : KRState} (hok : s.okB = true) :
    s.inCheckB .white = false := by
  obtain ⟨_, _, _, hna, _⟩ := (okB_iff s).mp hok
  simp [inCheckB, kingAttackedWhite, hna]

theorem kingAttacks_of_mem_kingNeighbors {k d : Square}
    (h : d ∈ kingNeighbors k) : KingAttacks k d := by
  revert k d
  native_decide

theorem inCheckmate_implies_mateB {s : KRState} (hok : s.okB = true)
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
    have hchk' : kingAttackedBlack s.wk s.bk s.rs = true := by
      simpa [inCheckB] using hchk
    have hall : (kingNeighbors s.bk).all (fun d =>
        d == s.wk || decide (KingAttacks s.wk d) ||
          (d != s.rs && rookChecks s.rs d s.wk)) = true := by
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
      have h3 : (d != s.rs && rookChecks s.rs d s.wk) = false := by
        cases h : (d != s.rs && rookChecks s.rs d s.wk)
        · rfl
        · simp [h1, h2, h] at hf
      have hkaB : KingAttacks s.bk d := kingAttacks_of_mem_kingNeighbors hd
      have hkaW : ¬ KingAttacks s.wk d := of_decide_eq_false h2
      have hnoleg : ∀ mv : Move, ¬ LegalMove s.toPosition mv :=
        (InCheckmate_iff_forall_not_LegalMove s.toPosition).mp hm |>.2
      by_cases hrs : d = s.rs
      · subst hrs
        have hleg : LegalMove s.toPosition (Move.std s.bk s.rs) :=
          play_blackCapture hok ht hkaB hkaW
        exact hnoleg _ hleg
      · have hne : (d != s.rs) = true := bne_iff_ne.mpr hrs
        have hnR : rookChecks s.rs d s.wk = false := by simpa [hne] using h3
        have hdwk : d ≠ s.wk := bne_iff_ne.mp (by simpa using h1)
        have hmv : fastKingB s.wk d s.bk s.rs = true := by
          simp [fastKingB, hkaB, hdwk, hrs, hkaW, hnR]
        have hfl : s.fastLegal (.king d) = true := by
          simp [fastLegal, ht, bne_iff_ne.mpr hrs, hmv]
        exact hnoleg _ (legalMove_of_fastLegal hok hfl)
    simp [mateB, ht, hchk', hall]

theorem not_inCheckmate_of_deadB {s : KRState} (hok : s.okB = true)
    (hd : s.deadB = true) : ¬ InCheckmate s.toPosition := by
  intro hm
  have := inCheckmate_implies_mateB hok hm
  exact Bool.false_ne_true ((deadB_mate_eq_false hd).symm.trans this)

theorem fastLegal_of_legalMove_noncapture {s : KRState} {m : Move}
    (hok : s.okB = true) (hm : LegalMove s.toPosition m)
    (he : s.toPosition.board m.dst = none) :
    ∃ km, s.fastLegal km = true := by
  obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
  obtain ⟨hpromo, _, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core rfl rfl hm
  obtain ⟨hdwk, hdbk, hdrs⟩ := ne_of_kingsRookBoard_eq_none (by
    simpa [toPosition] using he)
  rcases piece with ⟨pc, pk⟩
  subst hpc
  rcases hkind with hk | hk
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcW : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
          some { color := .white, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.wk := Board.kingsRookBoard_eq_white_king hsrcW
      have hattW : (Board.kingsRookBoard s.wk s.bk s.rs .white).attacks m.src m.dst = true := by
        simpa [toPosition] using hatt
      have hka : KingAttacks s.wk m.dst := by
        rw [Board.attacks_king hsrcW, hsq] at hattW
        exact of_decide_eq_true hattW
      have hplay := play_of_some s.toPosition m hsrc
      have hsideW : m.castlingSide? Color.white = none := by
        simpa [toPosition, ht] using hside rfl
      have hba := boardAfter_king_no_castle s.toPosition m (c := .white) hsideW hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsRookBoard m.dst s.bk s.rs .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.white := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsRookBoard_white s.wk s.bk s.rs m.dst .white
          h1 h2 h3 hdwk hdbk hdrs
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .white = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_white_eq m.dst s.bk s.rs hdbk hdrs h3] at hsafe'
      have hsafeK : ¬ KingAttacks s.bk m.dst := by
        simpa [kingAttackedWhite, kingAttacks_symmetric] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, fastKingW, hka, hdbk, hdrs, hsafeK]
    | black =>
      have hsrcB : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
          some { color := .black, kind := .king } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.bk := Board.kingsRookBoard_eq_black_king hsrcB
      have hattB : (Board.kingsRookBoard s.wk s.bk s.rs .white).attacks m.src m.dst = true := by
        simpa [toPosition] using hatt
      have hka : KingAttacks s.bk m.dst := by
        rw [Board.attacks_king hsrcB, hsq] at hattB
        exact of_decide_eq_true hattB
      have hplay := play_of_some s.toPosition m hsrc
      have hsideB : m.castlingSide? Color.black = none := by
        simpa [toPosition, ht] using hside rfl
      have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
      have hboard : (s.toPosition.play m).board =
          Board.kingsRookBoard s.wk m.dst s.rs .white := by
        have hpl : (s.toPosition.play m).board =
            s.toPosition.boardAfter m { color := s.toPosition.toMove, kind := .king } := by
          simp [hplay]
        rw [hpl]
        have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
        rw [this, hba, hsq]
        exact Board.relocate_kingsRookBoard_black s.wk s.bk s.rs m.dst .white
          h1 h2 h3 hdwk hdbk hdrs
      have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false := by
        simpa [toPosition, ht] using hsafe
      rw [hboard, kingIsAttacked_black_eq s.wk m.dst s.rs hdwk.symm h2 hdrs] at hsafe'
      have hpair : decide (KingAttacks s.wk m.dst) = false ∧
          rookChecks s.rs m.dst s.wk = false := by
        simpa [kingAttackedBlack, Bool.or_eq_false_iff] using hsafe'
      refine ⟨.king m.dst, ?_⟩
      simp [fastLegal, ht, bne_iff_ne.mpr hdrs, fastKingB, hka, hdwk, hdrs,
        of_decide_eq_false hpair.1, hpair.2]
  · subst hk
    cases ht : s.toMove with
    | white =>
      have hsrcR : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
          some { color := .white, kind := .rook } := by
        simpa [toPosition, ht] using hsrc
      have hsq : m.src = s.rs := Board.kingsRookBoard_eq_rook hsrcR
      have hatt0 :
          (Board.kingsRookBoard s.wk s.bk s.rs .white).attacks s.rs m.dst = true := by
        simpa [toPosition, hsq] using hatt
      obtain ⟨hR, hnw, hnb⟩ := (Board.kingsRookBoard_attacks_rook_iff h2 h3).mp hatt0
      refine ⟨.rook m.dst, ?_⟩
      simp [fastLegal, ht, fastRook, hR, hdwk, hdbk, orthoBetween_eq hR,
        decide_eq_false hnw, decide_eq_false hnb]
    | black =>
      have hsrc' : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
          some ⟨.black, .rook⟩ := by simpa [toPosition, ht] using hsrc
      unfold Board.kingsRookBoard at hsrc'
      split_ifs at hsrc' <;> cases hsrc'

theorem twoKings_of_deadB_legal {s : KRState} {m : Move}
    (hok : s.okB = true) (hd : s.deadB = true) (hm : LegalMove s.toPosition m) :
    IsTwoKings (s.toPosition.play m) := by
  have hplay := (toPosition_isKingAndRook hok).of_play hm
  cases hplay with
  | inr htk => exact htk
  | inl _ =>
    obtain ⟨_, _, hdstOr, _, _, _, _, _, _, _⟩ := kingRook_legalMove_core rfl rfl hm
    cases hdstOr with
    | inl he =>
      obtain ⟨km, hfl⟩ := fastLegal_of_legalMove_noncapture hok hm he
      exact (Bool.false_ne_true
        ((deadB_hasNoncapture_eq_false hd).symm.trans
          (hasNoncaptureLegal_of_fastLegal hfl))).elim
    | inr hrs =>
      obtain ⟨h1, h2, h3, _, _⟩ := (okB_iff s).mp hok
      have ht : s.toMove = .black :=
        destOk_toMove_of_dst_rook (p := s.toPosition) (m := m) (wk := s.wk)
          (bk := s.bk) (rs := s.rs) (c := Color.white) rfl h2 h3 hrs
          (kingRook_legalMove_core (p := s.toPosition) rfl rfl hm).2.1
      obtain ⟨hpromo, _, _, hsafe, _, piece, hsrc, hpc, hkind, hside⟩ :=
        kingRook_legalMove_core rfl rfl hm
      rcases piece with ⟨pc, pk⟩
      have hpc' : pc = .black := hpc.trans ht
      subst hpc'
      cases hkind with
      | inr hrk =>
        subst hrk
        have hsrc' : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
            some ⟨.black, .rook⟩ := by simpa [toPosition, ht] using hsrc
        unfold Board.kingsRookBoard at hsrc'
        split_ifs at hsrc' <;> cases hsrc'
      | inl hk =>
        subst hk
        have hsrcB : Board.kingsRookBoard s.wk s.bk s.rs .white m.src =
            some { color := .black, kind := .king } := by
          simpa [toPosition, ht] using hsrc
        have hsq : m.src = s.bk := Board.kingsRookBoard_eq_black_king hsrcB
        have hpl := play_of_some s.toPosition m hsrc
        have hsideB : m.castlingSide? Color.black = none := by
          simpa [toPosition, ht] using hside rfl
        have hba := boardAfter_king_no_castle s.toPosition m (c := .black) hsideB hpromo
        have hboard : (s.toPosition.play m).board = Board.kingsBoard s.wk s.rs := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this, hba, hsq, hrs]
          exact Board.relocate_capture_rook_black s.wk s.bk s.rs h1 h2 h3
        have hcast : (s.toPosition.play m).castling = ∅ := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this, hba]; exact castlingAfter_empty _
        have hep : (s.toPosition.play m).enPassant = none := by
          rw [hpl]
          have : s.toPosition.toMove = Color.black := by simp [toPosition, ht]
          rw [this]
          simp [enPassantAfter]
        have hna' : ¬ KingAttacks s.wk s.rs := by
          have hsafe' : (s.toPosition.play m).board.kingIsAttacked .black = false :=
            by simpa [ht, toPosition] using hsafe
          rw [hboard, Board.kingsBoard_kingIsAttacked_black s.wk s.rs h2] at hsafe'
          exact of_decide_eq_false hsafe'
        exact ⟨s.wk, s.rs, h2, hna', hboard, hcast, hep⟩

theorem reachable_from_deadB {s : KRState} {q : Position}
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

theorem not_CheckmateReachable_of_deadB {s : KRState} (hok : s.okB = true)
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
      allSquares.all fun rs =>
        checkState ⟨.white, ⟨f, r⟩, bk, rs⟩ &&
          checkState ⟨.black, ⟨f, r⟩, bk, rs⟩

set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile0 : checkFile 0 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile1 : checkFile 1 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile2 : checkFile 2 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile3 : checkFile 3 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile4 : checkFile 4 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile5 : checkFile 5 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
theorem checkFile6 : checkFile 6 = true := by native_decide
set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file of the 2 · 64² KR vs K states.
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

theorem progress_exists {s : KRState} (hok : s.okB = true) :
    s.mateB = true ∨ s.deadB = true ∨ ∃ s1, Progress s s1 := by
  have hcs : s.checkState = true := by
    rcases s with ⟨tm, wk, bk, rs⟩
    have hwk := (List.all_eq_true.mp checkAll_true) wk (mem_allSquares _)
    have hbk := (List.all_eq_true.mp hwk) bk (mem_allSquares _)
    have hrs := (List.all_eq_true.mp hbk) rs (mem_allSquares _)
    have hpair := Bool.and_eq_true_iff.mp hrs
    cases tm
    · exact hpair.1
    · exact hpair.2
  exact checkState_progress hok hcs

theorem dead_or_checkmate_of_okB_aux :
    ∀ n (s : KRState), s.okB = true → s.mu = n →
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

theorem checkmateReachable_of_okB_of_not_dead {s : KRState}
    (hok : s.okB = true) (hnd : s.deadB = false) :
    CheckmateReachable s.toPosition := by
  have h := dead_or_checkmate_of_okB_aux s.mu s hok rfl
  cases h with
  | inl hd => exact (Bool.false_ne_true (hnd.symm.trans hd)).elim
  | inr hcr => exact hcr

theorem checkmateReachable_iff_not_dead {s : KRState} (hok : s.okB = true) :
    CheckmateReachable s.toPosition ↔ s.deadB = false := by
  constructor
  · intro h
    cases hd : s.deadB with
    | true => exact (not_CheckmateReachable_of_deadB hok hd h).elim
    | false => rfl
  · intro hnd
    exact checkmateReachable_of_okB_of_not_dead hok hnd

/-- White to move always has a non-capturing move in a legal state. -/
theorem white_okB_hasNoncapture {wk bk rs : Square} :
    okB ⟨.white, wk, bk, rs⟩ = true →
      hasNoncaptureLegal ⟨.white, wk, bk, rs⟩ = true := by
  revert wk bk rs
  native_decide

theorem not_deadB_of_white {s : KRState} (hok : s.okB = true)
    (ht : s.toMove = .white) : s.deadB = false := by
  rcases s with ⟨tm, wk, bk, rs⟩
  subst ht
  have h := white_okB_hasNoncapture hok
  simp [deadB, h]

/-- The rook side to move can always reach checkmate. -/
theorem checkmateReachable_of_okB_white {s : KRState} (hok : s.okB = true)
    (ht : s.toMove = .white) : CheckmateReachable s.toPosition :=
  checkmateReachable_of_okB_of_not_dead hok (not_deadB_of_white hok ht)

end KRState

namespace Board

theorem between_isSome_rot180 (b : Board) (s t : Square) :
    (∃ u, Between s t u ∧ (b u).isSome = true) ↔
      (∃ u, Between s.rot180 t.rot180 u ∧ (b.rot180 u).isSome = true) := by
  constructor
  · intro ⟨u, hu, ho⟩
    refine ⟨u.rot180, (Square.between_rot180 s t u).mp hu, ?_⟩
    simpa [rot180] using ho
  · intro ⟨u, hu, ho⟩
    refine ⟨u.rot180, ?_, ?_⟩
    · have : Between s.rot180 t.rot180 (u.rot180.rot180) := by
        rwa [Square.rot180_involutive]
      exact (Square.between_rot180 s t u.rot180).mpr this
    · simpa [rot180, Square.rot180_involutive] using ho

theorem geoAttacks_rot180 (p : Piece) (s t : Square) :
    (match p.kind with
      | .pawn => decide (PawnAttacks p.color s t)
      | .knight => decide (KnightAttacks s t)
      | .king => decide (KingAttacks s t)
      | .bishop => decide (BishopAttacks s t)
      | .rook => decide (RookAttacks s t)
      | .queen => decide (QueenAttacks s t)) =
    (match p.flip.kind with
      | .pawn => decide (PawnAttacks p.flip.color s.rot180 t.rot180)
      | .knight => decide (KnightAttacks s.rot180 t.rot180)
      | .king => decide (KingAttacks s.rot180 t.rot180)
      | .bishop => decide (BishopAttacks s.rot180 t.rot180)
      | .rook => decide (RookAttacks s.rot180 t.rot180)
      | .queen => decide (QueenAttacks s.rot180 t.rot180)) := by
  revert p s t
  native_decide

theorem attacks_rot180 (b : Board) (s t : Square) :
    b.attacks s t = b.rot180.attacks s.rot180 t.rot180 := by
  cases hp : b s with
  | none =>
    have : b.rot180 s.rot180 = none := by
      simp only [rot180, hp, Square.rot180_involutive, Option.map_none]
    simp [attacks, hp, this]
  | some p =>
    have hpR : b.rot180 s.rot180 = some p.flip := by
      simp only [rot180, hp, Square.rot180_involutive, Option.map_some]
    simp only [attacks, hp, hpR]
    apply congrArg₂ (· && ·)
    · exact geoAttacks_rot180 p s t
    · apply congrArg not
      apply congrArg₂ (· && ·)
      · simp [Piece.flip]
      · rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
        exact between_isSome_rot180 b s t

theorem mem_kingSquares_rot180 (b : Board) (c : Color) (s : Square) :
    s ∈ b.kingSquares c ↔ s.rot180 ∈ b.rot180.kingSquares c.other := by
  simp only [mem_kingSquares, rot180, Square.rot180_involutive]
  cases h : b s with
  | none => simp
  | some p =>
    rcases p with ⟨pc, pk⟩
    cases pc <;> cases c <;> cases pk <;> simp [Piece.flip]

theorem kingIsAttacked_rot180 (b : Board) (c : Color) :
    b.kingIsAttacked c = b.rot180.kingIsAttacked c.other := by
  rw [Bool.eq_iff_iff, kingIsAttacked_iff_mem_attackers,
    kingIsAttacked_iff_mem_attackers]
  constructor
  · intro ⟨t, ht, s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    refine ⟨t.rot180, (mem_kingSquares_rot180 b c t).mp ht, s.rot180, ?_⟩
    rw [mem_attackers]
    constructor
    · cases hb : b s with
      | none => simp [hb] at hcol
      | some p =>
        have hpc : p.color = c.other := by simpa [hb] using hcol
        simp [rot180, Square.rot180_involutive, hb, Piece.flip, hpc]
    · rw [← attacks_rot180, hatt]
  · intro ⟨t, ht, s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    refine ⟨t.rot180, ?_, s.rot180, ?_⟩
    · have ht' : t ∈ b.rot180.kingSquares c.other := ht
      have := (mem_kingSquares_rot180 b c t.rot180).mpr
      simpa [Square.rot180_involutive] using this (by
        simpa [Square.rot180_involutive] using ht')
    · rw [mem_attackers]
      constructor
      · cases hb : b s.rot180 with
        | none =>
          have : b.rot180 s = none := by simp [rot180, hb]
          simp [this] at hcol
        | some p =>
          have hlook : b.rot180 s = some p.flip := by simp [rot180, hb]
          have hpc : p.color.other = c := by simpa [hlook, Piece.flip] using hcol
          have hpc' : p.color = c.other := by rw [← Color.other_other p.color, hpc]
          simp [hpc']
      · have h := attacks_rot180 b s.rot180 t.rot180
        have : b.rot180.attacks s t = b.attacks s.rot180 t.rot180 := by
          simpa [Square.rot180_involutive] using h.symm
        rwa [this] at hatt

end Board

namespace Position

theorem rot180_mk (b : Board) (tm : Color) (c : CastlingRights) (e : Option Square) :
    ({ board := b, toMove := tm, castling := c, enPassant := e } : Position).rot180 =
      { board := b.rot180, toMove := tm.other, castling := ∅, enPassant := none } :=
  rfl

theorem destOk_rot180 (p : Position) (m : Move) :
    p.destOk m = p.rot180.destOk m.rot180 := by
  simp only [destOk, Move.rot180_dst, rot180_board, rot180_toMove]
  cases h : p.board m.dst with
  | none => simp [Board.rot180, Square.rot180_involutive, h]
  | some q =>
    simp [Board.rot180, Square.rot180_involutive, h, Piece.flip]
    cases q.color <;> cases p.toMove <;> rfl

theorem inCheck_rot180 (p : Position) : p.inCheck = p.rot180.inCheck := by
  unfold inCheck rot180
  exact Board.kingIsAttacked_rot180 p.board p.toMove

theorem IsKingAndRook.castling_eq {p : Position} (h : IsKingAndRook p) :
    p.castling = ∅ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact hc

theorem IsKingAndRook.enPassant_eq {p : Position} (h : IsKingAndRook p) :
    p.enPassant = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, he⟩ := h
  exact he

theorem IsKingAndRook.rot180 {p : Position} (h : IsKingAndRook p) :
    IsKingAndRook p.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
  have h2' : wk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h2
  have h3' : bk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h3
  have hna' : ¬ KingAttacks bk.rot180 wk.rot180 := by
    intro hk
    exact hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
  cases c with
  | white =>
    refine ⟨bk.rot180, wk.rot180, rs.rot180, .black, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsRookBoard_white wk bk rs h1 h2 h3]
  | black =>
    refine ⟨bk.rot180, wk.rot180, rs.rot180, .white, h1', h3', h2', hna', ?_, rfl, rfl⟩
    rw [rot180_board, hboard, Board.rot180_kingsRookBoard_black wk bk rs h1 h2 h3]

theorem IsKingAndRook.not_IsTwoKings {p : Position} (h : IsKingAndRook p) :
    ¬ IsTwoKings p := by
  intro htk
  obtain ⟨wk, bk, rs, c, h1, h2, h3, _, hboard, _, _⟩ := h
  obtain ⟨wk', bk', hne', _, hboard', _, _⟩ := htk
  have h3c : p.board.occupied.card = 3 := by
    rw [hboard, Board.kingsRookBoard_occupied wk bk rs c h1 h2 h3]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [h3]
    · simp [h1, h2]
  have h2c : p.board.occupied.card = 2 := by
    rw [hboard', Board.kingsBoard_occupied wk' bk' hne']
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hne']
  omega

theorem piece_of_kind_king (piece : Piece) (hk : piece.kind = .king) :
    piece = { color := piece.color, kind := .king } := by
  rcases piece with ⟨pc, pk⟩
  subst hk
  rfl

theorem piece_of_kind_rook (piece : Piece) (hr : piece.kind = .rook) :
    piece = { color := piece.color, kind := .rook } := by
  rcases piece with ⟨pc, pk⟩
  subst hr
  rfl

theorem IsKingAndRook.play_rot180 {p : Position} {m : Move}
    (h : IsKingAndRook p) (hm : LegalMove p m) :
    (p.play m).rot180 = p.rot180.play m.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, _, hboard, hc, he⟩ := h
  obtain ⟨hpromo, _, _, _, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core hboard hc hm
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
      exact KRState.castlingSide_none_of_kingAttacks _
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
    have hpiece := piece_of_kind_rook piece hr
    have hba := boardAfter_rook p m (c := piece.color) hpromo
    have hbaR := boardAfter_rook p.rot180 m.rot180 (c := piece.flip.color)
      (by simpa [Move.rot180] using hpromo)
    have hep := enPassantAfter_rook m piece.color (p.boardAfter m piece)
    have hepR := enPassantAfter_rook m.rot180 piece.flip.color
      (p.rot180.boardAfter m.rot180 piece.flip)
    rw [hplay, hplayR, rot180_mk, hpiece, hba]
    refine Position.ext ?_ ?_ ?_ ?_
    · rw [show ({ color := piece.color, kind := PieceKind.rook } : Piece).flip =
          { color := piece.flip.color, kind := .rook } from rfl, hbaR]
      simpa [Piece.flip, Move.rot180_src, Move.rot180_dst, rot180_board] using
        Board.relocate_rot180 p.board m.src m.dst { color := piece.color, kind := .rook }
    · rw [rot180_toMove, Color.other_other]
    · rw [show p.rot180.castling = ∅ from rfl, castlingAfter_empty]
    · simp [enPassantAfter]

theorem IsKingAndRook.legalMove_rot180_of {p : Position} {m : Move}
    (h : IsKingAndRook p) (hm : LegalMove p m) :
    LegalMove p.rot180 m.rot180 := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  obtain ⟨hpromo, hdestOk, _, hsafe, hatt, piece, hsrc, hpc, hkind, hside⟩ :=
    kingRook_legalMove_core hboard hc hm
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
        exact KRState.castlingSide_none_of_kingAttacks p.rot180.toMove
          ((Square.kingAttacks_rot180 _ _).mp (hka_of_king hk))
      simp [Piece.flip, hk, hs]
    | inr hr => simp [Piece.flip, hr]
  have hattR : p.rot180.board.attacks m.rot180.src m.rot180.dst = true := by
    rw [rot180_board, Move.rot180_src, Move.rot180_dst, ← Board.attacks_rot180, hatt]
  have hsafeR :
      (p.rot180.play m.rot180).board.kingIsAttacked p.rot180.toMove = false := by
    have hpl := IsKingAndRook.play_rot180
      (⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ : IsKingAndRook p) hm
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

theorem IsKingAndRook.legalMove_rot180 {p : Position} {m : Move}
    (h : IsKingAndRook p) :
    LegalMove p m ↔ LegalMove p.rot180 m.rot180 := by
  constructor
  · exact legalMove_rot180_of h
  · intro hm
    have := legalMove_rot180_of h.rot180 (m := m.rot180) hm
    simpa [rot180_involutive h.castling_eq h.enPassant_eq, Move.rot180_involutive]
      using this

theorem IsKingAndRook.inCheckmate_rot180 {p : Position} (h : IsKingAndRook p)
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

theorem IsKingAndRook.reachable_rot180 {p : Position} (hp : IsKingAndRook p)
    {q : Position} (hr : Reachable p q) (hq : IsKingAndRook q) :
    Reachable p.rot180 q.rot180 := by
  refine Reachable.rec (motive := fun q _ => IsKingAndRook q →
      Reachable p.rot180 q.rot180) ?_ ?_ hr hq
  · intro _hq
    exact Reachable.refl
  · intro q m hrq hleg ih hq'
    have hqKR : IsKingAndRook q := by
      rcases hp.of_reachable hrq with h | htk
      · exact h
      · exact (hq'.not_IsTwoKings (htk.of_play hleg)).elim
    have hstep := Reachable.step m.rot180 (ih hqKR) (hqKR.legalMove_rot180.mp hleg)
    rwa [← hqKR.play_rot180 hleg] at hstep

theorem IsKingAndRook.checkmateReachable_rot180 {p : Position}
    (h : IsKingAndRook p) :
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
rook, and no remaining castling rights, holds only the two kings and that
rook, with the kings not adjacent. Castling rights are an extra hypothesis:
a rook on `a1`/`h1` with its king on `e1` could otherwise still have rights. -/
theorem isKingAndRook_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 3)
    (hrook : ∃ s c, p.board s = some { color := c, kind := .rook })
    (hcstl : p.castling = ∅) :
    IsKingAndRook p := by
  obtain ⟨hbv, hopp, _, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  obtain ⟨rs, c, hrs⟩ := hrook
  have hwk_bk : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hwk_rs : wk ≠ rs := by
    intro heq
    have hking : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    rw [heq] at hking
    exact some_king_ne_rook (hking.symm.trans hrs)
  have hbk_rs : bk ≠ rs := by
    intro heq
    have hking : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hking
    exact some_king_ne_rook (hking.symm.trans hrs)
  have hoccEq : p.board.occupied = {wk, bk, rs} := by
    have hsub : ({wk, bk, rs} : Finset Square) ⊆ p.board.occupied := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with h | h | h
      · have hking : p.board wk = some { color := .white, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
        simp [Board.mem_occupied, h, hking]
      · have hking : p.board bk = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        simp [Board.mem_occupied, h, hking]
      · simp [Board.mem_occupied, h, hrs]
    have hcard : ({wk, bk, rs} : Finset Square).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simp [hbk_rs]
      · simp [hwk_bk, hwk_rs]
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hocc, hcard])).symm
  have hboard : p.board = Board.kingsRookBoard wk bk rs c := by
    funext s
    by_cases hw : s = wk
    · rw [hw, Board.kingsRookBoard_white]
      exact (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    · by_cases hb : s = bk
      · rw [hb, Board.kingsRookBoard_black wk bk rs c hwk_bk]
        exact (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
      · by_cases hs : s = rs
        · rw [hs, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs]
          exact hrs
        · have hsocc : s ∉ p.board.occupied := by
            rw [hoccEq]
            simp [hw, hb, hs]
          rw [eq_none_of_not_mem_occupied hsocc,
            Board.kingsRookBoard_other wk bk rs s c hw hb hs]
  have hna : ¬ KingAttacks wk bk := by
    intro hk
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .black = true := by
        rw [hboard]
        exact (Board.kingsRookBoard_kingIsAttacked_black wk bk rs c
          hwk_bk hwk_rs hbk_rs).mpr (Or.inl hk)
      exact Bool.false_ne_true (hopp'.symm.trans htrue)
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      have htrue : p.board.kingIsAttacked .white = true := by
        rw [hboard]
        exact (Board.kingsRookBoard_kingIsAttacked_white wk bk rs c
          hwk_bk hwk_rs hbk_rs).mpr (Or.inl (kingAttacks_symmetric.mp hk))
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
      · rw [hsq, hboard, Board.kingsRookBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsRookBoard_black wk bk rs c hwk_bk] at hpawn
        cases some_king_ne_pawn hpawn
      · rw [hsq, hboard, Board.kingsRookBoard_rook wk bk rs c hwk_rs hbk_rs] at hpawn
        cases some_rook_ne_pawn hpawn
  exact ⟨wk, bk, rs, c, hwk_bk, hwk_rs, hbk_rs, hna, hboard, hcstl, he⟩

theorem exists_krState_white {p : Position} (hv : Valid p)
    {wk bk rs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsRookBoard wk bk rs .white)
    (hc : p.castling = ∅) (he : p.enPassant = none) :
    ∃ s : KRState, s.okB = true ∧ s.toPosition = p := by
  refine ⟨⟨p.toMove, wk, bk, rs⟩, ?_, ?_⟩
  · rw [KRState.okB_iff]
    refine ⟨h1, h2, h3, hna, ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have hopp' : (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .black =
          false := by simpa [ht] using hopp
      simpa [KRState.inCheckB, KRState.kingIsAttacked_black_eq wk bk rs h1 h2 h3] using hopp'
    | black =>
      have hopp' : (Board.kingsRookBoard wk bk rs .white).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      simpa [KRState.inCheckB, KRState.kingIsAttacked_white_eq wk bk rs h1 h2 h3] using hopp'
  · rcases p with ⟨board, toMove, castling, enPassant⟩
    simp only at hboard hc he
    subst hboard hc he
    rfl

theorem exists_krState_black {p : Position} (hv : Valid p)
    {wk bk rs : Square}
    (h1 : wk ≠ bk) (h2 : wk ≠ rs) (h3 : bk ≠ rs) (hna : ¬ KingAttacks wk bk)
    (hboard : p.board = Board.kingsRookBoard wk bk rs .black)
    (_hc : p.castling = ∅) (_he : p.enPassant = none) :
    ∃ s : KRState, s.okB = true ∧ s.toPosition = p.rot180 := by
  let s : KRState := ⟨p.toMove.other, bk.rot180, wk.rot180, rs.rot180⟩
  refine ⟨s, ?_, ?_⟩
  · have h1' : bk.rot180 ≠ wk.rot180 := mt Board.rot180_injective (Ne.symm h1)
    have h2' : wk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h2
    have h3' : bk.rot180 ≠ rs.rot180 := mt Board.rot180_injective h3
    have hna' : ¬ KingAttacks bk.rot180 wk.rot180 :=
      fun hk => hna (kingAttacks_symmetric.mp ((Square.kingAttacks_rot180 bk wk).mpr hk))
    rw [KRState.okB_iff]
    refine ⟨h1', h3', h2', hna', ?_⟩
    have hopp := hv.2.1
    rw [hboard] at hopp
    cases ht : p.toMove with
    | white =>
      have : s.toMove.other = .white := by simp [s, ht]
      rw [this]
      simpa [s, KRState.inCheckB, KRState.kingAttackedWhite] using hna'
    | black =>
      have hopp' : (Board.kingsRookBoard wk bk rs .black).kingIsAttacked .white =
          false := by simpa [ht] using hopp
      have hiff := Board.kingsRookBoard_kingIsAttacked_white wk bk rs .black h1 h2 h3
      have hn : ¬ (KingAttacks bk wk ∨
          (Color.black = .black ∧ RookAttacks rs wk ∧ ¬ Between rs wk bk)) := by
        intro h'
        exact Bool.false_ne_true (hopp'.symm.trans (hiff.mpr h'))
      have : s.toMove.other = .black := by simp [s, ht]
      rw [this]
      unfold KRState.inCheckB KRState.kingAttackedBlack
      simp only [Bool.or_eq_false_iff]
      refine ⟨decide_eq_false (by simpa [s] using hna'), ?_⟩
      cases hrc : KRState.rookChecks s.rs s.bk s.wk
      · rfl
      · have ⟨hR, hnb⟩ := (KRState.rookChecks_iff s.rs s.bk s.wk).mp hrc
        exact False.elim (hn (Or.inr ⟨rfl,
          (Square.rookAttacks_rot180 rs wk).mpr (by simpa [s] using hR),
          mt (Square.between_rot180 rs wk bk).mp (by simpa [s] using hnb)⟩))
  · simp [s, KRState.toPosition, rot180, hboard,
      Board.rot180_kingsRookBoard_black wk bk rs h1 h2 h3]

theorem exists_krState {p : Position} (hv : Valid p) (h : IsKingAndRook p) :
    (∃ s : KRState, s.okB = true ∧ s.toPosition = p) ∨
      (∃ s : KRState, s.okB = true ∧ s.toPosition = p.rot180) := by
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  cases c with
  | white => exact Or.inl (exists_krState_white hv h1 h2 h3 hna hboard hc he)
  | black => exact Or.inr (exists_krState_black hv h1 h2 h3 hna hboard hc he)

theorem IsKingAndRook.checkmateReachable_of_not_dead {p : Position}
    (_hv : Valid p) (h : IsKingAndRook p) {s : KRState}
    (hok : s.okB = true) (hnd : s.deadB = false)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p := by
  have hcr := KRState.checkmateReachable_of_okB_of_not_dead hok hnd
  rcases hpos with hpos | hpos
  · rwa [hpos] at hcr
  · rw [h.checkmateReachable_rot180]
    rwa [hpos] at hcr

theorem IsKingAndRook.checkmateReachable_iff_deadB {p : Position}
    (hv : Valid p) (h : IsKingAndRook p) {s : KRState}
    (hok : s.okB = true)
    (hpos : s.toPosition = p ∨ s.toPosition = p.rot180) :
    CheckmateReachable p ↔ s.deadB = false := by
  constructor
  · intro hcr
    have hiff := KRState.checkmateReachable_iff_not_dead hok
    rcases hpos with hpos | hpos
    · rw [← hpos] at hcr
      exact hiff.mp hcr
    · rw [h.checkmateReachable_rot180] at hcr
      rw [← hpos] at hcr
      exact hiff.mp hcr
  · intro hnd
    exact h.checkmateReachable_of_not_dead hv hok hnd hpos

/-- If the player to move owns the rook, checkmate is reachable. -/
theorem IsKingAndRook.checkmateReachable_of_rookToMove {p : Position}
    (hv : Valid p) (h : IsKingAndRook p)
    (hr : ∃ s, p.board s = some { color := p.toMove, kind := .rook }) :
    CheckmateReachable p := by
  have hKR : IsKingAndRook p := h
  obtain ⟨wk, bk, rs, c, h1, h2, h3, hna, hboard, hc, he⟩ := h
  have ht : p.toMove = c := by
    obtain ⟨sq, hsq⟩ := hr
    have hsqb : Board.kingsRookBoard wk bk rs c sq =
        some { color := p.toMove, kind := .rook } := by rwa [hboard] at hsq
    have hsqrs : sq = rs := by
      unfold Board.kingsRookBoard at hsqb
      split_ifs at hsqb <;>
        first | cases some_king_ne_rook hsqb | assumption
    rw [hsqrs, Board.kingsRookBoard_rook wk bk rs c h2 h3] at hsqb
    injection hsqb with hpiece
    injection hpiece with hcol _
    exact hcol.symm
  cases c with
  | white =>
    obtain ⟨s, hok, hpos⟩ := exists_krState_white hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, ht]
    have hcr := KRState.checkmateReachable_of_okB_white hok this
    rwa [hpos] at hcr
  | black =>
    obtain ⟨s, hok, hpos⟩ := exists_krState_black hv h1 h2 h3 hna hboard hc he
    have : s.toMove = .white := by
      change s.toPosition.toMove = .white
      rw [hpos, rot180_toMove, ht]
      rfl
    have hcr := KRState.checkmateReachable_of_okB_white hok this
    rw [hKR.checkmateReachable_rot180]
    rwa [hpos] at hcr

/-- If `a` is the unique element of `l` satisfying `p`, then `find?` returns it. -/
theorem find?_eq_some_of_unique {α} {p : α → Bool} {a : α} {l : List α}
    (hm : a ∈ l) (hp : p a = true) (hu : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => simp at hm
  | cons b l ih =>
    simp only [List.find?]
    split
    · next hb =>
      congr
      exact hu b (List.mem_cons_self ..) hb
    · next hb =>
      apply ih
      · simp only [List.mem_cons] at hm
        rcases hm with rfl | h
        · simp [hp] at hb
        · exact h
      · intro c hc hc'
        exact hu c (List.mem_cons_of_mem _ hc) hc'

theorem ofPositionWhite?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPositionWhite? p = some s) :
    s.okB = true ∧ s.toPosition = p := by
  unfold KRState.ofPositionWhite? at h
  split at h
  · rename_i wk bk rs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      have hboard : p.board = Board.kingsRookBoard wk bk rs .white := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KRState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      rfl
  · cases h

theorem ofPositionBlack?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPositionBlack? p = some s) :
    s.okB = true ∧ s.toPosition = p.rot180 := by
  unfold KRState.ofPositionBlack? at h
  split at h
  · rename_i wk bk rs _ _ _
    split_ifs at h with hcond
    · injection h with hs
      subst hs
      have ⟨hrest, hep⟩ := Bool.and_eq_true_iff.mp hcond
      have ⟨hrest2, hcst⟩ := Bool.and_eq_true_iff.mp hrest
      have ⟨hok, hall⟩ := Bool.and_eq_true_iff.mp hrest2
      refine ⟨hok, ?_⟩
      obtain ⟨h1s, h2s, h3s, _, _⟩ := (KRState.okB_iff _).mp hok
      have hwk_bk : wk ≠ bk := fun heq => h1s (by simp [heq])
      have hwk_rs : wk ≠ rs := fun heq => h3s (by simp [heq])
      have hbk_rs : bk ≠ rs := fun heq => h2s (by simp [heq])
      have hboard : p.board = Board.kingsRookBoard wk bk rs .black := by
        funext q
        exact beq_iff_eq.mp (List.all_eq_true.mp hall q (KRState.mem_allSquares q))
      have hcst' : p.castling = ∅ := of_decide_eq_true hcst
      have hep' : p.enPassant = none := of_decide_eq_true hep
      rcases p with ⟨b, tm, cst, ep⟩
      simp only at hboard hcst' hep'
      subst hboard hcst' hep'
      simp [KRState.toPosition, rot180,
        Board.rot180_kingsRookBoard_black wk bk rs hwk_bk hwk_rs hbk_rs]
  · cases h

theorem ofPositionWhite?_of_eq {p : Position} {s : KRState}
    (hok : s.okB = true) (hpos : s.toPosition = p) :
    KRState.ofPositionWhite? p = some s := by
  have hboard : p.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
    rw [← hpos]; rfl
  have htm : p.toMove = s.toMove := by
    have : s.toPosition.toMove = p.toMove := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  have hcst : p.castling = ∅ := by
    have : s.toPosition.castling = p.castling := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  have hep : p.enPassant = none := by
    have : s.toPosition.enPassant = p.enPassant := by rw [hpos]
    simpa [KRState.toPosition] using this.symm
  obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
  have hwk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.wk := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsRookBoard_white])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.bk := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_black s.wk s.bk s.rs .white h1])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .rook }) = some s.rs := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_rook s.wk s.bk s.rs .white h2 h3])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_rook (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KRState.allSquares.all fun q =>
      p.board q == Board.kingsRookBoard s.wk s.bk s.rs .white q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove, s.wk, s.bk, s.rs⟩ : KRState) = s := by
    cases s
    simp [htm]
  unfold KRState.ofPositionWhite?
  rw [hwk, hbk, hrs]
  simp [hs, hok, hall, hcst, hep]

theorem ofPositionBlack?_of_eq {p : Position} {s : KRState}
    (hok : s.okB = true) (hpos : s.toPosition = p.rot180)
    (hcst : p.castling = ∅) (hep : p.enPassant = none) :
    KRState.ofPositionBlack? p = some s := by
  obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
  have hboardR : p.rot180.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
    rw [← hpos]; rfl
  have hboard : p.board =
      Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180 .black := by
    have hrot := congrArg Board.rot180 hboardR
    rw [rot180_board, Board.board_rot180_involutive,
      Board.rot180_kingsRookBoard_white s.wk s.bk s.rs h1 h2 h3] at hrot
    exact hrot
  have htm : p.toMove.other = s.toMove := by
    have : s.toPosition.toMove = p.rot180.toMove := by rw [hpos]
    simpa [KRState.toPosition, rot180_toMove] using this.symm
  have hneWB : s.bk.rot180 ≠ s.wk.rot180 := Ne.symm (mt Board.rot180_injective h1)
  have hneWR : s.wk.rot180 ≠ s.rs.rot180 := mt Board.rot180_injective h2
  have hneBR : s.bk.rot180 ≠ s.rs.rot180 := mt Board.rot180_injective h3
  have hwk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .king }) = some s.bk.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by rw [hboard, Board.kingsRookBoard_white])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_white_king (hboard ▸ beq_iff_eq.mp hq)
  have hbk : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .king }) = some s.wk.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_black s.bk.rot180 s.wk.rot180 s.rs.rot180
          .black hneWB])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_black_king (hboard ▸ beq_iff_eq.mp hq)
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .black, kind := .rook }) = some s.rs.rot180 := by
    refine find?_eq_some_of_unique (KRState.mem_allSquares _) ?_ ?_
    · exact beq_iff_eq.mpr (by
        rw [hboard, Board.kingsRookBoard_rook s.bk.rot180 s.wk.rot180 s.rs.rot180
          .black hneBR hneWR])
    · intro q _ hq
      exact Board.kingsRookBoard_eq_rook (hboard ▸ beq_iff_eq.mp hq)
  have hall : (KRState.allSquares.all fun q =>
      p.board q == Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180
        .black q) = true := by
    refine List.all_eq_true.mpr ?_
    intro q _
    exact beq_iff_eq.mpr (by rw [hboard])
  have hs : (⟨p.toMove.other, s.wk, s.bk, s.rs⟩ : KRState) = s := by
    cases s
    simp [htm]
  unfold KRState.ofPositionBlack?
  rw [hwk, hbk, hrs]
  simp [Square.rot180_involutive, hs, hok, hall, hcst, hep]

theorem ofPositionWhite?_eq_none_of_black {p : Position} {wk bk rs : Square}
    (hboard : p.board = Board.kingsRookBoard wk bk rs .black) :
    KRState.ofPositionWhite? p = none := by
  have hrs : KRState.allSquares.find? (fun q =>
      p.board q == some { color := .white, kind := .rook }) = none := by
    refine List.find?_eq_none.mpr ?_
    intro q _
    cases hb : (p.board q == some { color := .white, kind := .rook })
    · exact Bool.false_ne_true
    · have heq : p.board q = some { color := .white, kind := .rook } :=
        beq_iff_eq.mp hb
      rw [hboard] at heq
      unfold Board.kingsRookBoard at heq
      split_ifs at heq <;> cases heq
  unfold KRState.ofPositionWhite?
  rw [hrs]
  split
  · rename_i _ _ _ heq
    cases heq
  · rfl

theorem ofPosition?_eq_some {p : Position} {s : KRState}
    (h : KRState.ofPosition? p = some s) :
    s.okB = true ∧ (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  unfold KRState.ofPosition? at h
  split at h
  · rename_i s' hW
    injection h with hs
    subst hs
    have ⟨hok, hpos⟩ := ofPositionWhite?_eq_some hW
    exact ⟨hok, Or.inl hpos⟩
  · have ⟨hok, hpos⟩ := ofPositionBlack?_eq_some h
    exact ⟨hok, Or.inr hpos⟩

theorem ofPosition?_complete {p : Position} (hv : Valid p) (h : IsKingAndRook p) :
    ∃ s, KRState.ofPosition? p = some s ∧ s.okB = true ∧
      (s.toPosition = p ∨ s.toPosition = p.rot180) := by
  rcases exists_krState hv h with ⟨s, hok, hpos⟩ | ⟨s, hok, hpos⟩
  · refine ⟨s, ?_, hok, Or.inl hpos⟩
    unfold KRState.ofPosition?
    rw [ofPositionWhite?_of_eq hok hpos]
  · refine ⟨s, ?_, hok, Or.inr hpos⟩
    obtain ⟨h1, h2, h3, _, _⟩ := (KRState.okB_iff s).mp hok
    have hboardR : p.rot180.board = Board.kingsRookBoard s.wk s.bk s.rs .white := by
      rw [← hpos]; rfl
    have hboard : p.board =
        Board.kingsRookBoard s.bk.rot180 s.wk.rot180 s.rs.rot180 .black := by
      have hrot := congrArg Board.rot180 hboardR
      rw [rot180_board, Board.board_rot180_involutive,
        Board.rot180_kingsRookBoard_white s.wk s.bk s.rs h1 h2 h3] at hrot
      exact hrot
    unfold KRState.ofPosition?
    rw [ofPositionWhite?_eq_none_of_black hboard,
      ofPositionBlack?_of_eq hok hpos h.castling_eq h.enPassant_eq]

/-- The engineered mating line of a king-and-rook versus king position;
`[]` when the position is dead or not of this material. Black-rook
positions are rotated into the white-rook frame, and the resulting moves
are rotated back. -/
def kingRookMatingLine (p : Position) : List Move :=
  match KRState.ofPositionWhite? p with
  | some s => s.matingLine
  | none =>
    match KRState.ofPositionBlack? p with
    | some s => s.matingLine.map Move.rot180
    | none => []

/-- Whether a king-and-rook versus king position is dead for helpmate
(`true` when the board is not of this material). -/
def kingRookDead (p : Position) : Bool :=
  match KRState.ofPosition? p with
  | some s => s.deadB
  | none => true

/-- In a valid king-and-rook versus king position, checkmate is reachable
exactly when the corresponding three-piece state is not dead. -/
theorem IsKingAndRook.checkmateReachable_iff {p : Position}
    (hv : Valid p) (h : IsKingAndRook p) :
    CheckmateReachable p ↔ kingRookDead p = false := by
  obtain ⟨s, hs, hok, hpos⟩ := ofPosition?_complete hv h
  have hdeq : kingRookDead p = s.deadB := by simp [kingRookDead, hs]
  rw [hdeq]
  exact h.checkmateReachable_iff_deadB hv hok hpos

/-- Decides whether checkmate is reachable from a valid king-and-rook
versus king position: exactly when the corresponding three-piece state
is not dead. -/
def kingRookCheckmateReachable (p : Position) (hv : Valid p)
    (h : IsKingAndRook p) : Decidable (CheckmateReachable p) :=
  decidable_of_iff (kingRookDead p = false) (h.checkmateReachable_iff hv).symm

/-! ### Example: kings on `e1` and `e8`, white rook on `a1` -/

/-- White king on `e1`, black king on `e8`, white rook on `a1`, White to
move. -/
def kingRookStart : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else if s = Square.a1 then some { color := .white, kind := .rook }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingRookStart_isValid : isValid kingRookStart = true := by
  native_decide

theorem kingRookStart_valid : Valid kingRookStart :=
  (isValid_eq_true_iff _).mp kingRookStart_isValid

theorem kingRookStart_isKingAndRook : IsKingAndRook kingRookStart :=
  isKingAndRook_of_valid kingRookStart_valid (by native_decide)
    ⟨Square.a1, Color.white, by native_decide⟩ (by native_decide)

theorem kingRookStart_CheckmateReachable : CheckmateReachable kingRookStart :=
  kingRookStart_isKingAndRook.checkmateReachable_of_rookToMove kingRookStart_valid
    ⟨Square.a1, by native_decide⟩

theorem kingRookStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingRookStart)
      (kingRookCheckmateReachable kingRookStart kingRookStart_valid
        kingRookStart_isKingAndRook) = true := by
  native_decide

theorem kingRookStart_not_deadPosition : ¬ DeadPosition kingRookStart :=
  not_deadPosition_of_checkmateReachable kingRookStart_CheckmateReachable

theorem kingRookStart_matingLine_legal :
    pathLegal kingRookStart (kingRookMatingLine kingRookStart) = true := by
  native_decide

theorem kingRookStart_matingLine_inCheckmate :
    (playSeq kingRookStart (kingRookMatingLine kingRookStart)).inCheckmate = true := by
  native_decide

theorem kingRookStart_CheckmateReachable' : CheckmateReachable kingRookStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingRookStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingRookStart_matingLine_inCheckmate)

/-- Forced capture of an unprotected rook: Black to move, in check, and
the only legal move takes the rook, leaving two kings. -/
def rookForcedCapture : Position where
  board := fun s =>
    if s = Square.c8 then some { color := .white, kind := .king }
    else if s = Square.a8 then some { color := .black, kind := .king }
    else if s = Square.a7 then some { color := .white, kind := .rook }
    else none
  toMove := .black
  castling := CastlingRights.empty
  enPassant := none

theorem rookForcedCapture_isValid : isValid rookForcedCapture = true := by
  native_decide

theorem rookForcedCapture_valid : Valid rookForcedCapture :=
  (isValid_eq_true_iff _).mp rookForcedCapture_isValid

theorem rookForcedCapture_isKingAndRook : IsKingAndRook rookForcedCapture :=
  isKingAndRook_of_valid rookForcedCapture_valid (by native_decide)
    ⟨Square.a7, Color.white, by native_decide⟩ (by native_decide)

theorem rookForcedCapture_deadB : ∃ s : KRState, s.okB = true ∧
    s.toPosition = rookForcedCapture ∧ s.deadB = true := by
  refine ⟨⟨.black, Square.c8, Square.a8, Square.a7⟩, by native_decide, ?_,
    by native_decide⟩
  have hboard : Board.kingsRookBoard Square.c8 Square.a8 Square.a7 .white =
      rookForcedCapture.board := by
    funext q
    simp [rookForcedCapture, Board.kingsRookBoard]
  simp [KRState.toPosition, rookForcedCapture, hboard, CastlingRights.empty]

theorem rookForcedCapture_not_CheckmateReachable :
    ¬ CheckmateReachable rookForcedCapture := by
  obtain ⟨s, hok, hpos, hd⟩ := rookForcedCapture_deadB
  intro hcr
  have := (rookForcedCapture_isKingAndRook.checkmateReachable_iff_deadB
    rookForcedCapture_valid hok (Or.inl hpos)).mp hcr
  exact Bool.false_ne_true (this.symm.trans hd)

theorem rookForcedCapture_decide_CheckmateReachable :
    @decide (CheckmateReachable rookForcedCapture)
      (kingRookCheckmateReachable rookForcedCapture rookForcedCapture_valid
        rookForcedCapture_isKingAndRook) = false := by
  native_decide

theorem rookStalemate_isKingAndRook : IsKingAndRook rookStalemate :=
  isKingAndRook_of_valid
    ((isValid_eq_true_iff rookStalemate).mp rookStalemate_isValid)
    (by native_decide) ⟨Square.g7, Color.white, by native_decide⟩ (by native_decide)

theorem rookStalemate_not_CheckmateReachable :
    ¬ CheckmateReachable rookStalemate :=
  not_CheckmateReachable_of_InStalemate
    ((inStalemate_eq_true_iff _).mp rookStalemate_inStalemate)

theorem rookStalemate_decide_CheckmateReachable :
    @decide (CheckmateReachable rookStalemate)
      (kingRookCheckmateReachable rookStalemate
        ((isValid_eq_true_iff rookStalemate).mp rookStalemate_isValid)
        rookStalemate_isKingAndRook) = false := by
  native_decide

theorem rookStalemate_deadPosition : DeadPosition rookStalemate :=
  (DeadPosition_iff_not_CheckmateReachable _).mpr
    rookStalemate_not_CheckmateReachable

end Position

end Chess



