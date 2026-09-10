import Chess.Board
import Chess.Geometry
import Mathlib.Data.Fintype.Basic

/-!
# Valid boards

A placement is valid when it satisfies the structural constraints of a
legal chess snapshot: at most one piece per square (already true of every
`Board`), exactly one king per player, at most sixteen pieces per
player, no pawns on the first or last ranks, and at least one king not
under attack.

Occupied-board attacks used for the last condition respect blocking
pieces on sliding rays. Empty-board geometry in `Chess.Geometry` is
unchanged.
-/

namespace Chess

namespace Board

/-- Whether the piece on `s`, if any, attacks `t`, taking occupancy into
account. Sliding pieces (bishop, rook, queen) require a clear path. -/
def attacks (b : Board) (s t : Square) : Bool :=
  match b s with
  | none => false
  | some p =>
    let geo : Bool :=
      match p.kind with
      | .pawn => decide (PawnAttacks p.color s t)
      | .knight => decide (KnightAttacks s t)
      | .king => decide (KingAttacks s t)
      | .bishop => decide (BishopAttacks s t)
      | .rook => decide (RookAttacks s t)
      | .queen => decide (QueenAttacks s t)
    let blocked : Bool :=
      p.kind.isSlider &&
        decide (∃ u : Square, Between s t u ∧ (b u).isSome = true)
    geo && !blocked

/-- Squares occupied by pieces of color `c` that attack `t`. -/
def attackers (b : Board) (c : Color) (t : Square) : Finset Square :=
  Finset.univ.filter fun s =>
    (b s).map (·.color) = some c ∧ b.attacks s t = true

theorem mem_attackers (b : Board) (c : Color) (s t : Square) :
    s ∈ b.attackers c t ↔
      (b s).map (·.color) = some c ∧ b.attacks s t = true := by
  simp [attackers]

/-- Whether square `t` is attacked by at least one piece of color `c`. -/
def isAttackedBy (b : Board) (c : Color) (t : Square) : Bool :=
  decide (∃ s : Square, (b s).map (·.color) = some c ∧ b.attacks s t = true)

/-- Whether a king of color `c` occupies a square attacked by the
opposite color. -/
def kingIsAttacked (b : Board) (c : Color) : Bool :=
  decide (∃ t ∈ b.kingSquares c, ∃ s : Square,
    (b s).map (·.color) = some c.other ∧ b.attacks s t = true)

/-- Whether a king of color `c` occupies a square attacked by two or
more opposing pieces. -/
def kingIsDoubleAttacked (b : Board) (c : Color) : Bool :=
  decide (∃ t ∈ b.kingSquares c, 2 ≤ (b.attackers c.other t).card)

theorem kingIsAttacked_iff_mem_attackers (b : Board) (c : Color) :
    b.kingIsAttacked c = true ↔
      ∃ t ∈ b.kingSquares c, ∃ s, s ∈ b.attackers c.other t := by
  simp [kingIsAttacked, mem_attackers]

theorem kingIsDoubleAttacked_iff (b : Board) (c : Color) :
    b.kingIsDoubleAttacked c = true ↔
      ∃ t ∈ b.kingSquares c, 2 ≤ (b.attackers c.other t).card := by
  simp [kingIsDoubleAttacked]

/-- Double attack on a king is a special case of being attacked. -/
theorem kingIsDoubleAttacked_implies_kingIsAttacked
    (b : Board) (c : Color) (h : b.kingIsDoubleAttacked c = true) :
    b.kingIsAttacked c = true := by
  rw [kingIsDoubleAttacked_iff] at h
  rw [kingIsAttacked_iff_mem_attackers]
  obtain ⟨t, ht, hcard⟩ := h
  have hpos : 0 < (b.attackers c.other t).card :=
    Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hcard
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨t, ht, s, hs⟩

/-- Whether a pawn occupies the first or last rank on this square. -/
def isPawnOnBackRank (b : Board) (s : Square) : Bool :=
  match b s with
  | some p => (p.kind == .pawn) && (s.rank.val == 0 || s.rank.val == 7)
  | none => false

/-- Whether every pawn stands off the first and last ranks. -/
def noPawnOnBackRank (b : Board) : Bool :=
  (Finset.univ.filter fun s => b.isPawnOnBackRank s).card == 0

/-- Whether `b` is a valid placement.

* At most one piece per square (true of every `Board` by construction)
* each player has exactly one king
* each player has at most 16 pieces
* no pawns on the first or last ranks
* at least one king is not under attack -/
def isValid (b : Board) : Bool :=
  decide ((b.kingSquares .white).card = 1) &&
  decide ((b.kingSquares .black).card = 1) &&
  decide ((b.occupiedBy .white).card ≤ 16) &&
  decide ((b.occupiedBy .black).card ≤ 16) &&
  b.noPawnOnBackRank &&
  (!b.kingIsAttacked .white || !b.kingIsAttacked .black)

/-- A placement that satisfies the structural constraints of a legal chess
snapshot. `Board` already places at most one piece per square. -/
def Valid (b : Board) : Prop :=
  (∀ c, (b.kingSquares c).card = 1) ∧
  (∀ c, (b.occupiedBy c).card ≤ 16) ∧
  b.noPawnOnBackRank = true ∧
  ∃ c, b.kingIsAttacked c = false

instance {b : Board} : Decidable (Valid b) := by
  unfold Valid
  infer_instance

theorem isValid_eq_true_iff (b : Board) : isValid b = true ↔ Valid b := by
  constructor
  · intro h
    simp only [isValid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hkw, hkb⟩, how⟩, hob⟩, hp⟩, hchk⟩ := h
    refine ⟨?kings, ?pieces, hp, ?check⟩
    · intro c
      cases c with
      | .white => exact hkw
      | .black => exact hkb
    · intro c
      cases c with
      | .white => exact how
      | .black => exact hob
    · cases hchk with
      | inl h => exact ⟨.white, h⟩
      | inr h => exact ⟨.black, h⟩
  · intro ⟨hk, ho, hp, ⟨c, hc⟩⟩
    simp only [isValid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨hk .white, hk .black⟩, ho .white⟩, ho .black⟩, hp⟩, ?_⟩
    cases c with
    | .white => exact Or.inl hc
    | .black => exact Or.inr hc

/-- Neither king is under attack in the starting position. -/
theorem starting_kings_not_attacked (c : Color) :
    starting.kingIsAttacked c = false := by
  cases c <;> native_decide

/-- Starting pawns occupy ranks 2 and 7 only. -/
theorem starting_noPawnOnBackRank : starting.noPawnOnBackRank = true := by
  native_decide

/-- The standard starting position is valid: one king and sixteen pieces
per side, pawns off the back ranks, and neither king under attack. -/
theorem starting_valid : Valid starting :=
  ⟨starting_kingSquares_card,
    fun c => le_of_eq (starting_occupiedBy_card c),
    starting_noPawnOnBackRank,
    ⟨.white, starting_kings_not_attacked .white⟩⟩

theorem starting_isValid : isValid starting = true :=
  (isValid_eq_true_iff starting).mpr starting_valid

/-- A sliding piece does not attack through a blocker: the black rook on
`e8` does not check the white king on `e1` while a pawn occupies `e2`. -/
theorem attacks_blocked_by_occupancy :
    let b : Board := fun s =>
      if s = Square.e1 then some { color := .white, kind := .king }
      else if s = Square.e8 then some { color := .black, kind := .rook }
      else if s = Square.e2 then some { color := .white, kind := .pawn }
      else none
    b.attacks Square.e8 Square.e1 = false := by
  native_decide

/-- With the e-file vacant, that rook does attack `e1`. -/
theorem attacks_rook_clear_e_file :
    let b : Board := fun s =>
      if s = Square.e1 then some { color := .white, kind := .king }
      else if s = Square.e8 then some { color := .black, kind := .rook }
      else none
    b.attacks Square.e8 Square.e1 = true := by
  native_decide

/-! ### Invalid (and barely valid) examples -/

/-- No pieces at all: each player lacks a king. -/
def empty : Board := fun _ => none

theorem empty_not_valid : isValid empty = false := by
  native_decide

/-- Two white kings. -/
def twoWhiteKings : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.d1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else none

theorem twoWhiteKings_not_valid : isValid twoWhiteKings = false := by
  native_decide

/-- Seventeen white pieces: the starting army plus a queen on `d4`. -/
def extraWhiteQueen : Board := fun s =>
  if s = Square.d4 then some { color := .white, kind := .queen }
  else starting s

theorem extraWhiteQueen_not_valid : isValid extraWhiteQueen = false := by
  native_decide

/-- A white pawn on the first rank. -/
def pawnOnFirstRank : Board := fun s =>
  if s = Square.a1 then some { color := .white, kind := .pawn }
  else if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else none

theorem pawnOnFirstRank_not_valid : isValid pawnOnFirstRank = false := by
  native_decide

/-- A white pawn on the last rank. -/
def pawnOnLastRank : Board := fun s =>
  if s = Square.a8 then some { color := .white, kind := .pawn }
  else if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else none

theorem pawnOnLastRank_not_valid : isValid pawnOnLastRank = false := by
  native_decide

/-- Adjacent kings attack each other, so both are under attack. -/
def adjacentKings : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.d2 then some { color := .black, kind := .king }
  else none

theorem adjacentKings_not_valid : isValid adjacentKings = false := by
  native_decide

/-- Both kings are in check from opposing rooks. -/
def bothKingsInCheck : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else if s = Square.a1 then some { color := .black, kind := .rook }
  else if s = Square.a8 then some { color := .white, kind := .rook }
  else none

theorem bothKingsInCheck_not_valid : isValid bothKingsInCheck = false := by
  native_decide

/-- Black's king is in check from a white rook; White's king is safe.
This is still valid: only both kings in check is forbidden. -/
def blackInCheck : Board := fun s =>
  if s = Square.e1 then some { color := .white, kind := .king }
  else if s = Square.e8 then some { color := .black, kind := .king }
  else if s = Square.e4 then some { color := .white, kind := .rook }
  else none

theorem blackInCheck_valid : isValid blackInCheck = true := by
  native_decide

end Board

end Chess
