import Chess.Checkmate

/-!
# Two kings

A valid position whose board holds only the two kings is never checkmate:
the kings cannot stand on adjacent squares (that would put both in check),
so the player to move is not in check. A legal move from such a position
is a king step onto an empty square not attacked by the other king, and
therefore yields another two-king position that is again not checkmate.
Hence no sequence of legal moves produces checkmate.
-/

namespace Chess

namespace Board

/-- The unique placement of a white king on `wk` and a black king on `bk`. -/
def kingsBoard (wk bk : Square) : Board := fun s =>
  if s = wk then some { color := .white, kind := .king }
  else if s = bk then some { color := .black, kind := .king }
  else none

theorem kingsBoard_white (wk bk : Square) :
    kingsBoard wk bk wk = some { color := .white, kind := .king } := by
  simp [kingsBoard]

theorem kingsBoard_black (wk bk : Square) (h : wk ≠ bk) :
    kingsBoard wk bk bk = some { color := .black, kind := .king } := by
  simp [kingsBoard, h.symm]

theorem kingsBoard_other (wk bk s : Square) (hw : s ≠ wk) (hb : s ≠ bk) :
    kingsBoard wk bk s = none := by
  simp [kingsBoard, hw, hb]

theorem kingsBoard_eq_white_king {wk bk s : Square} (hne : wk ≠ bk)
    (h : kingsBoard wk bk s = some { color := .white, kind := .king }) :
    s = wk := by
  by_cases hw : s = wk
  · exact hw
  · by_cases hb : s = bk
    · subst hb
      simp [kingsBoard, hw] at h
    · simp [kingsBoard, hw, hb] at h

theorem kingsBoard_eq_black_king {wk bk s : Square} (_hne : wk ≠ bk)
    (h : kingsBoard wk bk s = some { color := .black, kind := .king }) :
    s = bk := by
  by_cases hw : s = wk
  · subst hw
    simp [kingsBoard] at h
  · by_cases hb : s = bk
    · exact hb
    · simp [kingsBoard, hw, hb] at h

theorem attacks_king {b : Board} {s t : Square} {c : Color}
    (h : b s = some { color := c, kind := .king }) :
    b.attacks s t = decide (KingAttacks s t) := by
  unfold attacks
  rw [h]
  simp [PieceKind.isSlider]

theorem kingsBoard_occupiedBy_white (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).occupiedBy .white = {wk} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_singleton]
  by_cases hw : s = wk
  · subst hw
    simp [kingsBoard]
  · by_cases hb : s = bk
    · subst hb
      simp [kingsBoard, hw]
    · simp [kingsBoard, hw, hb]

theorem kingsBoard_occupiedBy_black (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).occupiedBy .black = {bk} := by
  ext s
  simp only [mem_occupiedBy, Finset.mem_singleton]
  by_cases hw : s = wk
  · subst hw
    simp [kingsBoard, h]
  · by_cases hb : s = bk
    · subst hb
      simp [kingsBoard, hw]
    · simp [kingsBoard, hw, hb]

theorem kingsBoard_kingSquares_white (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).kingSquares .white = {wk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  by_cases hw : s = wk
  · subst hw
    simp [kingsBoard]
  · by_cases hb : s = bk
    · subst hb
      simp [kingsBoard, hw]
    · simp [kingsBoard, hw, hb]

theorem kingsBoard_kingSquares_black (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).kingSquares .black = {bk} := by
  ext s
  simp only [mem_kingSquares, Finset.mem_singleton]
  by_cases hw : s = wk
  · subst hw
    simp [kingsBoard, h]
  · by_cases hb : s = bk
    · subst hb
      simp [kingsBoard, hw]
    · simp [kingsBoard, hw, hb]

theorem kingsBoard_occupied (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).occupied = {wk, bk} := by
  rw [occupied_eq_union, kingsBoard_occupiedBy_white wk bk h,
    kingsBoard_occupiedBy_black wk bk h]
  ext s
  simp

/-- Convert a Boolean equality-to-true characterisation of `P` into
`decide P`. -/
theorem bool_eq_decide {a : Bool} {P : Prop} [Decidable P]
    (h : a = true ↔ P) : a = decide P := by
  by_cases hP : P
  · simp [h.mpr hP, hP]
  · rw [decide_eq_false hP, Bool.eq_false_iff]
    exact mt h.mp hP

theorem kingsBoard_kingIsAttacked_white (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).kingIsAttacked .white = decide (KingAttacks bk wk) := by
  refine bool_eq_decide ?_
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBoard_kingSquares_white wk bk h, Finset.mem_singleton,
    exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hs' : s ∈ (kingsBoard wk bk).occupiedBy .black := by
      simpa [mem_occupiedBy] using hcol
    have hsEq : s = bk := by
      simpa [kingsBoard_occupiedBy_black wk bk h] using hs'
    rw [hsEq] at hatt hcol
    rw [attacks_king (kingsBoard_black wk bk h)] at hatt
    exact of_decide_eq_true hatt
  · intro hk
    refine ⟨bk, ?_⟩
    rw [mem_attackers]
    constructor
    · simp [kingsBoard_black wk bk h]
    · rw [attacks_king (kingsBoard_black wk bk h)]
      exact decide_eq_true hk

theorem kingsBoard_kingIsAttacked_black (wk bk : Square) (h : wk ≠ bk) :
    (kingsBoard wk bk).kingIsAttacked .black = decide (KingAttacks wk bk) := by
  refine bool_eq_decide ?_
  rw [kingIsAttacked_iff_mem_attackers]
  simp only [kingsBoard_kingSquares_black wk bk h, Finset.mem_singleton,
    exists_eq_left]
  constructor
  · intro ⟨s, hs⟩
    rw [mem_attackers] at hs
    obtain ⟨hcol, hatt⟩ := hs
    have hs' : s ∈ (kingsBoard wk bk).occupiedBy .white := by
      simpa [mem_occupiedBy] using hcol
    have hsEq : s = wk := by
      simpa [kingsBoard_occupiedBy_white wk bk h] using hs'
    rw [hsEq] at hatt hcol
    rw [attacks_king (kingsBoard_white wk bk)] at hatt
    exact of_decide_eq_true hatt
  · intro hk
    refine ⟨wk, ?_⟩
    rw [mem_attackers]
    constructor
    · simp [kingsBoard_white]
    · rw [attacks_king (kingsBoard_white wk bk)]
      exact decide_eq_true hk

theorem relocate_kingsBoard_white (wk bk dst : Square)
    (hne : wk ≠ bk) (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) :
    (kingsBoard wk bk).relocate wk dst { color := .white, kind := .king } =
      kingsBoard dst bk := by
  funext s
  unfold relocate kingsBoard
  split_ifs <;> simp_all

theorem relocate_kingsBoard_black (wk bk dst : Square)
    (hne : wk ≠ bk) (_hdw : dst ≠ wk) (_hdb : dst ≠ bk) :
    (kingsBoard wk bk).relocate bk dst { color := .black, kind := .king } =
      kingsBoard wk dst := by
  funext s
  unfold relocate kingsBoard
  split_ifs <;> simp_all

end Board

namespace Position

/-- `p` contains only a white king and a black king, not adjacent, with
no remaining castling rights and no en passant target. -/
def IsTwoKings (p : Position) : Prop :=
  ∃ wk bk : Square,
    wk ≠ bk ∧
      ¬ KingAttacks wk bk ∧
      p.board = Board.kingsBoard wk bk ∧
      p.castling = ∅ ∧
      p.enPassant = none

/-- Positions reachable from `start` by a (possibly empty) sequence of
legal moves. -/
inductive Reachable (start : Position) : Position → Prop
  | refl : Reachable start start
  | step {p : Position} (m : Move) :
      Reachable start p → LegalMove p m → Reachable start (p.play m)

theorem Reachable.trans {a b c : Position}
    (hab : Reachable a b) (hbc : Reachable b c) : Reachable a c := by
  induction hbc with
  | refl => exact hab
  | step m h1 hm ih => exact ih.step m hm

/-- Playing a list of moves in order. -/
def playSeq (p : Position) : List Move → Position
  | [] => p
  | m :: ms => playSeq (p.play m) ms

/-- Every move of the list is legal in the position that then obtains. -/
def LegalSeq (p : Position) : List Move → Prop
  | [] => True
  | m :: ms => LegalMove p m ∧ LegalSeq (p.play m) ms

def decidableLegalSeq (p : Position) : (ms : List Move) → Decidable (LegalSeq p ms)
  | [] => isTrue trivial
  | m :: ms =>
    if h : LegalMove p m then
      match decidableLegalSeq (p.play m) ms with
      | .isTrue hms => isTrue ⟨h, hms⟩
      | .isFalse hms => isFalse fun h' => hms h'.2
    else
      isFalse fun h' => h h'.1

instance (p : Position) (ms : List Move) : Decidable (LegalSeq p ms) :=
  decidableLegalSeq p ms

theorem legalSeq_reachable {p : Position} :
    ∀ {ms : List Move}, LegalSeq p ms → Reachable p (playSeq p ms) := by
  intro ms
  induction ms generalizing p with
  | nil => intro _; exact Reachable.refl
  | cons m ms ih =>
    intro ⟨hm, hms⟩
    exact Reachable.trans (Reachable.step m Reachable.refl hm) (ih hms)

/-- Checkmate is reachable from `start` when some position legally
reachable from it (including `start` itself) is checkmate. -/
def CheckmateReachable (p : Position) : Prop :=
  ∃ q, Reachable p q ∧ InCheckmate q

/-- A checkmate position can reach checkmate: the empty sequence. -/
theorem checkmateReachable_of_inCheckmate {p : Position}
    (h : InCheckmate p) : CheckmateReachable p :=
  ⟨p, Reachable.refl, h⟩

/-- A legal sequence ending in checkmate is a witness that checkmate
is reachable. -/
theorem checkmateReachable_of_legalSeq {p : Position} {ms : List Move}
    (hms : LegalSeq p ms) (hm : InCheckmate (playSeq p ms)) :
    CheckmateReachable p :=
  ⟨playSeq p ms, legalSeq_reachable hms, hm⟩

theorem IsTwoKings.not_inCheck {p : Position} (h : IsTwoKings p) :
    p.inCheck = false := by
  obtain ⟨wk, bk, hne, hna, hboard, _, _⟩ := h
  unfold inCheck
  rw [hboard]
  cases p.toMove with
  | white =>
    rw [Board.kingsBoard_kingIsAttacked_white wk bk hne]
    have : ¬ KingAttacks bk wk := mt kingAttacks_symmetric.mpr hna
    simp [this]
  | black =>
    rw [Board.kingsBoard_kingIsAttacked_black wk bk hne]
    simp [hna]

theorem IsTwoKings.not_inCheckmate {p : Position} (h : IsTwoKings p) :
    p.inCheckmate = false :=
  not_inCheck_not_inCheckmate h.not_inCheck

theorem IsTwoKings.not_InCheckmate {p : Position} (h : IsTwoKings p) :
    ¬ InCheckmate p :=
  mt (inCheckmate_eq_true_iff p).mpr
    (Eq.trans_ne h.not_inCheckmate Bool.false_ne_true)

theorem castleMoveOk_of_empty {p : Position} {m : Move}
    (hc : p.castling = ∅) : p.castleMoveOk m = false := by
  unfold castleMoveOk
  cases m.castlingSide? p.toMove with
  | none => rfl
  | some side =>
    simp [hc]

theorem destOk_kingsBoard {p : Position} {m : Move} {wk bk : Square}
    (hboard : p.board = Board.kingsBoard wk bk) (hne : wk ≠ bk)
    (hok : p.destOk m = true) : p.board m.dst = none := by
  unfold destOk at hok
  rw [hboard] at hok ⊢
  by_cases hw : m.dst = wk
  · subst hw
    simp [Board.kingsBoard] at hok
  · by_cases hb : m.dst = bk
    · subst hb
      simp [Board.kingsBoard, hw] at hok
    · simp [Board.kingsBoard, hw, hb]

theorem play_of_some (p : Position) (m : Move) {piece : Piece}
    (h : p.board m.src = some piece) :
    p.play m =
      { board := p.boardAfter m piece
        toMove := p.toMove.other
        castling := castlingAfter p.castling (p.boardAfter m piece)
        enPassant := enPassantAfter m piece (p.boardAfter m piece) } := by
  unfold play
  rw [h]

theorem boardAfter_king_no_castle (p : Position) (m : Move) {c : Color}
    (hside : m.castlingSide? c = none) (hpromo : m.promotion = none) :
    p.boardAfter m { color := c, kind := .king } =
      p.board.relocate m.src m.dst { color := c, kind := .king } := by
  unfold boardAfter
  simp [hside, hpromo]

theorem enPassantAfter_king (m : Move) (c : Color) (b : Board) :
    enPassantAfter m { color := c, kind := .king } b = none := by
  unfold enPassantAfter
  simp

theorem castlingAfter_empty (b : Board) : castlingAfter ∅ b = ∅ := by
  simp [castlingAfter]

theorem eq_none_of_not_mem_occupied {b : Board} {s : Square}
    (h : s ∉ b.occupied) : b s = none := by
  cases hs : b s with
  | none => rfl
  | some _ =>
    have : s ∈ b.occupied := by simp [Board.mem_occupied, hs]
    exact (h this).elim

theorem some_king_ne_rook {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .rook }) : False := by
  simp at h

theorem some_king_ne_pawn {c₁ c₂ : Color}
    (h : (some { color := c₁, kind := .king } : Option Piece) =
      some { color := c₂, kind := .pawn }) : False := by
  simp at h

/-- A valid position with exactly two occupied squares holds only the two
kings, not adjacent. -/
theorem isTwoKings_of_valid {p : Position} (hv : Valid p)
    (hocc : p.board.occupied.card = 2) : IsTwoKings p := by
  obtain ⟨hbv, hopp, hcast, hep⟩ := hv
  obtain ⟨hkings, _, _, _⟩ := hbv
  obtain ⟨wk, hwk⟩ := Finset.card_eq_one.mp (hkings .white)
  obtain ⟨bk, hbk⟩ := Finset.card_eq_one.mp (hkings .black)
  have hne : wk ≠ bk := by
    intro heq
    have hwmem : p.board wk = some { color := .white, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
    have hbmem : p.board bk = some { color := .black, kind := .king } :=
      (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
    rw [heq] at hwmem
    cases hwmem.symm.trans hbmem
  have hWle : 1 ≤ (p.board.occupiedBy .white).card := by
    have hle := Finset.card_le_card (Board.kingSquares_subset_occupiedBy p.board .white)
    simpa [hwk] using hle
  have hBle : 1 ≤ (p.board.occupiedBy .black).card := by
    have hle := Finset.card_le_card (Board.kingSquares_subset_occupiedBy p.board .black)
    simpa [hbk] using hle
  have hsum :
      (p.board.occupiedBy .white).card + (p.board.occupiedBy .black).card = 2 := by
    rw [← Board.occupied_card_eq_sum, hocc]
  have hW1 : (p.board.occupiedBy .white).card = 1 := by omega
  have hB1 : (p.board.occupiedBy .black).card = 1 := by omega
  have hoccW : p.board.occupiedBy .white = {wk} := by
    have hsub := Board.kingSquares_subset_occupiedBy p.board .white
    rw [hwk] at hsub
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hW1])).symm
  have hoccB : p.board.occupiedBy .black = {bk} := by
    have hsub := Board.kingSquares_subset_occupiedBy p.board .black
    rw [hbk] at hsub
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hB1])).symm
  have hboard : p.board = Board.kingsBoard wk bk := by
    funext s
    by_cases hw : s = wk
    · subst hw
      have : p.board s = some { color := .white, kind := .king } :=
        (Board.mem_kingSquares _ _ _).mp (by simp [hwk])
      rw [this, Board.kingsBoard_white]
    · by_cases hb : s = bk
      · subst hb
        have : p.board s = some { color := .black, kind := .king } :=
          (Board.mem_kingSquares _ _ _).mp (by simp [hbk])
        rw [this, Board.kingsBoard_black wk s hne]
      · have hsocc : s ∉ p.board.occupied := by
          rw [Board.occupied_eq_union, hoccW, hoccB]
          simp [hw, hb]
        rw [eq_none_of_not_mem_occupied hsocc, Board.kingsBoard_other wk bk s hw hb]
  have hna : ¬ KingAttacks wk bk := by
    cases ht : p.toMove with
    | white =>
      have hopp' : p.board.kingIsAttacked .black = false := by
        simpa [ht] using hopp
      rw [hboard, Board.kingsBoard_kingIsAttacked_black wk bk hne] at hopp'
      exact of_decide_eq_false hopp'
    | black =>
      have hopp' : p.board.kingIsAttacked .white = false := by
        simpa [ht] using hopp
      rw [hboard, Board.kingsBoard_kingIsAttacked_white wk bk hne] at hopp'
      exact mt kingAttacks_symmetric.mp (of_decide_eq_false hopp')
  have hc : p.castling = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro r hr
    obtain ⟨_, hrook⟩ := hcast r hr
    have hmem : r.rookSquare ∈ p.board.occupied := by
      simp [Board.mem_occupied, hrook]
    rw [hboard, Board.kingsBoard_occupied wk bk hne] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    cases hmem with
    | inl hsq =>
      rw [hsq, hboard, Board.kingsBoard_white] at hrook
      exact some_king_ne_rook hrook
    | inr hsq =>
      rw [hsq, hboard, Board.kingsBoard_black wk bk hne] at hrook
      exact some_king_ne_rook hrook
  have he : p.enPassant = none := by
    cases hep' : p.enPassant with
    | none => rfl
    | some ep =>
      obtain ⟨_, _, hcap⟩ := (enPassantOk_some p ep hep').mp (by simpa [hep'] using hep)
      obtain ⟨s, hs, _⟩ := (existsPawnAttacking_iff _ _ _).mp hcap
      have hpawn := (hasPawn_eq_true_iff _ _ _).mp hs
      have hmem : s ∈ p.board.occupied := by
        simp [Board.mem_occupied, hpawn]
      rw [hboard, Board.kingsBoard_occupied wk bk hne] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      cases hmem with
      | inl hsq =>
        rw [hsq, hboard, Board.kingsBoard_white] at hpawn
        cases some_king_ne_pawn hpawn
      | inr hsq =>
        rw [hsq, hboard, Board.kingsBoard_black wk bk hne] at hpawn
        cases some_king_ne_pawn hpawn
  exact ⟨wk, bk, hne, hna, hboard, hc, he⟩

theorem twoKings_legalMove_spec {p : Position} {m : Move} {wk bk : Square}
    (hboard : p.board = Board.kingsBoard wk bk) (hne : wk ≠ bk)
    (hc : p.castling = ∅) (hm : LegalMove p m) :
    m.promotion = none ∧
      m.castlingSide? p.toMove = none ∧
      p.board m.dst = none ∧
      p.board m.src = some { color := p.toMove, kind := .king } ∧
      KingAttacks m.src m.dst ∧
      (p.play m).board.kingIsAttacked p.toMove = false := by
  have hm' : isLegalMove p m = true := hm
  unfold isLegalMove at hm'
  rw [hboard] at hm'
  cases hsrc : Board.kingsBoard wk bk m.src with
  | none => simp [hsrc] at hm'
  | some piece =>
    simp only [hsrc, Bool.and_eq_true] at hm'
    obtain ⟨⟨hcolDest, hifs⟩, hsafeB⟩ := hm'
    have hcol' : piece.color = p.toMove := beq_iff_eq.mp hcolDest.1
    have hdestOk : p.destOk m = true := hcolDest.2
    have hking : piece.kind = .king := by
      unfold Board.kingsBoard at hsrc
      split_ifs at hsrc <;> cases hsrc <;> rfl
    have hpiece : piece = { color := p.toMove, kind := .king } := by
      cases piece
      simp_all
    have hsrcP : p.board m.src = some { color := p.toMove, kind := .king } := by
      rw [hboard, hsrc, hpiece]
    have hdstNone : p.board m.dst = none :=
      destOk_kingsBoard hboard hne hdestOk
    have hside : m.castlingSide? p.toMove = none := by
      cases hopt : m.castlingSide? p.toMove with
      | none => rfl
      | some _ =>
        have hs : (m.castlingSide? p.toMove).isSome = true := by simp [hopt]
        rw [hpiece] at hifs
        simp [hs, castleMoveOk_of_empty hc] at hifs
    have hgeo : (Board.kingsBoard wk bk).attacks m.src m.dst = true ∧
        m.promotion = none := by
      rw [hpiece] at hifs
      simpa [hside, Bool.and_eq_true, beq_iff_eq] using hifs
    have hatt : KingAttacks m.src m.dst := by
      have : (Board.kingsBoard wk bk).attacks m.src m.dst = true := hgeo.1
      have hsk : Board.kingsBoard wk bk m.src =
          some { color := p.toMove, kind := .king } := by
        simpa [hboard] using hsrcP
      rw [Board.attacks_king hsk] at this
      exact of_decide_eq_true this
    have hsafe : (p.play m).board.kingIsAttacked p.toMove = false := by
      simpa [Bool.not_eq_true'] using hsafeB
    exact ⟨hgeo.2, hside, hdstNone, hsrcP, hatt, hsafe⟩

theorem IsTwoKings.of_play {p : Position} {m : Move}
    (h : IsTwoKings p) (hm : LegalMove p m) : IsTwoKings (p.play m) := by
  obtain ⟨wk, bk, hne, _hna, hboard, hc, _he⟩ := h
  obtain ⟨hpromo, hside, hdstNone, hsrcP, _hatt, hsafe⟩ :=
    twoKings_legalMove_spec hboard hne hc hm
  have hdstW : m.dst ≠ wk := by
    intro heq
    rw [heq, hboard, Board.kingsBoard_white] at hdstNone
    cases hdstNone
  have hdstB : m.dst ≠ bk := by
    intro heq
    rw [heq, hboard, Board.kingsBoard_black wk bk hne] at hdstNone
    cases hdstNone
  have hplay := play_of_some p m hsrcP
  have hba := boardAfter_king_no_castle p m hside hpromo
  have hcast' : (p.play m).castling = ∅ := by
    calc (p.play m).castling
        = castlingAfter p.castling
            (p.boardAfter m { color := p.toMove, kind := .king }) := by
          rw [hplay]
      _ = castlingAfter ∅
            (p.boardAfter m { color := p.toMove, kind := .king }) := by
          rw [hc]
      _ = ∅ := castlingAfter_empty _
  have hep' : (p.play m).enPassant = none := by
    calc (p.play m).enPassant
        = enPassantAfter m { color := p.toMove, kind := .king }
            (p.boardAfter m { color := p.toMove, kind := .king }) := by
          rw [hplay]
      _ = none := enPassantAfter_king _ _ _
  cases ht : p.toMove with
  | white =>
    have hsrcW : m.src = wk :=
      Board.kingsBoard_eq_white_king hne (by simpa [hboard, ht] using hsrcP)
    have hboard' : (p.play m).board = Board.kingsBoard m.dst bk := by
      calc (p.play m).board
          = p.boardAfter m { color := p.toMove, kind := .king } := by
            rw [hplay]
        _ = p.board.relocate m.src m.dst
              { color := p.toMove, kind := .king } := hba
        _ = (Board.kingsBoard wk bk).relocate wk m.dst
              { color := .white, kind := .king } := by
            rw [hboard, hsrcW, ht]
        _ = Board.kingsBoard m.dst bk :=
            Board.relocate_kingsBoard_white wk bk m.dst hne hdstW hdstB
    have hna' : ¬ KingAttacks m.dst bk := by
      have hsafe' : (p.play m).board.kingIsAttacked .white = false := by
        simpa [ht] using hsafe
      rw [hboard', Board.kingsBoard_kingIsAttacked_white m.dst bk hdstB] at hsafe'
      exact mt kingAttacks_symmetric.mpr (of_decide_eq_false hsafe')
    exact ⟨m.dst, bk, hdstB, hna', hboard', hcast', hep'⟩
  | black =>
    have hsrcB : m.src = bk :=
      Board.kingsBoard_eq_black_king hne (by simpa [hboard, ht] using hsrcP)
    have hboard' : (p.play m).board = Board.kingsBoard wk m.dst := by
      calc (p.play m).board
          = p.boardAfter m { color := p.toMove, kind := .king } := by
            rw [hplay]
        _ = p.board.relocate m.src m.dst
              { color := p.toMove, kind := .king } := hba
        _ = (Board.kingsBoard wk bk).relocate bk m.dst
              { color := .black, kind := .king } := by
            rw [hboard, hsrcB, ht]
        _ = Board.kingsBoard wk m.dst :=
            Board.relocate_kingsBoard_black wk bk m.dst hne hdstW hdstB
    have hna' : ¬ KingAttacks wk m.dst := by
      have hsafe' : (p.play m).board.kingIsAttacked .black = false := by
        simpa [ht] using hsafe
      rw [hboard', Board.kingsBoard_kingIsAttacked_black wk m.dst hdstW.symm] at hsafe'
      exact of_decide_eq_false hsafe'
    exact ⟨wk, m.dst, hdstW.symm, hna', hboard', hcast', hep'⟩

theorem IsTwoKings.of_reachable {p q : Position}
    (h : IsTwoKings p) (hr : Reachable p q) : IsTwoKings q := by
  induction hr with
  | refl => exact h
  | step m _hm hleg ih => exact ih.of_play hleg

/-- A valid two-king position is never checkmate. -/
theorem twoKings_not_inCheckmate {p : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 2) :
    p.inCheckmate = false :=
  (isTwoKings_of_valid hv hocc).not_inCheckmate

/-- From a valid position with only two kings, every legally reachable
position is still not checkmate. -/
theorem twoKings_reachable_not_inCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 2)
    (hr : Reachable p q) : q.inCheckmate = false :=
  (IsTwoKings.of_reachable (isTwoKings_of_valid hv hocc) hr).not_inCheckmate

/-- From a valid position with only two kings, no sequence of legal
moves produces checkmate. -/
theorem twoKings_legalSeq_not_inCheckmate {p : Position} {ms : List Move}
    (hv : Valid p) (hocc : p.board.occupied.card = 2)
    (hms : LegalSeq p ms) :
    (playSeq p ms).inCheckmate = false :=
  twoKings_reachable_not_inCheckmate hv hocc (legalSeq_reachable hms)

theorem twoKings_reachable_not_InCheckmate {p q : Position}
    (hv : Valid p) (hocc : p.board.occupied.card = 2)
    (hr : Reachable p q) : ¬ InCheckmate q :=
  (IsTwoKings.of_reachable (isTwoKings_of_valid hv hocc) hr).not_InCheckmate

/-! ### Example: kings on `e1` and `e8` -/

/-- White king on `e1`, black king on `e8`, White to move. -/
def kingsOnly : Position where
  board := fun s =>
    if s = Square.e1 then some { color := .white, kind := .king }
    else if s = Square.e8 then some { color := .black, kind := .king }
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingsOnly_isValid : isValid kingsOnly = true := by
  native_decide

theorem kingsOnly_occupied_card : kingsOnly.board.occupied.card = 2 := by
  native_decide

theorem kingsOnly_not_inCheckmate : kingsOnly.inCheckmate = false :=
  twoKings_not_inCheckmate
    ((isValid_eq_true_iff kingsOnly).mp kingsOnly_isValid)
    kingsOnly_occupied_card

/-- White's `e1–e2` is legal with only the two kings. -/
theorem kingsOnly_e1e2_legal :
    isLegalMove kingsOnly (Move.std Square.e1 Square.e2) = true := by
  native_decide

/-- After `e1–e2`, the position is still not checkmate. -/
theorem kingsOnly_play_e1e2_not_inCheckmate :
    (kingsOnly.play (Move.std Square.e1 Square.e2)).inCheckmate = false := by
  native_decide

end Position

end Chess
