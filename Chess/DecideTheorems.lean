import Chess.Decide

/-!
# Soundness of the general `CheckmateReachable` search

`Position.checkmateVerdict` is correct for every valid position
(`checkmateVerdict_iff`): a `true` answer is a checked mating line or an
exhaustive exploration that found checkmate, and a `false` answer is a
closed-off reachable graph that never meets checkmate. Together these
give `Position.checkmateReachableDecidable`.
-/

namespace Chess

namespace Position

/-! ## King uniqueness and non-adjacency (no material restriction) -/

/-- Neither player has two kings, and the kings are not adjacent. -/
structure KingShape (p : Position) : Prop where
  /-- No player has two kings. -/
  oneKing : ∀ d s t, p.board s = some { color := d, kind := .king } →
    p.board t = some { color := d, kind := .king } → s = t
  /-- The kings are not adjacent. -/
  noAdj : ∀ c s t, p.board s = some { color := c, kind := .king } →
    p.board t = some { color := c.other, kind := .king } → ¬ KingAttacks s t

/-- Every valid position has the shape. -/
theorem KingShape.of_valid {p : Position} (hv : Valid p) : KingShape p := by
  obtain ⟨⟨hkings, _, _, _⟩, hopp, _, _⟩ := hv
  refine ⟨?_, ?_⟩
  · intro d s t hs ht
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hkings d)
    have hs' : s ∈ p.board.kingSquares d := (Board.mem_kingSquares _ _ _).mpr hs
    have ht' : t ∈ p.board.kingSquares d := (Board.mem_kingSquares _ _ _).mpr ht
    rw [ha, Finset.mem_singleton] at hs' ht'
    exact hs'.trans ht'.symm
  · intro c s t hs ht hatt
    rcases Color.eq_or_eq_other p.toMove c with htm | htm
    · rw [htm] at hopp
      have := Board.kingIsAttacked_of_attacks ht (by rw [Color.other_other]; exact hs)
        (by rw [Board.attacks_king hs]; exact decide_eq_true hatt)
      exact Bool.false_ne_true (hopp.symm.trans this)
    · rw [htm, Color.other_other] at hopp
      have := Board.kingIsAttacked_of_attacks hs ht
        (by rw [Board.attacks_king ht]; exact decide_eq_true (kingAttacks_symmetric.mp hatt))
      exact Bool.false_ne_true (hopp.symm.trans this)

/-- The shape is preserved by every legal move. -/
theorem KingShape.of_play {p : Position} {m : Move} (h : KingShape p) (hm : LegalMove p m) :
    KingShape (p.play m) := by
  obtain ⟨piece, hsrc, _, _, _, _⟩ := legalMove_spec hm
  refine ⟨?_, ?_⟩
  · intro d s t hs ht
    rcases play_board_king hm hsrc hs with ⟨hsd, hps⟩ | ⟨hss, _, hs'⟩ <;>
      rcases play_board_king hm hsrc ht with ⟨htd, hpt⟩ | ⟨hts, _, ht'⟩
    · exact hsd.trans htd.symm
    · exact absurd (h.oneKing d _ _ (hps ▸ hsrc) ht') (Ne.symm hts)
    · exact absurd (h.oneKing d _ _ (hpt ▸ hsrc) hs') (Ne.symm hss)
    · exact h.oneKing d _ _ hs' ht'
  · intro c s t hs ht hatt
    have hsafe := legalMove_safe hm
    rcases Color.eq_or_eq_other p.toMove c with htm | htm
    · rw [htm] at hsafe
      have := Board.kingIsAttacked_of_attacks hs ht
        (by rw [Board.attacks_king ht]; exact decide_eq_true (kingAttacks_symmetric.mp hatt))
      exact Bool.false_ne_true (hsafe.symm.trans this)
    · rw [htm] at hsafe
      have := Board.kingIsAttacked_of_attacks ht (by rw [Color.other_other]; exact hs)
        (by rw [Board.attacks_king hs]; exact decide_eq_true hatt)
      exact Bool.false_ne_true (hsafe.symm.trans this)

theorem KingShape.of_reachable {p q : Position} (h : KingShape p) (hr : Reachable p q) :
    KingShape q := by
  induction hr with
  | refl => exact h
  | step m _ hleg ih => exact ih.of_play hleg

/-! ## Same-color bishops (both sides) is dead -/

/-- The property is preserved by every legal move: a bishop keeps the color
of its square, nothing is promoted, and no rook castles. -/
theorem BishopsOnly.of_play {χ : Color} {p : Position} {m : Move}
    (h : BishopsOnly χ p) (hm : LegalMove p m) : BishopsOnly χ (p.play m) := by
  obtain ⟨piece, hsrc, _, _, _, _⟩ := legalMove_spec hm
  intro x q hx hnk
  rcases play_board_some hsrc hx with ⟨hxd, hq'⟩ | ⟨hk, side, hside, _, hq'⟩ | ⟨_, _, hx'⟩
  · have hpk : piece.kind ≠ .pawn := by
      intro hp
      have := (h _ _ hsrc (fun hk => by rw [hk] at hp; cases hp)).1
      rw [hp] at this
      cases this
    rw [placed_of_promotion_none (legalMove_promotion_none hm hsrc hpk)] at hq'
    subst hq'
    obtain ⟨hb, hsχ⟩ := h _ _ hsrc hnk
    refine ⟨hb, ?_⟩
    have hatt := legalMove_attacks hm hsrc hpk (by rw [hb]; decide)
    rw [Piece.eq_mk rfl hb] at hsrc
    have hgeo := Board.bishopAttacks_of_attacks hsrc hatt
    rw [hxd, ← bishopAttacks_same_color hgeo]
    exact hsχ
  · have := (h _ _ (legalMove_castling_rook hm hsrc hk hside) (by simp)).1
    cases this
  · exact h _ _ hx' hnk

theorem BishopsOnly.of_reachable {χ : Color} {p q : Position} (h : BishopsOnly χ p)
    (hr : Reachable p q) : BishopsOnly χ q := by
  induction hr with
  | refl => exact h
  | step m _ hleg ih => exact ih.of_play hleg

/-- A piece attacking a square is a king, adjacent to the square, or a
bishop, in which case the square has color `χ`. -/
theorem BishopsOnly.attacker {χ : Color} {p : Position} {b : Board} {s t : Square}
    {q : Piece} (hb : BishopsOnly χ p) (hs : p.board s = some q) (hs' : b s = some q)
    (hatt : b.attacks s t = true) :
    (q.kind = .king ∧ KingAttacks s t) ∨ t.color = χ := by
  by_cases hk : q.kind = .king
  · rw [show q = { color := q.color, kind := .king } from Piece.eq_mk rfl hk] at hs'
    rw [Board.attacks_king hs'] at hatt
    exact Or.inl ⟨hk, of_decide_eq_true hatt⟩
  · obtain ⟨hbish, hsχ⟩ := hb _ _ hs hk
    rw [Piece.eq_mk rfl hbish] at hs'
    exact Or.inr ((bishopAttacks_same_color (Board.bishopAttacks_of_attacks hs' hatt)).symm.trans
      hsχ)

/-- The king on `k`, a square of the bishops' color, may step to an
orthogonal neighbor `e` that the other king does not attack. -/
theorem KingShape.escape_legal {χ : Color} {p : Position} (hs : KingShape p)
    (hb : BishopsOnly χ p) {k e : Square}
    (hk : p.board k = some { color := p.toMove, kind := .king })
    (hkχ : k.color = χ) (ho : OrthogonalAdjacent k e)
    (hne : ∀ w, p.board w = some { color := p.toMove.other, kind := .king } → ¬ KingAttacks w e) :
    LegalMove p (Move.std k e) := by
  have heχ : e.color = χ.other := by rw [orthoAdj_color ho, hkχ]
  have hke : k ≠ e := orthoAdj_ne ho
  have hempty : p.board e = none := by
    cases hq : p.board e with
    | none => rfl
    | some q =>
      exfalso
      rcases Color.eq_or_eq_other q.color p.toMove with hqc | hqc
      · by_cases hqk : q.kind = .king
        · exact hke (hs.oneKing p.toMove _ _ hk (by rw [hq, Piece.eq_mk hqc hqk]))
        · exact Color.other_ne χ ((hb _ _ hq hqk).2.symm.trans heχ).symm
      · by_cases hqk : q.kind = .king
        · exact hs.noAdj p.toMove k e hk (by rw [hq, Piece.eq_mk hqc hqk])
            (orthoAdj_kingAttacks ho)
        · exact Color.other_ne χ ((hb _ _ hq hqk).2.symm.trans heχ).symm
  have hside : (Move.std k e).castlingSide? p.toMove = none :=
    castlingSide_none_of_ortho p.toMove ho
  have hboard :
      (p.play (Move.std k e)).board =
        p.board.relocate k e { color := p.toMove, kind := .king } := by
    rw [play_of_some p _ hk]
    exact boardAfter_king_no_castle p _ hside rfl
  have hsafe : (p.play (Move.std k e)).board.kingIsAttacked p.toMove = false := by
    rw [hboard]
    cases hatt : (p.board.relocate k e { color := p.toMove, kind := .king }).kingIsAttacked
        p.toMove with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨t, s, q, ht, hsq, hqc, hatt'⟩ := Board.exists_of_kingIsAttacked hatt
      have hte : t = e := by
        by_contra hte
        have htk : t ≠ k := by
          intro htk
          subst htk
          simp [Board.relocate, hte] at ht
        have ht' : p.board t = some { color := p.toMove, kind := .king } := by
          simpa [Board.relocate, hte, htk] using ht
        exact htk (hs.oneKing p.toMove _ _ ht' hk)
      subst hte
      have hse : s ≠ t := by
        intro hst
        subst hst
        simp only [Board.relocate, if_true, Option.some.injEq] at hsq
        rw [← hsq] at hqc
        exact Color.other_ne p.toMove hqc.symm
      have hsk : s ≠ k := by
        intro hsk
        subst hsk
        simp only [Board.relocate, hse, if_false, if_true] at hsq
        cases hsq
      have hsq' : p.board s = some q := by
        simpa [Board.relocate, hse, hsk] using hsq
      rcases hb.attacker hsq' hsq hatt' with ⟨hqk, hatt''⟩ | htχ
      · rw [show q = { color := q.color, kind := .king } from Piece.eq_mk rfl hqk] at hsq' hqc
        have hqco : q.color = p.toMove.other := hqc
        rw [hqco] at hsq'
        exact hne s hsq' hatt''
      · exact Color.other_ne χ (heχ.symm.trans htχ)
  have hdest : p.destOk (Move.std k e) = true := by
    unfold destOk
    have : p.board (Move.std k e).dst = none := hempty
    rw [this]
  have hgeo : p.board.attacks k e = true := by
    rw [Board.attacks_king hk]
    exact decide_eq_true (orthoAdj_kingAttacks ho)
  unfold LegalMove isLegalMove
  simp only [Move.std] at hdest hside hsafe ⊢
  rw [hk]
  simp [hdest, hside, hgeo, hsafe]

/-- The player to move is never checkmated: a king checked by a bishop
always has an orthogonal neighbor that no bishop can attack. -/
theorem KingShape.not_InCheckmate_of_bishopsOnly {χ : Color} {p : Position}
    (hs : KingShape p) (hb : BishopsOnly χ p) : ¬ InCheckmate p := by
  cases hchk : p.inCheck with
  | false =>
    intro hm
    exact Bool.false_ne_true ((not_inCheck_not_inCheckmate hchk).symm.trans
      ((inCheckmate_eq_true_iff p).mpr hm))
  | true =>
    unfold inCheck at hchk
    obtain ⟨k, s, q, hk, hsq, hqc, hatt⟩ := Board.exists_of_kingIsAttacked hchk
    have hkχ : k.color = χ := by
      rcases hb.attacker hsq hsq hatt with ⟨hqk, hatt'⟩ | hkχ
      · rw [show q = { color := q.color, kind := .king } from Piece.eq_mk rfl hqk] at hsq hqc
        rw [hqc] at hsq
        exact (hs.noAdj p.toMove k s hk hsq (kingAttacks_symmetric.mp hatt')).elim
      · exact hkχ
    have hleg : ∃ e, LegalMove p (Move.std k e) := by
      by_cases hw : ∃ w, p.board w = some { color := p.toMove.other, kind := .king }
      · obtain ⟨w, hw⟩ := hw
        refine ⟨kingOrthoEscape k w, hs.escape_legal hb hk hkχ (kingOrthoEscape_ortho k w)
          fun w' hw' => ?_⟩
        rw [hs.oneKing _ _ _ hw' hw]
        refine kingOrthoEscape_not_kingAttacks k w ?_ fun hatt' =>
          hs.noAdj p.toMove k w hk hw (kingAttacks_symmetric.mp hatt')
        intro hwk
        rw [hwk, hk, Option.some.injEq] at hw
        exact Color.other_ne p.toMove (congrArg Piece.color hw).symm
      · exact ⟨horizNeighbor k, hs.escape_legal hb hk hkχ (horizNeighbor_ortho k)
          fun w' hw' => (hw ⟨w', hw'⟩).elim⟩
    obtain ⟨e, hleg⟩ := hleg
    intro hm
    exact ((InCheckmate_iff_forall_not_LegalMove p).mp hm).2 _ hleg

/-- Kings and bishops all standing on squares of one color cannot reach
checkmate. -/
theorem KingShape.deadPosition_of_bishopsOnly {χ : Color} {p : Position}
    (hs : KingShape p) (hb : BishopsOnly χ p) : DeadPosition p := by
  intro q hr
  exact (hs.of_reachable hr).not_InCheckmate_of_bishopsOnly (hb.of_reachable hr)

theorem bishopsOnlySameB_sound {p : Position} (hs : KingShape p)
    (h : bishopsOnlySameB p = true) : DeadPosition p := by
  unfold bishopsOnlySameB at h
  rw [decide_eq_true_eq] at h
  obtain ⟨χ, hB⟩ := h
  exact hs.deadPosition_of_bishopsOnly hB

end Position

namespace Decide

open Position
open Position.LoneKing (mem_successors mem_fresh inCheckmate_of_mateTest
  not_inCheckmate_of_mateTest checkmateReachable_of_play deadLeaf_sound)

/-! ## Checked mating lines -/

theorem checkLine_sound {p : Position} {ms : List Move} (h : checkLine p ms = true) :
    CheckmateReachable p := by
  unfold checkLine at h
  simp only [pathLegalN_eq, playSeqN_eq, Bool.and_eq_true] at h
  exact checkmateReachable_of_legalSeq ((pathLegal_iff _ _).mp h.1)
    ((inCheckmate_eq_true_iff _).mp h.2)

theorem checkedLine_sound {p : Position} {o : Option (List Move)} {ms : List Move}
    (h : checkedLine p o = some ms) : CheckmateReachable p := by
  unfold checkedLine at h
  split at h
  · split at h
    · rename_i hcl
      cases h
      exact checkLine_sound hcl
    · cases h
  · cases h

theorem knownLive_sound {q : Position} (h : knownLive q = true) : CheckmateReachable q := by
  unfold knownLive at h
  split at h
  · exact checkLine_sound h
  · cases h

theorem orElse_eq_some {α} {o₁ : Option α} {o₂ : Unit → Option α} {a : α} :
    o₁.orElse o₂ = some a ↔ o₁ = some a ∨ (o₁ = none ∧ o₂ () = some a) := by
  cases o₁ <;> simp [Option.orElse]

theorem matingLine?_sound {p : Position} {ms : List Move}
    (h : matingLine? p = some ms) : CheckmateReachable p := by
  unfold matingLine? at h
  simp only [normalize_eq] at h
  split at h
  · cases h
  · rw [orElse_eq_some] at h
    rcases h with h | ⟨_, h⟩
    · exact checkedLine_sound h
    · rw [orElse_eq_some] at h
      rcases h with h | ⟨_, h⟩
      · exact checkedLine_sound h
      · rw [orElse_eq_some] at h
        rcases h with h | ⟨_, h⟩
        · exact checkedLine_sound h
        · rw [orElse_eq_some] at h
          rcases h with h | ⟨_, h⟩
          · exact checkedLine_sound h
          · exact checkedLine_sound h

theorem probe_sound {p : Position} (h : probe p = true) : CheckmateReachable p := by
  unfold probe at h
  cases hms : matingLine? p with
  | none =>
    rw [hms] at h
    exact (Bool.false_ne_true h).elim
  | some _ => exact matingLine?_sound hms

/-! ## Dead nodes -/

theorem deadNode_sound {q : Position} (hs : KingShape q) (h : deadNode q = true) :
    DeadPosition q := by
  unfold deadNode at h
  simp only [Bool.or_eq_true] at h
  rcases h with hleaf | hmat
  · exact deadLeaf_sound hleaf
  · exact bishopsOnlySameB_sound hs hmat

/-! ## Exhaustive exploration -/

/-- `true` is answered only when checkmate is reachable from a position of
the work list. -/
theorem explore_true :
    ∀ V W, explore V W = true → ∃ q ∈ W, CheckmateReachable q := by
  intro V W
  induction V, W using explore.induct with
  | case1 V => intro h; rw [explore] at h; cases h
  | case2 V q W hlive => exact fun _ => ⟨q, List.mem_cons_self, knownLive_sound hlive⟩
  | case3 V q W hlive hdead ih =>
    intro h
    rw [explore, if_neg hlive, if_pos hdead] at h
    obtain ⟨r, hr, hcr⟩ := ih h
    exact ⟨r, List.mem_cons_of_mem q hr, hcr⟩
  | case4 V q W hlive hdead _ hmate =>
    exact fun _ => ⟨q, List.mem_cons_self, checkmateReachable_of_inCheckmate
      (inCheckmate_of_mateTest hmate)⟩
  | case5 V q W hlive hdead _ hmate ih =>
    intro h
    rw [explore, if_neg hlive, if_neg hdead, if_neg hmate] at h
    obtain ⟨r, hr, hcr⟩ := ih h
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_cons_of_mem q hr, hcr⟩
    · obtain ⟨m, hleg, rfl⟩ := mem_successors.mp (mem_fresh.mp hr).1
      exact ⟨q, List.mem_cons_self, checkmateReachable_of_play hleg hcr⟩

/-- A position of the seen list is closed off: recognized as dead, or not
checkmate with every legal move leading into the seen list. -/
def Closed (V : List Position) (q : Position) : Prop :=
  deadNode q = true ∨ (¬ InCheckmate q ∧ ∀ m, LegalMove q m → q.play m ∈ V)

theorem Closed.mono {V V' : List Position} {q : Position} (h : Closed V q)
    (hVV : ∀ r ∈ V, r ∈ V') : Closed V' q := by
  rcases h with h | ⟨hnm, hsucc⟩
  · exact Or.inl h
  · exact Or.inr ⟨hnm, fun m hm => hVV _ (hsucc m hm)⟩

/-- `false` is answered only once every seen position is closed off. -/
theorem explore_false (p : Position) :
    ∀ V W, explore V W = false → (∀ q ∈ W, q ∈ V) → (∀ q ∈ V, Reachable p q) →
      (∀ q ∈ V, q ∉ W → Closed V q) →
      ∃ V', (∀ q ∈ V, q ∈ V') ∧ (∀ q ∈ V', Reachable p q) ∧ ∀ q ∈ V', Closed V' q := by
  intro V W
  induction V, W using explore.induct with
  | case1 V =>
    intro _ _ hreach hclosed
    exact ⟨V, fun q hq => hq, hreach, fun q hq => hclosed q hq (List.not_mem_nil)⟩
  | case2 V q W hlive =>
    intro h
    rw [explore, if_pos hlive] at h
    cases h
  | case3 V q W hlive hdead ih =>
    intro h hWV hreach hclosed
    rw [explore, if_neg hlive, if_pos hdead] at h
    refine ih h (fun r hr => hWV r (List.mem_cons_of_mem q hr)) hreach fun r hr hrW => ?_
    by_cases hrq : r = q
    · exact Or.inl (hrq ▸ hdead)
    · exact hclosed r hr fun hmem => (List.mem_cons.mp hmem).elim hrq hrW
  | case4 V q W hlive hdead _ hmate =>
    intro h
    rw [explore, if_neg hlive, if_neg hdead, if_pos hmate] at h
    cases h
  | case5 V q W hlive hdead _ hmate ih =>
    intro h hWV hreach hclosed
    rw [explore, if_neg hlive, if_neg hdead, if_neg hmate] at h
    have hqV : q ∈ V := hWV q List.mem_cons_self
    have hWV' : ∀ r ∈ W ++ LoneKing.fresh V (LoneKing.successors q),
        r ∈ V ++ LoneKing.fresh V (LoneKing.successors q) := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ (hWV r (List.mem_cons_of_mem q hr))
      · exact List.mem_append_right _ hr
    have hreach' : ∀ r ∈ V ++ LoneKing.fresh V (LoneKing.successors q), Reachable p r := by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hreach r hr
      · obtain ⟨m, hleg, rfl⟩ := mem_successors.mp (mem_fresh.mp hr).1
        exact Reachable.step m (hreach q hqV) hleg
    have hclosed' : ∀ r ∈ V ++ LoneKing.fresh V (LoneKing.successors q),
        r ∉ W ++ LoneKing.fresh V (LoneKing.successors q) →
        Closed (V ++ LoneKing.fresh V (LoneKing.successors q)) r := by
      intro r hr hrW
      have hrV : r ∈ V := by
        rcases List.mem_append.mp hr with hr | hr
        · exact hr
        · exact (hrW (List.mem_append_right _ hr)).elim
      have hrW' : r ∉ W := fun h' => hrW (List.mem_append_left _ h')
      by_cases hrq : r = q
      · subst hrq
        refine Or.inr ⟨not_inCheckmate_of_mateTest (Bool.eq_false_iff.mpr hmate), fun m hm => ?_⟩
        have hsucc : r.play m ∈ LoneKing.successors r := mem_successors.mpr ⟨m, hm, rfl⟩
        by_cases hmem : r.play m ∈ V
        · exact List.mem_append_left _ hmem
        · exact List.mem_append_right _ (mem_fresh.mpr ⟨hsucc, hmem⟩)
      · exact (hclosed r hrV fun hmem => (List.mem_cons.mp hmem).elim hrq hrW').mono
          fun x hx => List.mem_append_left _ hx
    obtain ⟨V', hVV', hreach'', hclosed''⟩ := ih h hWV' hreach' hclosed'
    exact ⟨V', fun r hr => hVV' r (List.mem_append_left _ hr), hreach'', hclosed''⟩

/-- A start position of a closed-off list all of whose recognized-dead
members are dead is dead. -/
theorem deadPosition_of_closed {p : Position} {V' : List Position} (hp : p ∈ V')
    (hclosed : ∀ q ∈ V', Closed V' q)
    (hdead : ∀ q ∈ V', deadNode q = true → DeadPosition q) : DeadPosition p := by
  have key : ∀ q, Reachable p q → q ∈ V' ∨ ∃ d ∈ V', deadNode d = true ∧ Reachable d q := by
    intro q hq
    induction hq with
    | refl => exact Or.inl hp
    | step m _ hleg ih =>
      rcases ih with hmem | ⟨d, hd, hdn, hrd⟩
      · rcases hclosed _ hmem with hdn | ⟨_, hsucc⟩
        · exact Or.inr ⟨_, hmem, hdn, Reachable.step m Reachable.refl hleg⟩
        · exact Or.inl (hsucc m hleg)
      · exact Or.inr ⟨d, hd, hdn, Reachable.step m hrd hleg⟩
  intro q hq hm
  rcases key q hq with hmem | ⟨d, hd, hdn, hrd⟩
  · rcases hclosed _ hmem with hdn | ⟨hnm, _⟩
    · exact hdead _ hmem hdn _ Reachable.refl hm
    · exact hnm hm
  · exact hdead d hd hdn q hrd hm

end Decide

namespace Position

/-- The verdict is correct for every valid position. -/
theorem checkmateVerdict_iff {p : Position} (hv : Valid p) :
    checkmateVerdict p = true ↔ CheckmateReachable p := by
  unfold checkmateVerdict
  split_ifs with hlone hdead hprobe
  · exact loneKingVerdict_iff hv hlone
  · constructor
    · intro h
      exact h.elim
    · intro hcr
      exact ((DeadPosition_iff_not_CheckmateReachable p).mp
        (Decide.deadNode_sound (KingShape.of_valid hv) hdead) hcr).elim
  · exact ⟨fun _ => Decide.probe_sound hprobe, fun _ => rfl⟩
  · simp only [normalize_eq]
    constructor
    · intro he
      obtain ⟨q, hq, hcr⟩ := Decide.explore_true _ _ he
      rw [List.mem_singleton] at hq
      exact hq ▸ hcr
    · intro hcr
      by_contra he
      rw [Bool.not_eq_true] at he
      obtain ⟨V', hV, hreach, hclosed⟩ :=
        Decide.explore_false p _ _ he (fun q hq => hq)
          (fun q hq => by rw [List.mem_singleton] at hq; exact hq ▸ Reachable.refl)
          (fun q hq hnq => (hnq hq).elim)
      have hs : KingShape p := KingShape.of_valid hv
      exact (DeadPosition_iff_not_CheckmateReachable p).mp
        (Decide.deadPosition_of_closed (hV p (List.mem_singleton_self p)) hclosed
          fun q hq hdn => Decide.deadNode_sound (hs.of_reachable (hreach q hq)) hdn) hcr

/-- Decides whether checkmate is reachable from a valid position, by
evaluating `checkmateVerdict`. -/
def checkmateReachableDecidable (p : Position) (hv : Valid p) :
    Decidable (CheckmateReachable p) :=
  decidable_of_iff (checkmateVerdict p = true) (checkmateVerdict_iff hv)

/-! ### Examples -/

/-- White king `e1`, black king `e8`, white bishop `c1`, black knight `b8`. -/
def kingBishopVsKnight : Position where
  board := fun s =>
    if s = Square.e1 then some ⟨.white, .king⟩
    else if s = Square.e8 then some ⟨.black, .king⟩
    else if s = Square.c1 then some ⟨.white, .bishop⟩
    else if s = Square.b8 then some ⟨.black, .knight⟩
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem kingBishopVsKnight_isValid : isValid kingBishopVsKnight = true := by
  native_decide

theorem kingBishopVsKnight_valid : Valid kingBishopVsKnight :=
  (isValid_eq_true_iff _).mp kingBishopVsKnight_isValid

/-- Three same-color bishops (two white, one black) cannot mate. -/
def sameColorBishops3 : Position where
  board := fun s =>
    if s = Square.e1 then some ⟨.white, .king⟩
    else if s = Square.e8 then some ⟨.black, .king⟩
    else if s = Square.c1 then some ⟨.white, .bishop⟩
    else if s = Square.e3 then some ⟨.white, .bishop⟩
    else if s = Square.a7 then some ⟨.black, .bishop⟩
    else none
  toMove := .white
  castling := CastlingRights.empty
  enPassant := none

theorem sameColorBishops3_isValid : isValid sameColorBishops3 = true := by
  native_decide

theorem sameColorBishops3_valid : Valid sameColorBishops3 :=
  (isValid_eq_true_iff _).mp sameColorBishops3_isValid

theorem starting_checkmateVerdict : checkmateVerdict starting = true := by
  native_decide

theorem starting_CheckmateReachable' : CheckmateReachable starting :=
  (checkmateVerdict_iff starting_valid).mp starting_checkmateVerdict

theorem kingsOnly_checkmateVerdict : checkmateVerdict kingsOnly = false := by
  native_decide

theorem kingsOnly_not_CheckmateReachable' : ¬ CheckmateReachable kingsOnly := by
  intro hcr
  have := (checkmateVerdict_iff ((isValid_eq_true_iff _).mp kingsOnly_isValid)).mpr hcr
  rw [kingsOnly_checkmateVerdict] at this
  exact Bool.false_ne_true this

theorem sameColorBishops3_checkmateVerdict : checkmateVerdict sameColorBishops3 = false := by
  native_decide

theorem sameColorBishops3_not_CheckmateReachable : ¬ CheckmateReachable sameColorBishops3 := by
  intro hcr
  have := (checkmateVerdict_iff sameColorBishops3_valid).mpr hcr
  rw [sameColorBishops3_checkmateVerdict] at this
  exact Bool.false_ne_true this

theorem kingBishopsStart_checkmateVerdict : checkmateVerdict kingBishopsStart = true := by
  native_decide

theorem kingKnightsStart_checkmateVerdict : checkmateVerdict kingKnightsStart = true := by
  native_decide

theorem kingBishopVsKnight_checkmateVerdict : checkmateVerdict kingBishopVsKnight = true := by
  native_decide

theorem kingBishopVsKnight_CheckmateReachable : CheckmateReachable kingBishopVsKnight :=
  (checkmateVerdict_iff kingBishopVsKnight_valid).mp kingBishopVsKnight_checkmateVerdict

end Position

end Chess
