import Chess.EndsGame
import Chess.KingKnights
import Chess.KingKnightsMate
import Chess.KingKnightsW0
import Chess.KingKnightsW1
import Chess.KingKnightsW2
import Chess.KingKnightsW3

/-!
# King and knight versus king and knight: reachability

Every legal king-and-knight versus king-and-knight state is covered by
the engineered policy of `Chess.KingKnights`. The exhaustive Boolean
check is split by white-king file across `Chess.KingKnightsW0`–`W3`.
Strong induction on the potential then yields `CheckmateReachable`.
-/

namespace Chess

namespace KNState

open Position

/-- Every state is illegal or makes progress under the engineered policy. -/
theorem covered (s : KNState) : (!s.okB || s.checkState) = true := by
  rcases Nat.lt_or_ge s.wk.file.val 2 with h0 | h0
  · exact covered_w0 s h0
  rcases Nat.lt_or_ge s.wk.file.val 4 with h1 | h1
  · exact covered_w1 s ⟨h0, h1⟩
  rcases Nat.lt_or_ge s.wk.file.val 6 with h2 | h2
  · exact covered_w2 s ⟨h1, h2⟩
  · exact covered_w3 s h2

/-- Every legal state makes progress: the check `covered`. -/
theorem progress_exists {s : KNState} (hok : s.okB = true) : ∃ s1, Progress s s1 := by
  have h := covered s
  simp only [hok, Bool.not_true, Bool.false_or] at h
  exact checkState_sound hok h

theorem checkmateReachable_of_okB_aux :
    ∀ n (s : KNState), s.okB = true → s.mu = n → CheckmateReachable s.toPosition := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hok hn
    obtain ⟨s1, hok1, hr, hp⟩ := progress_exists hok
    rcases hp with hm | hlt
    · exact ⟨s1.toPosition, hr, inCheckmate_of_mateB hok1 hm⟩
    · obtain ⟨q, hrq, hq⟩ := ih s1.mu (hn ▸ hlt) s1 hok1 rfl
      exact ⟨q, hr.trans hrq, hq⟩

/-- From every legal king-and-knight versus king-and-knight state,
checkmate is reachable. -/
theorem checkmateReachable_of_okB {s : KNState} (hok : s.okB = true) :
    CheckmateReachable s.toPosition :=
  checkmateReachable_of_okB_aux s.mu s hok rfl

end KNState

namespace Position

/-- King and knight versus king and knight: checkmate is reachable from
every valid position. -/
theorem IsKingKnights.checkmateReachable {p : Position} (hv : Valid p)
    (h : IsKingKnights p) : CheckmateReachable p := by
  obtain ⟨s, hok, rfl⟩ := exists_knState_of_kingKnights hv h
  exact KNState.checkmateReachable_of_okB hok

/-- King and knight versus king and knight: the position is not dead. -/
theorem IsKingKnights.not_deadPosition {p : Position} (hv : Valid p)
    (h : IsKingKnights p) : ¬ DeadPosition p :=
  not_deadPosition_of_checkmateReachable (h.checkmateReachable hv)

/-- Decides whether checkmate is reachable from a valid king-and-knight
versus king-and-knight position: it always is. -/
def kingKnightsCheckmateReachable (p : Position) (hv : Valid p) (h : IsKingKnights p) :
    Decidable (CheckmateReachable p) :=
  isTrue (h.checkmateReachable hv)

/-- Checkmate is reachable from the starting example. -/
theorem kingKnightsStart_CheckmateReachable : CheckmateReachable kingKnightsStart :=
  kingKnightsStart_isKingKnights.checkmateReachable kingKnightsStart_valid

set_option maxRecDepth 100000

/-- The engineered line is legal. -/
theorem kingKnightsStart_matingLine_legal :
    pathLegal kingKnightsStart (kingKnightsMatingLine kingKnightsStart) = true := by
  native_decide

/-- The engineered line ends in checkmate. -/
theorem kingKnightsStart_matingLine_inCheckmate :
    (playSeq kingKnightsStart (kingKnightsMatingLine kingKnightsStart)).inCheckmate = true := by
  native_decide

/-- Checkmate is reachable from the starting example, by its concrete line. -/
theorem kingKnightsStart_CheckmateReachable' : CheckmateReachable kingKnightsStart :=
  checkmateReachable_of_legalSeq
    ((pathLegal_iff _ _).mp kingKnightsStart_matingLine_legal)
    ((inCheckmate_eq_true_iff _).mp kingKnightsStart_matingLine_inCheckmate)

/-- The decision procedure agrees. -/
theorem kingKnightsStart_decide_CheckmateReachable :
    @decide (CheckmateReachable kingKnightsStart)
      (kingKnightsCheckmateReachable kingKnightsStart kingKnightsStart_valid
        kingKnightsStart_isKingKnights) = true := by
  native_decide

theorem kingKnightsStart_not_deadPosition : ¬ DeadPosition kingKnightsStart :=
  not_deadPosition_of_checkmateReachable kingKnightsStart_CheckmateReachable

end Position

end Chess
