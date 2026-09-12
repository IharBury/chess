import Chess.KingKnights

/-!
`mateB` of a legal king-and-knight state is checkmate. Kept in its own
module so the covering slices do not wait on this scan.
-/

namespace Chess.KNState

open Position

/-- Every `mateB` state of an `okB` state is a checkmate position. The
scan skips non-mating states; only the 16 mating pictures compute
`legalMoves`. -/
theorem mateB_covered (s : KNState) :
    (!s.okB || !s.mateB || s.toPosition.inCheckmate) = true := by
  revert s
  native_decide

theorem inCheckmate_of_mateB {s : KNState} (hok : s.okB = true) (hm : s.mateB = true) :
    InCheckmate s.toPosition := by
  have h := mateB_covered s
  simp only [hok, hm, Bool.not_true, Bool.false_or] at h
  exact (inCheckmate_eq_true_iff _).mp h

end Chess.KNState
