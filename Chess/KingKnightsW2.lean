import Chess.KingKnights

/-!
Coverage of the engineered king-and-knight policy for white king files `e` and `f`.
-/

namespace Chess.KNState

set_option maxHeartbeats 0 in
-- `native_decide` of the nested covering loop exceeds the default heartbeat budget.
theorem checkSlice_w2 : checkSlice 4 6 = true := by
  native_decide

/-- Legal states with the white king on the e- or f-file make progress. -/
theorem covered_w2 (s : KNState) (h : 4 ≤ s.wk.file.val ∧ s.wk.file.val < 6) :
    (!s.okB || s.checkState) = true :=
  checkSlice_sound 4 6 checkSlice_w2 s h.1 h.2

end Chess.KNState
