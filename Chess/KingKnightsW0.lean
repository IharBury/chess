import Chess.KingKnights

/-!
Coverage of the engineered king-and-knight policy for white king files `a` and `b`.
-/

namespace Chess.KNState

set_option maxHeartbeats 0 in
-- `native_decide` of the nested covering loop exceeds the default heartbeat budget.
theorem checkSlice_w0 : checkSlice 0 2 = true := by
  native_decide

/-- Legal states with the white king on the a- or b-file make progress. -/
theorem covered_w0 (s : KNState) (h : s.wk.file.val < 2) :
    (!s.okB || s.checkState) = true :=
  checkSlice_sound 0 2 checkSlice_w0 s (Nat.zero_le _) h

end Chess.KNState
