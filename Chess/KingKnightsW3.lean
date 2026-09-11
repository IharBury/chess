import Chess.KingKnights

/-!
Coverage of the engineered king-and-knight policy for white king files `g` and `h`.
-/

namespace Chess.KNState

set_option maxHeartbeats 0 in
theorem checkSlice_w3 : checkSlice 6 8 = true := by
  native_decide

/-- Legal states with the white king on the g- or h-file make progress. -/
theorem covered_w3 (s : KNState) (h : 6 ≤ s.wk.file.val) :
    (!s.okB || s.checkState) = true :=
  checkSlice_sound 6 8 checkSlice_w3 s h s.wk.file.isLt

end Chess.KNState
