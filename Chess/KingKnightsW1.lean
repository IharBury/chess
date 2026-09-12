import Chess.KingKnights

/-!
Coverage of the engineered king-and-knight policy for white king files `c` and `d`.
-/

namespace Chess.KNState

theorem checkSlice_w1 : checkSlice 2 4 = true := by
  native_decide

/-- Legal states with the white king on the c- or d-file make progress. -/
theorem covered_w1 (s : KNState) (h : 2 ≤ s.wk.file.val ∧ s.wk.file.val < 4) :
    (!s.okB || s.checkState) = true :=
  checkSlice_sound 2 4 checkSlice_w1 s h.1 h.2

end Chess.KNState
