import Chess.KingKnights

/-!
Exhaustive covering of the engineered king-and-knight policy. Kept in its
own module so the `native_decide` of `checkAll` does not sit in the
definition file.
-/

namespace Chess.KNState

theorem checkAll_true : checkAll = true := by
  native_decide

/-- Every state is illegal or makes progress under the engineered policy. -/
theorem covered (s : KNState) : stateCovered s = true :=
  checkAll_sound checkAll_true s

end Chess.KNState
