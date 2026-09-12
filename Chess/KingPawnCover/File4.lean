import Chess.KingPawn

/-!
Exhaustive covering of one white-king file of king-and-pawn versus king.
Kept in its own module so `native_decide` can run in parallel with the
other files, and not inside the definition file.
-/

namespace Chess.KPState

set_option maxHeartbeats 0 in
-- `native_decide` of one white-king file; heartbeat bound would abort it.
theorem checkFile4 : checkFile 4 = true := by native_decide

end Chess.KPState
