import Chess.KingQueen

/-!
Exhaustive covering of one white-king file of king-and-queen versus king.
Kept in its own module so `native_decide` can run in parallel with the
other files, and not inside the definition file.
-/

namespace Chess.KQState

set_option maxHeartbeats 0
theorem checkFile4 : checkFile 4 = true := by native_decide

end Chess.KQState
