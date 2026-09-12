import Chess.KingRook

/-!
Exhaustive covering of one white-king file of king-and-rook versus king.
Kept in its own module so `native_decide` can run in parallel with the
other files, and not inside the definition file.
-/

namespace Chess.KRState

set_option maxHeartbeats 0
theorem checkFile3 : checkFile 3 = true := by native_decide

end Chess.KRState
