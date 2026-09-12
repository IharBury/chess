import Chess.KingQueenCover.File0
import Chess.KingQueenCover.File1
import Chess.KingQueenCover.File2
import Chess.KingQueenCover.File3
import Chess.KingQueenCover.File4
import Chess.KingQueenCover.File5
import Chess.KingQueenCover.File6
import Chess.KingQueenCover.File7

/-!
Glue for the eight king-and-queen covering files. Each file
`native_decide`s one white-king file; this module combines them into
`checkAll_true`.
-/

namespace Chess.KQState

theorem checkFile_true (f : Fin 8) : checkFile f = true :=
  match f with
  | ⟨0, _⟩ => checkFile0
  | ⟨1, _⟩ => checkFile1
  | ⟨2, _⟩ => checkFile2
  | ⟨3, _⟩ => checkFile3
  | ⟨4, _⟩ => checkFile4
  | ⟨5, _⟩ => checkFile5
  | ⟨6, _⟩ => checkFile6
  | ⟨7, _⟩ => checkFile7

theorem checkAll_true : checkAll = true := by
  refine List.all_eq_true.mpr ?_
  intro wk _
  rcases wk with ⟨f, r⟩
  exact (List.all_eq_true.mp (checkFile_true f)) r (by simp [List.mem_finRange])

end Chess.KQState
