import Chess.KingRookCover.File0
import Chess.KingRookCover.File1
import Chess.KingRookCover.File2
import Chess.KingRookCover.File3
import Chess.KingRookCover.File4
import Chess.KingRookCover.File5
import Chess.KingRookCover.File6
import Chess.KingRookCover.File7

/-!
Glue for the eight king-and-rook covering files. Each file
`native_decide`s one white-king file; this module combines them into
`checkAll_true`.
-/

namespace Chess.KRState

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

end Chess.KRState
