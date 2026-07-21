/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.WrittenOnTheWallII.GraphConjecture217

/-!
# WOWII Conjecture 217 isolated formalization attempt

This scratch module preserves the upstream target and records only kernel-checkable
reductions. It is intentionally kept off `main` and is not a submission artifact.
-/

namespace WrittenOnTheWallII.GraphConjecture217

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The indicator is one exactly in the residue-two branch. -/
theorem residueEqTwoIndicator_eq_one_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 1 ↔ residue G = 2 := by
  simp [residueEqTwoIndicator]

/-- The indicator is zero exactly outside the residue-two branch. -/
theorem residueEqTwoIndicator_eq_zero_iff (G : SimpleGraph α) [DecidableRel G.Adj] :
    residueEqTwoIndicator G = 0 ↔ residue G ≠ 2 := by
  simp [residueEqTwoIndicator]

/-- Outside the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 2`. -/
theorem Ls_le_two_of_residue_ne_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G ≠ 2) : Ls G ≤ 2 := by
  simpa [residueEqTwoIndicator, hr] using hL

/-- In the residue-two branch, the conjecture hypothesis reduces to `Ls G ≤ 6`. -/
theorem Ls_le_six_of_residue_eq_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2)
    (hr : residue G = 2) : Ls G ≤ 6 := by
  simpa [residueEqTwoIndicator, hr] using hL

end WrittenOnTheWallII.GraphConjecture217
