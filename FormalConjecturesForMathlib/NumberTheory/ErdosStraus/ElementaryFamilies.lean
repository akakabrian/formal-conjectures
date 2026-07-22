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
module

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Basic

@[expose] public section

/-!
# Elementary Erdős–Straus families

These distinct-denominator identities eliminate the even numbers and the
residue classes `2 mod 3`, `3 mod 4`, and `5 mod 8`.
-/

namespace ErdosStraus

/-- Every even number `2 * m`, for `m ≥ 2`, has a distinct decomposition. -/
theorem even_family (m : ℕ) (hm : 2 ≤ m) :
    HasDistinctDecomposition (2 * m) := by
  refine ⟨m, m + 1, m * (m + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · ring

/-- Every number of the form `3 * k + 2`, for `k ≥ 1`, has a distinct decomposition. -/
theorem mod_three_two_family (k : ℕ) (hk : 1 ≤ k) :
    HasDistinctDecomposition (3 * k + 2) := by
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1),
    by omega, by omega, ?_, ?_⟩
  · nlinarith
  · ring

/-- Every number of the form `4 * k + 3` has a distinct decomposition. -/
theorem mod_four_three_family (k : ℕ) :
    HasDistinctDecomposition (4 * k + 3) := by
  let M := (4 * k + 3) * (k + 1)
  have hM : 1 < M := by
    dsimp [M]
    nlinarith
  have hMpos : 0 < M + 1 := by omega
  refine ⟨k + 1, M + 1, M * (M + 1), by omega, ?_, ?_, ?_⟩
  · dsimp [M]
    nlinarith
  · calc
      M + 1 = (M + 1) * 1 := by simp
      _ < (M + 1) * M := Nat.mul_lt_mul_of_pos_left hM hMpos
      _ = M * (M + 1) := by ring
  · dsimp [M]
    ring

/-- Every number of the form `8 * k + 5` has a distinct decomposition. -/
theorem mod_eight_five_family (k : ℕ) :
    HasDistinctDecomposition (8 * k + 5) := by
  refine ⟨2 * (k + 1), (8 * k + 5) * (k + 1),
    2 * (8 * k + 5) * (k + 1), by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · ring

end ErdosStraus
