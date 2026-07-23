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
# Scaling Erdős–Straus decompositions

Multiplying the target denominator and each witness by the same positive
integer preserves both the certificate identity and strict ordering.
-/

namespace ErdosStraus

/-- Multiplying the target denominator and all three witnesses preserves a decomposition. -/
theorem HasDecomposition.scale {n m : ℕ}
    (h : HasDecomposition n) (hm : 0 < m) :
    HasDecomposition (m * n) := by
  rcases h with ⟨x, y, z, hx, hy, hz, hEq⟩
  refine ⟨m * x, m * y, m * z, by positivity, by positivity, by positivity, ?_⟩
  calc
    4 * (m * x) * (m * y) * (m * z)
        = m ^ 3 * (4 * x * y * z) := by ring
    _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hEq]
    _ = (m * n) * ((m * x) * (m * y) + (m * x) * (m * z) + (m * y) * (m * z)) := by
      ring

/-- Scaling also preserves strict denominator order. -/
theorem HasDistinctDecomposition.scale {n m : ℕ}
    (h : HasDistinctDecomposition n) (hm : 0 < m) :
    HasDistinctDecomposition (m * n) := by
  rcases h with ⟨x, y, z, hx, hxy, hyz, hEq⟩
  have hmx : 0 < m * x := by positivity
  refine ⟨m * x, m * y, m * z, by omega, ?_, ?_, ?_⟩
  · exact (Nat.mul_lt_mul_left hm).2 hxy
  · exact (Nat.mul_lt_mul_left hm).2 hyz
  · calc
      4 * (m * x) * (m * y) * (m * z)
          = m ^ 3 * (4 * x * y * z) := by ring
      _ = m ^ 3 * (n * (x * y + x * z + y * z)) := by rw [hEq]
      _ = (m * n) * ((m * x) * (m * y) + (m * x) * (m * z) + (m * y) * (m * z)) := by
        ring

end ErdosStraus
