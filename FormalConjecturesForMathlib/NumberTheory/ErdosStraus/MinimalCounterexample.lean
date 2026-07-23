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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.Reduction

@[expose] public section

/-!
# Minimal counterexamples

Divisor scaling shows that the least counterexample, if one exists, must be
prime. The elementary residue reduction then places it in `1 mod 24`.
-/

namespace ErdosStraus

/-- A natural number in the range of Erdős Problem 242 which has no strict decomposition. -/
def IsCounterexample (n : ℕ) : Prop :=
  2 < n ∧ ¬ HasDistinctDecomposition n

/-- Failure of the conjecture implies a prime counterexample congruent to `1 mod 24`. -/
theorem exists_prime_counterexample_one_mod_twenty_four
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ p % 24 = 1 ∧ ¬ HasDistinctDecomposition p := by
  classical
  let p := @Nat.find IsCounterexample (Classical.decPred _) h
  have hpCounter : IsCounterexample p := by
    dsimp [p]
    exact @Nat.find_spec IsCounterexample (Classical.decPred _) h
  have hpMin : ∀ {m : ℕ}, m < p → ¬ IsCounterexample m := by
    intro m hm
    dsimp [p] at hm ⊢
    exact @Nat.find_min IsCounterexample (Classical.decPred _) h m hm
  have hpmod : p % 24 = 1 :=
    counterexample_mod_twenty_four_eq_one p hpCounter.1 hpCounter.2
  have hpPrime : p.Prime := by
    have hpTwo : 2 ≤ p := hpCounter.1.le
    rw [Nat.prime_iff_not_exists_mul_eq]
    refine ⟨hpTwo, ?_⟩
    rintro ⟨a, b, ha, hb, hab⟩
    have ha0 : a ≠ 0 := by
      intro hzero
      subst a
      simp at hab
      omega
    have ha1 : a ≠ 1 := by
      intro hone
      subst a
      simp at hab
      omega
    have ha2 : a ≠ 2 := by
      intro htwo
      subst a
      omega
    have ha_gt_two : 2 < a := by omega
    have hbpos : 0 < b := by
      by_contra hnot
      have hbzero : b = 0 := Nat.eq_zero_of_not_pos hnot
      subst b
      simp at hab
      omega
    have haNotCounter : ¬ IsCounterexample a := hpMin ha
    have haDecomp : HasDistinctDecomposition a := by
      by_contra hnot
      exact haNotCounter ⟨ha_gt_two, hnot⟩
    have hscaled : HasDistinctDecomposition (b * a) := haDecomp.scale hbpos
    have hba : b * a = p := by simpa [Nat.mul_comm] using hab
    exact hpCounter.2 (by simpa [hba] using hscaled)
  exact ⟨p, hpPrime, hpmod, hpCounter.2⟩

end ErdosStraus
