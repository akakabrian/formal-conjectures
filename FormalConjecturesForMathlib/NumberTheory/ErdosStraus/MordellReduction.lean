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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MinimalCounterexample
public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MordellFamilies

@[expose] public section

/-!
# Mordell's six residual classes modulo 840

The `d=3` and `d=7` strict Type-II families reduce a hypothetical prime
counterexample from `1 mod 24` to the six classical Mordell classes modulo
`840`.
-/

namespace ErdosStraus

/-- A prime strict counterexample in `1 mod 24` is `1` or `49 mod 120`. -/
theorem prime_counterexample_mod_one_twenty
    (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1)
    (hnot : ¬ HasDistinctDecomposition p) :
    p % 120 = 1 ∨ p % 120 = 49 := by
  have hdiv24 := Nat.mod_add_div p 24
  have hdiv5 := Nat.mod_add_div (p / 24) 5
  have hdiv120 := Nat.mod_add_div p 120
  have hclasses :
      (p / 24) % 5 = 0 ∨ (p / 24) % 5 = 1 ∨ (p / 24) % 5 = 2 ∨
        (p / 24) % 5 = 3 ∨ (p / 24) % 5 = 4 := by
    omega
  rcases hclasses with h0 | h1 | h2 | h3 | h4
  · left
    omega
  · have h5p : 5 ∣ p := by
      refine ⟨24 * ((p / 24) / 5) + 5, ?_⟩
      omega
    have hp5 : p = 5 := (hp.dvd_iff_eq (by norm_num)).mp h5p
    omega
  · right
    omega
  · have hform : p = 120 * ((p / 24) / 5) + 73 := by omega
    exact (hnot (by simpa [hform] using
      mod_one_twenty_seventy_three_family ((p / 24) / 5))).elim
  · have hform : p = 120 * ((p / 24) / 5) + 97 := by omega
    exact (hnot (by simpa [hform] using
      mod_one_twenty_ninety_seven_family ((p / 24) / 5))).elim

/-- A prime strict counterexample in `1 mod 24` is `1`, `25`, or `121 mod 168`. -/
theorem prime_counterexample_mod_one_sixty_eight
    (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1)
    (hnot : ¬ HasDistinctDecomposition p) :
    p % 168 = 1 ∨ p % 168 = 25 ∨ p % 168 = 121 := by
  have hdiv24 := Nat.mod_add_div p 24
  have hdiv7 := Nat.mod_add_div (p / 24) 7
  have hdiv168 := Nat.mod_add_div p 168
  have hclasses :
      (p / 24) % 7 = 0 ∨ (p / 24) % 7 = 1 ∨ (p / 24) % 7 = 2 ∨
        (p / 24) % 7 = 3 ∨ (p / 24) % 7 = 4 ∨ (p / 24) % 7 = 5 ∨
        (p / 24) % 7 = 6 := by
    omega
  rcases hclasses with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · left
    omega
  · right
    left
    omega
  · have h7p : 7 ∣ p := by
      refine ⟨24 * ((p / 24) / 7) + 7, ?_⟩
      omega
    have hp7 : p = 7 := (hp.dvd_iff_eq (by norm_num)).mp h7p
    omega
  · have hform : p = 168 * ((p / 24) / 7) + 73 := by omega
    exact (hnot (by simpa [hform] using
      mod_one_sixty_eight_seventy_three_family ((p / 24) / 7))).elim
  · have hform : p = 168 * ((p / 24) / 7) + 97 := by omega
    exact (hnot (by simpa [hform] using
      mod_one_sixty_eight_ninety_seven_family ((p / 24) / 7))).elim
  · right
    right
    omega
  · have hform : p = 168 * ((p / 24) / 7) + 145 := by omega
    exact (hnot (by simpa [hform] using
      mod_one_sixty_eight_one_forty_five_family ((p / 24) / 7))).elim

/-- The six classical Mordell residual classes modulo `840`. -/
def IsMordellResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 121 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529

/-- A prime strict counterexample lies in one of the six Mordell classes modulo `840`. -/
theorem prime_counterexample_mod_eight_forty
    (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1)
    (hnot : ¬ HasDistinctDecomposition p) :
    IsMordellResidue (p % 840) := by
  have h120 := prime_counterexample_mod_one_twenty p hp hp24 hnot
  have h168 := prime_counterexample_mod_one_sixty_eight p hp hp24 hnot
  have hmod120 : (p % 840) % 120 = p % 120 :=
    Nat.mod_mod_of_dvd p ⟨7, by norm_num⟩
  have hmod168 : (p % 840) % 168 = p % 168 :=
    Nat.mod_mod_of_dvd p ⟨5, by norm_num⟩
  rcases h120 with h120 | h120 <;>
    rcases h168 with h168 | h168 | h168 <;>
    dsimp [IsMordellResidue] <;> omega

/-- Failure of the conjecture implies a prime counterexample in a Mordell class. -/
theorem exists_prime_counterexample_mordell
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ IsMordellResidue (p % 840) ∧
      ¬ HasDistinctDecomposition p := by
  obtain ⟨p, hp, hp24, hnot⟩ := exists_prime_counterexample_one_mod_twenty_four h
  exact ⟨p, hp, prime_counterexample_mod_eight_forty p hp hp24 hnot, hnot⟩

end ErdosStraus
