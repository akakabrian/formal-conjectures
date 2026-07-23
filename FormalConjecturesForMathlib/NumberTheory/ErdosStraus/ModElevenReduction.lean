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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.ModElevenFamilies

@[expose] public section

/-!
# The modulo-11 and modulo-9240 reductions

Combining the two surviving classes modulo `120` with the `d=11` families
leaves twelve possible prime-counterexample classes modulo `1320`. Combining
those with Mordell's modulo-168 reduction and the corrected `1201` and `6001`
families leaves 34 classes modulo `9240`.
-/

namespace ErdosStraus

/-- The twelve classes left after the modulo-11 sieve. -/
def IsModElevenResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 49 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529 ∨
    r = 721 ∨ r = 841 ∨ r = 889 ∨ r = 961 ∨ r = 1081 ∨ r = 1201

/-- A prime strict counterexample in `1 mod 24` lies in one of twelve classes modulo `1320`. -/
theorem prime_counterexample_mod_one_three_two_zero
    (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1)
    (hnot : ¬ HasDistinctDecomposition p) :
    IsModElevenResidue (p % 1320) := by
  have h120 := prime_counterexample_mod_one_twenty p hp hp24 hnot
  have hdiv120 := Nat.mod_add_div p 120
  have hdiv11 := Nat.mod_add_div (p / 120) 11
  have hdiv1320 := Nat.mod_add_div p 1320
  have hlt1320 : p % 1320 < 1320 := Nat.mod_lt p (by norm_num)
  have hclasses :
      (p / 120) % 11 = 0 ∨ (p / 120) % 11 = 1 ∨
      (p / 120) % 11 = 2 ∨ (p / 120) % 11 = 3 ∨
      (p / 120) % 11 = 4 ∨ (p / 120) % 11 = 5 ∨
      (p / 120) % 11 = 6 ∨ (p / 120) % 11 = 7 ∨
      (p / 120) % 11 = 8 ∨ (p / 120) % 11 = 9 ∨
      (p / 120) % 11 = 10 := by
    omega
  rcases h120 with h120 | h120
  · rcases hclasses with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
    · dsimp [IsModElevenResidue]
      omega
    · have h11p : 11 ∣ p := by
        refine ⟨120 * ((p / 120) / 11) + 11, ?_⟩
        omega
      rcases hp.eq_one_or_self_of_dvd 11 h11p with hbad | hp11
      · norm_num at hbad
      · have hpeq : p = 11 := hp11.symm
        subst p
        norm_num at hp24
    · have hform : p = 1320 * ((p / 120) / 11) + 241 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_two_forty_one_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · dsimp [IsModElevenResidue]
      omega
    · have hform : p = 1320 * ((p / 120) / 11) + 481 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_four_eighty_one_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · have hform : p = 1320 * ((p / 120) / 11) + 601 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_six_zero_one_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
  · rcases hclasses with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
    · dsimp [IsModElevenResidue]
      omega
    · have hform : p = 1320 * ((p / 120) / 11) + 409 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_four_zero_nine_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · dsimp [IsModElevenResidue]
      omega
    · have h11p : 11 ∣ p := by
        refine ⟨120 * ((p / 120) / 11) + 59, ?_⟩
        omega
      rcases hp.eq_one_or_self_of_dvd 11 h11p with hbad | hp11
      · norm_num at hbad
      · have hpeq : p = 11 := hp11.symm
        subst p
        norm_num at hp24
    · have hform : p = 1320 * ((p / 120) / 11) + 769 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_seven_sixty_nine_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · dsimp [IsModElevenResidue]
      omega
    · have hform : p = 1320 * ((p / 120) / 11) + 1009 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_one_zero_zero_nine_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · have hform : p = 1320 * ((p / 120) / 11) + 1129 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_one_one_two_nine_family ((p / 120) / 11)
      exact (hnot hdec).elim
    · have hform : p = 1320 * ((p / 120) / 11) + 1249 := by omega
      have hdec : HasDistinctDecomposition p := by
        rw [hform]
        exact mod_one_three_two_zero_one_two_four_nine_family ((p / 120) / 11)
      exact (hnot hdec).elim

/-- The 34 classes left by the corrected Ionascu–Wilson modulo-9240 sieve. -/
def IsModNineTwoFourZeroResidue (r : ℕ) : Prop :=
  r = 1 ∨ r = 169 ∨ r = 289 ∨ r = 361 ∨ r = 529 ∨ r = 841 ∨
    r = 961 ∨ r = 1369 ∨ r = 1681 ∨ r = 1849 ∨ r = 2041 ∨ r = 2209 ∨
    r = 2521 ∨ r = 2641 ∨ r = 2689 ∨ r = 2809 ∨ r = 3361 ∨ r = 3481 ∨
    r = 3529 ∨ r = 3721 ∨ r = 4321 ∨ r = 4489 ∨ r = 5041 ∨ r = 5161 ∨
    r = 5329 ∨ r = 5569 ∨ r = 6169 ∨ r = 6241 ∨ r = 6889 ∨ r = 7561 ∨
    r = 7681 ∨ r = 7921 ∨ r = 8089 ∨ r = 8761

/-- A prime strict counterexample lies in one of 34 classes modulo `9240`. -/
theorem prime_counterexample_mod_nine_two_four_zero
    (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1)
    (hnot : ¬ HasDistinctDecomposition p) :
    IsModNineTwoFourZeroResidue (p % 9240) := by
  have h1320 := prime_counterexample_mod_one_three_two_zero p hp hp24 hnot
  have h168 := prime_counterexample_mod_one_sixty_eight p hp hp24 hnot
  have hmod1320 : (p % 9240) % 1320 = p % 1320 :=
    Nat.mod_mod_of_dvd p ⟨7, by norm_num⟩
  have hmod168 : (p % 9240) % 168 = p % 168 :=
    Nat.mod_mod_of_dvd p ⟨55, by norm_num⟩
  have hlt9240 : p % 9240 < 9240 := Nat.mod_lt p (by norm_num)
  have hdiv9240 := Nat.mod_add_div p 9240
  have hne1201 : p % 9240 ≠ 1201 := by
    intro h1201
    have hform : p = 9240 * (p / 9240) + 1201 := by omega
    apply hnot
    rw [hform]
    exact mod_nine_two_four_zero_one_two_zero_one_family (p / 9240)
  have hne6001 : p % 9240 ≠ 6001 := by
    intro h6001
    have hform : p = 9240 * (p / 9240) + 6001 := by omega
    apply hnot
    rw [hform]
    exact mod_nine_two_four_zero_six_zero_zero_one_family (p / 9240)
  rw [← hmod1320] at h1320
  rw [← hmod168] at h168
  dsimp [IsModElevenResidue] at h1320
  dsimp [IsModNineTwoFourZeroResidue]
  rcases h1320 with h1 | h49 | h169 | h289 | h361 | h529 |
      h721 | h841 | h889 | h961 | h1081 | h1201 <;>
    rcases h168 with h1' | h25' | h121' <;> omega

/-- Failure implies a prime counterexample in one of the twelve modulo-1320 classes. -/
theorem exists_prime_counterexample_mod_one_three_two_zero
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ IsModElevenResidue (p % 1320) ∧
      ¬ HasDistinctDecomposition p := by
  obtain ⟨p, hp, hp24, hnot⟩ := exists_prime_counterexample_one_mod_twenty_four h
  exact ⟨p, hp, prime_counterexample_mod_one_three_two_zero p hp hp24 hnot, hnot⟩

/-- Failure implies a prime counterexample in one of 34 classes modulo `9240`. -/
theorem exists_prime_counterexample_mod_nine_two_four_zero
    (h : ∃ n : ℕ, IsCounterexample n) :
    ∃ p : ℕ, p.Prime ∧ IsModNineTwoFourZeroResidue (p % 9240) ∧
      ¬ HasDistinctDecomposition p := by
  obtain ⟨p, hp, hp24, hnot⟩ := exists_prime_counterexample_one_mod_twenty_four h
  exact ⟨p, hp, prime_counterexample_mod_nine_two_four_zero p hp hp24 hnot, hnot⟩

end ErdosStraus
