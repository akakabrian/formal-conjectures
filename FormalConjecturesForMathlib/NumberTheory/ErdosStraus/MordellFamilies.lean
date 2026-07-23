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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.DivisorSquareNormalization

@[expose] public section

/-!
# Small Type-II families underlying Mordell's reduction

The classical reductions modulo `120` and `168` can be expressed using only
strict Type-II factor-pair certificates with offsets `3` and `7`.
-/

namespace ErdosStraus

/-- The class `73 mod 120`, using `(a,b,c,s,d)=(2,5,3t+2,1,7)`. -/
theorem mod_one_twenty_seventy_three_family (t : ℕ) :
    HasDistinctDecomposition (120 * t + 73) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (120 * t + 73) 2 5 (3 * t + 2) 1 7
  · omega
  · norm_num
  · norm_num
  · omega
  · norm_num
  · norm_num
  · nlinarith
  · ring
  · ring

/-- The class `97 mod 120`, using `(a,b,c,s,d)=(1,5,6t+5,2,3)`. -/
theorem mod_one_twenty_ninety_seven_family (t : ℕ) :
    HasDistinctDecomposition (120 * t + 97) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (120 * t + 97) 1 5 (6 * t + 5) 2 3
  · omega
  · norm_num
  · norm_num
  · omega
  · norm_num
  · norm_num
  · nlinarith
  · ring
  · ring

/-- The class `73 mod 168`, using `(a,b,c,s,d)=(1,42t+20,1,6t+3,7)`. -/
theorem mod_one_sixty_eight_seventy_three_family (t : ℕ) :
    HasDistinctDecomposition (168 * t + 73) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (168 * t + 73) 1 (42 * t + 20) 1 (6 * t + 3) 7
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `97 mod 168`, using `(a,b,c,s,d)=(1,21t+13,2,3t+2,7)`. -/
theorem mod_one_sixty_eight_ninety_seven_family (t : ℕ) :
    HasDistinctDecomposition (168 * t + 97) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (168 * t + 97) 1 (21 * t + 13) 2 (3 * t + 2) 7
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `145 mod 336`, the even-quotient half of `145 mod 168`. -/
theorem mod_three_thirty_six_one_forty_five_family (t : ℕ) :
    HasDistinctDecomposition (336 * t + 145) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (336 * t + 145) 2 (42 * t + 19) 1 (6 * t + 3) 7
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `313 mod 336`, the odd-quotient half of `145 mod 168`. -/
theorem mod_three_thirty_six_three_thirteen_family (t : ℕ) :
    HasDistinctDecomposition (336 * t + 313) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (336 * t + 313) 1 (21 * t + 20) 4 (3 * t + 3) 7
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The complete class `145 mod 168`, obtained by splitting the quotient parity. -/
theorem mod_one_sixty_eight_one_forty_five_family (t : ℕ) :
    HasDistinctDecomposition (168 * t + 145) := by
  have ht := Nat.mod_add_div t 2
  interval_cases h : t % 2
  · have hteq : t = 2 * (t / 2) := by omega
    rw [hteq]
    convert mod_three_thirty_six_one_forty_five_family (t / 2) using 1 <;> ring
  · have hteq : t = 2 * (t / 2) + 1 := by omega
    rw [hteq]
    convert mod_three_thirty_six_three_thirteen_family (t / 2) using 1 <;> ring

end ErdosStraus
