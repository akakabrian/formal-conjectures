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

public import FormalConjecturesForMathlib.NumberTheory.ErdosStraus.MordellReduction

@[expose] public section

/-!
# The modulo-11 Type-II families

These strict families implement the next classical sieve after the reductions
modulo `120` and `168`. They leave twelve classes modulo `1320`. Two later
families remove the classes `1201` and `6001` modulo `9240`.
-/

namespace ErdosStraus

/-- The class `241 mod 1320`, using `(a,b,c,s,d)=(1,110t+21,3,10t+2,11)`. -/
theorem mod_one_three_two_zero_two_forty_one_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 241) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 241) 1 (110 * t + 21) 3 (10 * t + 2) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `481 mod 1320`, using `(a,b,c,s,d)=(3,110t+41,1,10t+4,11)`. -/
theorem mod_one_three_two_zero_four_eighty_one_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 481) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 481) 3 (110 * t + 41) 1 (10 * t + 4) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `601 mod 1320`, using `(a,b,c,s,d)=(1,330t+153,1,30t+14,11)`. -/
theorem mod_one_three_two_zero_six_zero_one_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 601) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 601) 1 (330 * t + 153) 1 (30 * t + 14) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `409 mod 1320`, using `(a,b,c,s,d)=(1,66t+21,5,6t+2,11)`. -/
theorem mod_one_three_two_zero_four_zero_nine_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 409) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 409) 1 (66 * t + 21) 5 (6 * t + 2) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `769 mod 1320`, using `(a,b,c,s,d)=(1,110t+65,3,10t+6,11)`. -/
theorem mod_one_three_two_zero_seven_sixty_nine_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 769) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 769) 1 (110 * t + 65) 3 (10 * t + 6) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `1009 mod 1320`, using `(a,b,c,s,d)=(3,110t+85,1,10t+8,11)`. -/
theorem mod_one_three_two_zero_one_zero_zero_nine_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 1009) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 1009) 3 (110 * t + 85) 1 (10 * t + 8) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `1129 mod 1320`, using `(a,b,c,s,d)=(3,22t+19,5,2t+2,11)`. -/
theorem mod_one_three_two_zero_one_one_two_nine_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 1129) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 1129) 3 (22 * t + 19) 5 (2 * t + 2) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/-- The class `1249 mod 1320`, using `(a,b,c,s,d)=(1,22t+21,15,2t+2,11)`. -/
theorem mod_one_three_two_zero_one_two_four_nine_family (t : ℕ) :
    HasDistinctDecomposition (1320 * t + 1249) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (1320 * t + 1249) 1 (22 * t + 21) 15 (2 * t + 2) 11
  · omega
  · norm_num
  · omega
  · norm_num
  · omega
  · omega
  · nlinarith
  · ring
  · ring

/--
The corrected `1201 mod 9240` identity. The two large denominators contain
`9240t+1201` (not `9240t+1`), and arise from the Type-II parameters
`(a,b,c,s,d)=(1,154,15t+2,5,31)`.
-/
theorem mod_nine_two_four_zero_one_two_zero_one_family (t : ℕ) :
    HasDistinctDecomposition (9240 * t + 1201) := by
  apply typeII_factor_pair_hasDistinctDecomposition
      (9240 * t + 1201) 1 154 (15 * t + 2) 5 31
  · omega
  · norm_num
  · norm_num
  · omega
  · norm_num
  · norm_num
  · nlinarith
  · ring
  · ring

/-- The `6001 mod 9240` strict family from the corrected polynomial identity. -/
theorem mod_nine_two_four_zero_six_zero_zero_one_family (t : ℕ) :
    HasDistinctDecomposition (9240 * t + 6001) := by
  refine ⟨770 * (3 * t + 2),
    22 * (3 * t + 2) * (2034 * t + 1321),
    385 * (9240 * t + 6001) * (2034 * t + 1321),
    ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · ring

end ErdosStraus
