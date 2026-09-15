import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherColourCounts

/-! # Complete Gamma colour dictionary and exact prefix formulas -/
namespace Wu2008DoubleSieve

def secondFunctionalMotherGammaWords : ℕ → List (List ℕ)
  | 7 => [[0, 0]]
  | 8 => [[0, 1]]
  | 9 => [[1, 1, 1], [1, 1, 2], [1, 2, 2], [2, 2, 2]]
  | 10 => [[1, 1, 2], [1, 1, 3]]
  | 11 => [[1, 2, 2]]
  | 12 => [[0, 0, 3]]
  | 13 => [[0, 1, 2], [0, 1, 3]]
  | 14 => [[0, 2, 2], [0, 2, 3], [0, 3, 3]]
  | 15 => [[1, 2, 3]]
  | 16 => [[2, 2, 2, 2]]
  | 17 => [[2, 2, 2, 3]]
  | 18 => [[2, 2, 3, 3]]
  | 19 => [[1, 3, 3, 3]]
  | 20 => [[2, 3, 3, 3, 3]]
  | 21 => [[3, 3, 3, 3, 3, 3]]
  | _ => []

def secondFunctionalMotherGammaBand (x y z w i : ℕ) : ℕ :=
  ((secondFunctionalMotherGammaWords i).map (secondFunctionalMotherBandCount x y z w)).sum

theorem secondFunctionalMother_gamma7_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 7 = (x-1) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  omega

theorem secondFunctionalMother_gamma8_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 8 = (if 0 < x then y else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]

theorem secondFunctionalMother_gamma9_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 9 = (if x = 0 then y+z-2 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma10_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 10 = (if x = 0 ∧ 2 ≤ y then z+w else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma11_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 11 = (if x = 0 ∧ y = 1 then z-1 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma12_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 12 = (if 2 ≤ x then w else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma13_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 13 = (if x = 1 ∧ 1 ≤ y then z+w else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma14_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 14 = (if x = 1 ∧ y = 0 then z+w-1 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma15_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 15 = (if x = 0 ∧ y = 1 ∧ 1 ≤ z then w else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma16_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 16 = (if x = 0 ∧ y = 0 then z-3 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma17_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 17 = (if x = 0 ∧ y = 0 ∧ 3 ≤ z then w else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma18_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 18 = (if x = 0 ∧ y = 0 ∧ z = 2 then w-1 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma19_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 19 = (if x = 0 ∧ y = 1 ∧ z = 0 then w-2 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma20_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 20 = (if x = 0 ∧ y = 0 ∧ z = 1 then w-3 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

theorem secondFunctionalMother_gamma21_formula (x y z w : ℕ) :
    secondFunctionalMotherGammaBand x y z w 21 = (if x = 0 ∧ y = 0 ∧ z = 0 then w-5 else 0) := by
  norm_num [secondFunctionalMotherGammaBand, secondFunctionalMotherGammaWords,
    secondFunctionalMotherBandCount]
  split_ifs <;> omega

end Wu2008DoubleSieve
