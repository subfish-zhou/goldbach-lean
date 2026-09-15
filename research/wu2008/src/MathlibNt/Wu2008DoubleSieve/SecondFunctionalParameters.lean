import MathlibNt.Wu2008DoubleSieve.FourthRowMotherBandFormulas

/-! # Five independent parameters of the second functional -/

namespace Wu2008DoubleSieve

structure SecondFunctionalParameters where
  s : ℝ
  S : ℝ
  kappa1 : ℝ
  kappa2 : ℝ
  kappa3 : ℝ

namespace SecondFunctionalParameters

/-- The finite mother hypotheses, separate from analytic admissibility. -/
structure MotherAdmissible (p : SecondFunctionalParameters) : Prop where
  one_le_s : 1 ≤ p.s
  s_le_kappa3 : p.s ≤ p.kappa3
  kappa3_lt_kappa2 : p.kappa3 < p.kappa2
  kappa2_lt_kappa1 : p.kappa2 < p.kappa1
  kappa1_le_S : p.kappa1 ≤ p.S
  S_le_ten : p.S ≤ 10

noncomputable def row1 : SecondFunctionalParameters := ⟨220/100, 454/100, 353/100, 290/100, 244/100⟩
noncomputable def row2 : SecondFunctionalParameters := ⟨230/100, 450/100, 354/100, 288/100, 243/100⟩
noncomputable def row3 : SecondFunctionalParameters := ⟨240/100, 446/100, 357/100, 287/100, 240/100⟩
noncomputable def row4 : SecondFunctionalParameters := ⟨250/100, 412/100, 356/100, 291/100, 250/100⟩

theorem row1_motherAdmissible : row1.MotherAdmissible := by
  constructor <;> norm_num [row1]
theorem row2_motherAdmissible : row2.MotherAdmissible := by
  constructor <;> norm_num [row2]
theorem row3_motherAdmissible : row3.MotherAdmissible := by
  constructor <;> norm_num [row3]
theorem row4_motherAdmissible : row4.MotherAdmissible := by
  constructor <;> norm_num [row4]

theorem row3_last_eq : row3.kappa3 = row3.s := rfl
theorem row4_last_eq : row4.kappa3 = row4.s := rfl

end SecondFunctionalParameters
end Wu2008DoubleSieve
