import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabLaplaceODE
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalBuchstabAbel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailTransportLimit

/-! Euler identification and effective compact reduction for the original joint kernel. -/
namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set Filter Real LiLiuPrereqBuchstab SecondFunctionalCoupled
open scoped Topology

/-- Two independently proved limits of the same literal scaled transform identify the constant. -/
theorem buchstabTailLimit_eq_exp_neg_euler :
    buchstabTailLimit = exp (-eulerMascheroniConstant) :=
  tendsto_nhds_unique tendsto_mul_buchstabLaplace_zero buchstabLaplace_scaled_tendsto

theorem buchstab_tendsto_exp_neg_euler :
    Tendsto buchstab atTop (𝓝 (exp (-eulerMascheroniConstant))) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using tendsto_buchstab_tail_limit

theorem buchstab_euler_tail_error (m : ℕ) (hm : 3 ≤ m) (u : ℝ) (hu : (m : ℝ) ≤ u) :
    |buchstab u - exp (-eulerMascheroniConstant)| ≤ 4 / (m.factorial : ℝ) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using buchstab_tail_limit_error m hm u hu

/-- The mass is the sum of the twelve original weighted geometric integrals. -/
theorem kernel_euler_tail_error (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {phi : ℝ}
    (hphi : ((m : ℝ) + 6) / 2 ≤ phi) :
    |kernel p phi - exp (-eulerMascheroniConstant) * M p| ≤
      4 * M p / (m.factorial : ℝ) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using kernel_tail_error p hp hs m hm hphi

theorem kernel_tendsto_euler (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    Tendsto (kernel p) atTop (𝓝 (exp (-eulerMascheroniConstant) * M p)) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using kernel_tendsto p hp hs

/-- A rigorous sandwich, not an unconditional equality with the compact supremum. -/
theorem compact_euler_tail_sandwich (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {P : ℝ}
    (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P) :
    max (compactSup p P) (exp (-eulerMascheroniConstant) * M p) ≤ jointSup p ∧
      jointSup p ≤ max (compactSup p P)
        (exp (-eulerMascheroniConstant) * M p + 4 * M p / (m.factorial : ℝ)) := by
  simpa only [buchstabTailLimit_eq_exp_neg_euler] using compact_tail_sandwich p hp hs m hm hP

/-- The compact head together with the exact tail center approximates the unbounded supremum. -/
theorem jointSup_compact_euler_error (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (m : ℕ) (hm : 3 ≤ m) {P : ℝ}
    (hP : max 2 (((m : ℝ) + 6) / 2) ≤ P) :
    |jointSup p - max (compactSup p P) (exp (-eulerMascheroniConstant) * M p)| ≤
      4 * M p / (m.factorial : ℝ) := by
  obtain ⟨hlo, hhi⟩ := compact_euler_tail_sandwich p hp hs m hm hP
  have herr : 0 ≤ 4 * M p / (m.factorial : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) (M_nonneg p hp hs)) (by positivity)
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  apply sub_le_iff_le_add.mpr
  apply hhi.trans
  apply max_le
  · exact (le_max_left (compactSup p P) (exp (-eulerMascheroniConstant) * M p)).trans
      (le_add_of_nonneg_left herr)
  · linarith only [le_max_right (compactSup p P) (exp (-eulerMascheroniConstant) * M p)]

end Wu2008DoubleSieve.SecondFunctionalJointTail
