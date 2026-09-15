import WSrcSixthGainOriginal

noncomputable section
namespace WuPaper.RMapMSixth
open Real Set MeasureTheory QuarterTrim Wu2008DoubleSieve
open WuSource.SrcSixthGain
open scoped Interval

def c6Lower (t : ℝ) : ℝ := (3*alpha-t)/alpha
def c6Upper (t : ℝ) : ℝ := (1/2-beta-t)/alpha
def paperC6 (p : ℝ → ℝ) : ℝ :=
  8*∫ t in alpha..beta, ∫ s in c6Lower t..c6Upper t, paperKernel p t s

def c6A (s : ℝ) : ℝ :=
  if s ≤ 2 then 0 else if s ≤ 4 then log (s-1) else
    log (s-1) + ∫ t in (3 : ℝ)..(s-1),
      (∫ u in (2 : ℝ)..(t-1), log (u-1)/u)/t

theorem c6_interval (t : ℝ) : c6Lower t ≤ c6Upper t := by
  apply div_le_div_of_nonneg_right _ alpha_pos.le
  have h : 3*alpha ≤ 1/2-beta := by norm_num [alpha,beta]
  linarith

theorem c6_domain_iff (t s : ℝ) :
    t ∈ Icc alpha beta ∧ s ∈ Icc (c6Lower t) (c6Upper t) ↔
      (t,1/2-t-alpha*s) ∈ envelope := by
  simp only [c6Lower,c6Upper,envelope,mem_prod,mem_Icc]
  rw [div_le_iff₀ alpha_pos,le_div_iff₀ alpha_pos]
  constructor
  · rintro ⟨ht,hs,hs'⟩
    exact ⟨ht,by linarith,by linarith⟩
  · rintro ⟨ht,hs,hs'⟩
    exact ⟨ht,by linarith,by linarith⟩

theorem c6_parameter_range {t s : ℝ} (ht : t ∈ Icc alpha beta)
    (hs : s ∈ Icc (c6Lower t) (c6Upper t)) :
    3-beta/alpha ≤ s ∧ s ≤ endpoint := by
  have hlo := (div_le_iff₀ alpha_pos).mp hs.1
  have hhi := (le_div_iff₀ alpha_pos).mp hs.2
  constructor
  · have h : (3-beta/alpha)*alpha = 3*alpha-beta := by
      field_simp [alpha_pos.ne']
    apply (mul_le_mul_iff_left₀ alpha_pos).mp
    nlinarith [ht.2]
  · apply (le_div_iff₀ alpha_pos).mpr
    linarith [ht.1]

theorem c6_denominator_positive {t s : ℝ} (ht : t ∈ Icc alpha beta)
    (hs : s ∈ Icc (c6Lower t) (c6Upper t)) :
    0 < t ∧ 0 < s ∧ 0 < 1-2*t-2*alpha*s := by
  have hr := c6_parameter_range ht hs
  have hhi := (le_div_iff₀ alpha_pos).mp hs.2
  have hb : 0 < beta := by norm_num [beta]
  have hlo : 0 < 3-beta/alpha := by norm_num [alpha,beta]
  exact ⟨alpha_pos.trans_le ht.1,hlo.trans_le hr.1,by linarith⟩

theorem c6_breakpoints :
    (3-beta/alpha : ℝ) < 2 ∧ (2 : ℝ) < 4 ∧
      (4 : ℝ) < endpoint ∧ endpoint < 6 := by
  norm_num [endpoint,alpha,beta]

theorem c6_a_eq {s : ℝ} (hs : s ≤ endpoint) : c6A s = wuLowerCoefficient s := by
  by_cases h2 : s ≤ 2
  · rw [c6A,if_pos h2,truncatedSixthZeroDelta_coefficient_zero h2]
  · by_cases h4 : s ≤ 4
    · rw [c6A,if_neg h2,if_pos h4]
      exact (WuTarget.Wu08FifthSource.coefficient_initial (le_of_not_ge h2) h4).symm
    · rw [c6A,if_neg h2,if_neg h4]
      exact (WuTarget.Wu08FifthSource.coefficient_recurrence (le_of_not_ge h4)
        (hs.trans c6_breakpoints.2.2.2.le)).symm

theorem c6_at_two : c6A 2 = 0 := by norm_num [c6A]
theorem c6_at_four : c6A 4 = log 3 := by norm_num [c6A]

theorem c6_inner_transport (p : ℝ → ℝ) (t : ℝ) :
    2*(∫ s in c6Lower t..c6Upper t, paperKernel p t s) =
      ∫ y in beta..(1/2-3*alpha), kernel p t y := by
  have h := paper_inner p t beta (1/2-3*alpha)
  convert h using 1 <;> congr 2 <;> unfold c6Lower c6Upper <;> ring

theorem c6_rectangle_transport (p : ℝ → ℝ) :
    paperC6 p =
      4*∫ t in alpha..beta, ∫ y in beta..(1/2-3*alpha), kernel p t y := by
  have h := intervalIntegral.integral_congr (μ := volume) (a := alpha) (b := beta)
    (fun t _ => c6_inner_transport p t)
  rw [intervalIntegral.integral_const_mul] at h
  unfold paperC6
  linarith only [h]

theorem c6_eq_existing_classical :
    paperC6 wuLowerCoefficient = Wu08TerminalAlignment.sixthMain := by
  rw [c6_rectangle_transport]
  exact truncatedSixthZeroDelta_full_rectangle.symm

theorem c6_literal_complete :
    paperC6 wuLowerCoefficient =
      8*∫ t in alpha..beta, ∫ s in c6Lower t..c6Upper t,
        c6A s/(t*s*(1-2*t-2*alpha*s)) := by
  unfold paperC6
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le envelope_bounds.1] at ht
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (c6_interval t)] at hs
  rw [c6_a_eq (c6_parameter_range ht hs).2]
  rfl

#check @c6Lower
#check @c6Upper
#check @paperC6
#check @c6A
#check @c6_interval
#check @c6_domain_iff
#check @c6_parameter_range
#check @c6_denominator_positive
#check @c6_breakpoints
#check @c6_a_eq
#check @c6_at_two
#check @c6_at_four
#check @c6_inner_transport
#check @c6_rectangle_transport
#check @c6_eq_existing_classical
#check @c6_literal_complete
#print axioms c6Lower
#print axioms c6Upper
#print axioms paperC6
#print axioms c6A
#print axioms c6_interval
#print axioms c6_domain_iff
#print axioms c6_parameter_range
#print axioms c6_denominator_positive
#print axioms c6_breakpoints
#print axioms c6_a_eq
#print axioms c6_at_two
#print axioms c6_at_four
#print axioms c6_inner_transport
#print axioms c6_rectangle_transport
#print axioms c6_eq_existing_classical
#print axioms c6_literal_complete
end WuPaper.RMapMSixth
