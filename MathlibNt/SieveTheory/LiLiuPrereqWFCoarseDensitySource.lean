import MathlibNt.SieveTheory.LiLiuPrereqWFAnalytic
import MathlibNt.SieveTheory.SuzukiUpperSourcePTail

/-!
# The genuine continuous mass of the ordinary Rosser producer

The Suzuki parity series, not the Section-13 hats, are `F - 1` and `1 - f`.
The amplitude comes from the admitted adjoint pairing. The identification
extends from the initial intervals by the integral method of steps, with no
upper bound on the sieve coordinate or on the finite source depth.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity

open MeasureTheory intervalIntegral Set
open SuzukiFiniteContinuousLayers
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical BigOperators Interval

theorem sourceTPlus_eq_jr1965F_sub_one_initial {s : ℝ}
    (hs1 : 1 < s) (hs3 : s ≤ 3) :
    suzukiProposition118SourceTPlus s = jr1965F s - 1 := by
  have h := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub
    jr1965Section13HatSourceContract hs1 hs3
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract] at h
  rw [jr1965F_eq_of_le_three hs3]
  have hsne : s ≠ 0 := by linarith
  field_simp
  nlinarith

theorem sourceTMinus_eq_one_sub_jr1965f_initial {s : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiProposition118SourceTMinus s = 1 - jr1965f s := by
  have hrec := jr1965f_integral_recurrence (v := 2) le_rfl hs2
  have hint :
      (∫ t in (2 : ℝ)..s, jr1965F (t - 1)) =
        (2 * Real.exp Real.eulerMascheroniConstant) *
          ∫ t in (2 : ℝ)..s, (t - 1)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hs2] at ht
    change jr1965F (t - 1) =
      2 * Real.exp Real.eulerMascheroniConstant * (t - 1)⁻¹
    rw [jr1965F_eq_of_le_three (by linarith [ht.2])]
    exact div_eq_mul_inv _ _
  rw [jr1965f_initial le_rfl, mul_zero, zero_add, hint] at hrec
  have hsource :=
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs2 hs4
  unfold suzukiLowerSieveFactorFirstInterval at hsource
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract] at hsource
  have hsne : s ≠ 0 := by linarith
  field_simp at hsource
  simp only [one_div] at hsource
  nlinarith

private theorem sourceParity_eq_jr1965_on_strip (n : ℕ) :
    ∀ s : ℝ, 2 ≤ s → s ≤ (n : ℝ) + 3 →
      suzukiProposition118SourceTPlus s = jr1965F s - 1 ∧
      suzukiProposition118SourceTMinus s = 1 - jr1965f s := by
  induction n with
  | zero =>
      intro s hs2 hs3
      constructor
      · exact sourceTPlus_eq_jr1965F_sub_one_initial (by linarith) (by simpa using hs3)
      · exact sourceTMinus_eq_one_sub_jr1965f_initial hs2 (by norm_num at hs3; linarith)
  | succ n ih =>
      intro s hs2 hsN
      by_cases hsold : s ≤ (n : ℝ) + 3
      · exact ih s hs2 hsold
      have hs3 : 3 ≤ s := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hshift : ∀ t ∈ Set.uIcc (3 : ℝ) s,
          suzukiProposition118SourceTPlus (t - 1) = jr1965F (t - 1) - 1 ∧
          suzukiProposition118SourceTMinus (t - 1) = 1 - jr1965f (t - 1) := by
        intro t ht
        rw [Set.uIcc_of_le hs3] at ht
        apply ih (t - 1) (by linarith [ht.1])
        push_cast at hsN
        linarith [ht.2]
      have hFint : IntervalIntegrable (fun t => jr1965F (t - 1)) volume 3 s := by
        apply ContinuousOn.intervalIntegrable
        apply continuousOn_jr1965F.comp (continuousOn_id.sub continuousOn_const)
        intro t ht
        rw [Set.uIcc_of_le hs3] at ht
        change 0 < t - 1
        linarith [ht.1]
      have hfint : IntervalIntegrable (fun t => jr1965f (t - 1)) volume 3 s := by
        apply ContinuousOn.intervalIntegrable
        apply continuousOn_jr1965f.comp (continuousOn_id.sub continuousOn_const)
        intro t ht
        rw [Set.uIcc_of_le hs3] at ht
        change 0 < t - 1
        linarith [ht.1]
      have hp := suzukiProposition118SourceTPlus_weighted_sub
        jr1965Section13HatSourceContract (x := 3) le_rfl hs3
      have hm := suzukiProposition118SourceTMinus_weighted_sub
        jr1965Section13HatSourceContract (x := 3) (by norm_num) hs3
      have hpi :
          (∫ t in (3 : ℝ)..s, suzukiProposition118SourceTPlus (t - 1)) =
            (∫ t in (3 : ℝ)..s, jr1965F (t - 1)) - (s - 3) := by
        rw [intervalIntegral.integral_congr (fun t ht => (hshift t ht).1)]
        rw [intervalIntegral.integral_sub hFint intervalIntegrable_const]
        simp
      have hmi :
          (∫ t in (3 : ℝ)..s, suzukiProposition118SourceTMinus (t - 1)) =
            (s - 3) - ∫ t in (3 : ℝ)..s, jr1965f (t - 1) := by
        rw [intervalIntegral.integral_congr (fun t ht => (hshift t ht).2)]
        rw [intervalIntegral.integral_sub intervalIntegrable_const hfint]
        simp
      rw [hmi, sourceTPlus_eq_jr1965F_sub_one_initial (s := 3)
        (by norm_num) (by norm_num)] at hp
      rw [hpi, sourceTMinus_eq_one_sub_jr1965f_initial (s := 3)
        (by norm_num) (by norm_num)] at hm
      have hF := jr1965F_integral_recurrence (v := 3) (by norm_num) hs3
      have hf := jr1965f_integral_recurrence (v := 3) (by norm_num) hs3
      constructor <;> nlinarith

/-- The exact full continuous masses. In particular neither mass is a JR hat. -/
theorem sourceParity_eq_jr1965 {s : ℝ} (hs : 2 ≤ s) :
    suzukiProposition118SourceTPlus s = jr1965F s - 1 ∧
    suzukiProposition118SourceTMinus s = 1 - jr1965f s :=
  sourceParity_eq_jr1965_on_strip ⌈s⌉₊ s hs (by linarith [Nat.le_ceil s])

theorem finiteSourceLayer_odd_le_jr1965F_sub_one (m : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    finiteSourceLayer 1 2 (2 * m + 1) s ≤ jr1965F s - 1 := by
  rw [← (sourceParity_eq_jr1965 hs).1,
    finiteSourceLayer_two_mul_add_one_eq_oddPartialSum]
  unfold suzukiOddSourceUpperPartialSum suzukiProposition118SourceTPlus
  exact (summable_suzukiProposition118SourceTPlus_of_sourceContract
    jr1965Section13HatSourceContract (by linarith)).sum_le_tsum _
      (fun k _ => suzukiLayer_one_two_odd_nonneg (by linarith) k)

theorem finiteSourceLayer_even_le_one_sub_jr1965f (m : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    finiteSourceLayer 1 2 (2 * m) s ≤ 1 - jr1965f s := by
  rw [← (sourceParity_eq_jr1965 hs).2, finiteSourceLayer_two_mul_eq_sum_evenLayers]
  unfold suzukiProposition118SourceTMinus
  exact (summable_suzukiProposition118SourceTMinus_of_sourceContract
    jr1965Section13HatSourceContract hs).sum_le_tsum _
      (fun k _ => suzukiLayer_one_two_even_nonneg hs k)

#check sourceParity_eq_jr1965
#check finiteSourceLayer_odd_le_jr1965F_sub_one
#check finiteSourceLayer_even_le_one_sub_jr1965f
#print axioms sourceParity_eq_jr1965
#print axioms finiteSourceLayer_odd_le_jr1965F_sub_one
#print axioms finiteSourceLayer_even_le_one_sub_jr1965f

end MathlibNt.SieveTheory.LiLiuPrereqWF.CoarseDensity
