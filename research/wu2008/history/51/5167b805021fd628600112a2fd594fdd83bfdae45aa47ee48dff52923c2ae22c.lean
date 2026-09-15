import MathlibNt.Wu2008DoubleSieve.CanonicalUpperExtension

/-!
# Identification of the genuine Suzuki factors through ten

The initial normalized source values and the two integral delay recurrences
determine the factors by seven finite method-of-steps extensions. No explicit
first-interval formula is used outside its interval.
-/

namespace Wu2008DoubleSieve

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

private theorem upper_source_initial {s : ℝ} (hs : 1 < s) (hs3 : s ≤ 3) :
    suzukiContinuousUpperFactor s = jr1965F s := by
  have h := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub
    jr1965Section13HatSourceContract hs hs3
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract] at h
  rw [jr1965F_eq_of_le_three hs3]
  apply (eq_div_iff (by linarith : s ≠ 0)).2
  unfold suzukiContinuousUpperFactor
  nlinarith

private theorem shifted_jr_upper_integrable {s : ℝ} (hs : 3 ≤ s) :
    IntervalIntegrable (fun t => jr1965F (t - 1)) volume 3 s := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_jr1965F.comp
    (continuousOn_id.sub continuousOn_const)
  intro t ht
  rw [uIcc_of_le hs] at ht
  change 0 < t - 1
  linarith [ht.1]

private theorem shifted_jr_lower_integrable {s : ℝ} (hs : 3 ≤ s) :
    IntervalIntegrable (fun t => jr1965f (t - 1)) volume 3 s := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_jr1965f.comp
    (continuousOn_id.sub continuousOn_const)
  intro t ht
  rw [uIcc_of_le hs] at ht
  change 0 < t - 1
  linarith [ht.1]

private theorem bounded_source_factors_steps (n : ℕ) (hn : n ≤ 7) :
    (∀ s : ℝ, 1 < s → s ≤ (n : ℝ) + 3 →
      suzukiContinuousUpperFactor s = jr1965F s) ∧
    (∀ s : ℝ, 2 ≤ s → s ≤ (n : ℝ) + 3 →
      suzukiContinuousLowerFactor s = jr1965f s) := by
  induction n with
  | zero =>
    constructor
    · intro s hs hsb
      exact upper_source_initial hs (by simpa using hsb)
    · intro s hs hsb
      exact suzukiContinuousLowerFactor_eq_jr1965f_firstInterval hs (by
        norm_num at hsb
        linarith)
  | succ n ih =>
    have hprev := ih (by omega)
    constructor
    · intro s hs hsb
      by_cases hs3 : s ≤ 3
      · exact upper_source_initial hs hs3
      have h3s : 3 ≤ s := (lt_of_not_ge hs3).le
      have hsource := suzukiProposition118SourceTPlus_weighted_sub
        jr1965Section13HatSourceContract (x := 3) (by norm_num) h3s
      have hint :
          (∫ t in (3 : ℝ)..s, suzukiProposition118SourceTMinus (t - 1)) =
            (s - 3) - ∫ t in (3 : ℝ)..s, jr1965f (t - 1) := by
        calc
          _ = ∫ t in (3 : ℝ)..s, (1 - jr1965f (t - 1)) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le h3s] at ht
            have h := hprev.2 (t - 1) (by linarith [ht.1]) (by
              push_cast at hsb
              linarith [ht.2])
            unfold suzukiContinuousLowerFactor suzukiContinuousLowerTail at h
            linarith
          _ = _ := by
            rw [intervalIntegral.integral_sub
              (continuousOn_const.intervalIntegrable)
              (shifted_jr_lower_integrable h3s)]
            simp
      rw [hint] at hsource
      have hbase := upper_source_initial (s := 3) (by norm_num) le_rfl
      have hrec := jr1965F_integral_recurrence (v := 3) (by norm_num) h3s
      unfold suzukiContinuousUpperFactor at hbase ⊢
      nlinarith
    · intro s hs hsb
      by_cases hs3 : s ≤ 3
      · exact suzukiContinuousLowerFactor_eq_jr1965f_firstInterval hs (by linarith)
      have h3s : 3 ≤ s := (lt_of_not_ge hs3).le
      have hsource := suzukiProposition118SourceTMinus_weighted_sub
        jr1965Section13HatSourceContract (x := 3) (by norm_num) h3s
      have hint :
          (∫ t in (3 : ℝ)..s, suzukiProposition118SourceTPlus (t - 1)) =
            (∫ t in (3 : ℝ)..s, jr1965F (t - 1)) - (s - 3) := by
        calc
          _ = ∫ t in (3 : ℝ)..s, (jr1965F (t - 1) - 1) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_le h3s] at ht
            have h := hprev.1 (t - 1) (by linarith [ht.1]) (by
              push_cast at hsb
              linarith [ht.2])
            unfold suzukiContinuousUpperFactor at h
            linarith
          _ = _ := by
            rw [intervalIntegral.integral_sub (shifted_jr_upper_integrable h3s)
              (continuousOn_const.intervalIntegrable)]
            simp
      rw [hint] at hsource
      have hbase := suzukiContinuousLowerFactor_eq_jr1965f_firstInterval
        (s := 3) (by norm_num) (by norm_num)
      have hrec := jr1965f_integral_recurrence (v := 3) (by norm_num) h3s
      unfold suzukiContinuousLowerFactor suzukiContinuousLowerTail at hbase ⊢
      nlinarith

/-- The actual summable odd Suzuki source factor equals the constructed
Jurkat--Richert upper function on the bounded source domain. -/
theorem suzukiContinuousUpperFactor_eq_jr1965F_bounded
    {s : ℝ} (hs : 1 < s) (hs10 : s ≤ 10) :
    suzukiContinuousUpperFactor s = jr1965F s :=
  (bounded_source_factors_steps 7 le_rfl).1 s hs (by norm_num; exact hs10)

/-- The actual summable even Suzuki source factor equals the constructed
Jurkat--Richert lower function on the bounded source domain. -/
theorem suzukiContinuousLowerFactor_eq_jr1965f_bounded
    {s : ℝ} (hs : 2 ≤ s) (hs10 : s ≤ 10) :
    suzukiContinuousLowerFactor s = jr1965f s :=
  (bounded_source_factors_steps 7 le_rfl).2 s hs (by norm_num; exact hs10)

end Wu2008DoubleSieve
