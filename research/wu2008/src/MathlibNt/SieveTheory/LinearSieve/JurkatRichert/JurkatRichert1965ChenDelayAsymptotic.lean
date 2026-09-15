import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenDelayDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePairingConservation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiStandardUpperAdjointDDE
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEinEulerTailAsymptotic

/-!
# Jurkat--Richert (5.10) for the constructed global delay functions

The common limit is `1`: pair the actual sum `F + f` with the independently
constructed Laplace adjoint. The conserved pairing is `2` at the initial
endpoint and twice the common limit at infinity.

This is a modern adjoint proof of the exact statement on printed p. 226,
not the original paper's appeal to de Bruijn's estimates (5.3). Only the generic
pairing identity and unconditional adjoint producers are reused; no Suzuki
source-tail or amplitude-normalization hypothesis is consumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def jr1965DelaySum (u : ℝ) : ℝ := jr1965F u + jr1965f u

theorem continuousOn_jr1965DelaySum :
    ContinuousOn jr1965DelaySum (Ici 1) :=
  (continuousOn_jr1965F.add continuousOn_jr1965f).mono
    (fun u hu => by
      change 0 < u
      have hu' : 1 ≤ u := hu
      linarith)

theorem jr1965DelaySum_initial {u : ℝ} (hu : u ≤ 2) :
    jr1965DelaySum u = jr1965DelayConstant / u := by
  simp only [jr1965DelaySum, jr1965F_initial hu, jr1965f_initial hu,
    add_zero, jr1965DelayConstant]

theorem jr1965DelaySum_integral_recurrence (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    b * jr1965DelaySum b - a * jr1965DelaySum a =
      ∫ t in a..b, jr1965DelaySum (t - 1) := by
  have hshift : MapsTo (fun t : ℝ => t - 1) (uIcc a b) (Ioi 0) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    change 0 < t - 1
    linarith only [ha, ht.1]
  have hiF : IntervalIntegrable (fun t => jr1965F (t - 1)) volume a b :=
    (continuousOn_jr1965F.comp
      (continuousOn_id.sub continuousOn_const) hshift).intervalIntegrable
  have hif : IntervalIntegrable (fun t => jr1965f (t - 1)) volume a b :=
    (continuousOn_jr1965f.comp
      (continuousOn_id.sub continuousOn_const) hshift).intervalIntegrable
  simp only [jr1965DelaySum, intervalIntegral.integral_add hiF hif]
  linarith [jr1965F_integral_recurrence ha hab, jr1965f_integral_recurrence ha hab]

theorem norm_jr1965DelaySum_le {u : ℝ} (hu : 1 ≤ u) :
    ‖jr1965DelaySum u‖ ≤ 2 * jr1965DelayConstant := by
  unfold jr1965DelaySum
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
    (jr1965F_pos (by linarith : 0 < u)).le (jr1965f_nonneg (by linarith : 0 < u)))]
  linarith [jr1965F_le_delayConstant hu, jr1965f_le_delayConstant hu]

theorem jr1965DelaySum_adjoint_pairing_two :
    upperSourcePairingFor jr1965DelaySum suzukiStandardUpperAdjoint 2 = 2 := by
  have hpos : ∀ t ∈ uIcc (1 : ℝ) 2, 0 < t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    linarith only [ht.1]
  have hpcont : ContinuousOn suzukiStandardUpperAdjoint (Ioi 0) :=
    fun _ hs => (suzukiStandardUpperAdjoint_hasDerivAt_dde hs).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable
      (fun t => suzukiStandardUpperAdjoint (t + 1) / t) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply hpcont.comp (continuousOn_id.add continuousOn_const)
      intro t ht
      exact add_pos (hpos t ht) zero_lt_one
    · exact continuousOn_id
    · intro t ht
      exact (hpos t ht).ne'
  have heval := integral_upperAdjoint_shift_div_eq_sub
    (p := suzukiStandardUpperAdjoint)
    (fun t ht => suzukiStandardUpperAdjoint_hasDerivAt_dde (hpos t ht)) hint
  have hi :
      (∫ t in (1 : ℝ)..2, suzukiStandardUpperAdjoint (t + 1) * jr1965DelaySum t) =
        jr1965DelayConstant * (suzukiStandardUpperAdjoint 1 -
          suzukiStandardUpperAdjoint 2) := by
    rw [← heval, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    dsimp only
    rw [jr1965DelaySum_initial ht.2]
    ring
  unfold upperSourcePairingFor
  rw [show (2 : ℝ) - 1 = 1 by norm_num, hi, jr1965DelaySum_initial le_rfl]
  calc
    _ = jr1965DelayConstant * suzukiStandardUpperAdjoint 1 := by ring
    _ = 2 := by
      rw [suzukiStandardUpperAdjoint_one_eq_exp_neg_eulerMascheroni_unconditional,
        jr1965DelayConstant, mul_assoc, ← Real.exp_add]
      simp

/-- The generic conservation theorem instantiated on the actual JR functions. -/
theorem jr1965DelaySum_adjoint_pairing_eq_two {u : ℝ} (hu : 2 ≤ u) :
    upperSourcePairingFor jr1965DelaySum suzukiStandardUpperAdjoint u = 2 := by
  rw [upperSourcePairing_eq_of_integralDDE continuousOn_jr1965DelaySum
    jr1965DelaySum_integral_recurrence
    (fun s hs => suzukiStandardUpperAdjoint_hasDerivAt_dde (by linarith))
    (x := 2) le_rfl hu]
  exact jr1965DelaySum_adjoint_pairing_two

theorem tendsto_jr1965DelaySum_adjoint_window :
    Tendsto (fun s : ℝ => ∫ t in (s - 1)..s,
      suzukiStandardUpperAdjoint (t + 1) * jr1965DelaySum t) atTop (𝓝 0) := by
  have hp := suzukiStandardUpperAdjoint_scaledTail
  unfold SuzukiStandardUpperAdjointScaledTail at hp
  rw [Metric.tendsto_atTop] at hp ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hp 1 zero_lt_one
  let A := jr1965DelayConstant
  have hA : 0 < A := by dsimp [A, jr1965DelayConstant]; positivity
  refine ⟨max N (max 2 ((4 * A + 1) / ε)), ?_⟩
  intro s hs
  have hsN : N ≤ s := (le_max_left _ _).trans hs
  have hs2 : 2 ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hse : (4 * A + 1) / ε ≤ s :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hspos : 0 < s := by linarith
  rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
  apply lt_of_le_of_lt
    (intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * A / s) ?_)
  · rw [show |s - (s - 1)| = 1 by
      rw [show s - (s - 1) = 1 by ring]
      norm_num, mul_one]
    apply (div_lt_iff₀ hspos).2
    have h := (div_le_iff₀ hε).1 hse
    nlinarith
  · intro t ht
    rw [uIoc_of_le (by linarith : s - 1 ≤ s)] at ht
    have htS : s ≤ t + 1 := by linarith [ht.1]
    have htpos : 0 < t + 1 := hspos.trans_le htS
    have hpb := hN (t + 1) (hsN.trans htS)
    have hqnorm : ‖(t + 1) * suzukiStandardUpperAdjoint (t + 1)‖ ≤ 2 := by
      rw [Real.dist_eq, abs_sub_lt_iff] at hpb
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hpb.1, hpb.2]
    have hPnorm := norm_jr1965DelaySum_le (u := t) (by linarith [ht.1])
    rw [show suzukiStandardUpperAdjoint (t + 1) =
        ((t + 1) * suzukiStandardUpperAdjoint (t + 1)) / (t + 1) by field_simp]
    rw [norm_mul, norm_div, Real.norm_eq_abs (t + 1), abs_of_pos htpos]
    calc
      _ ≤ 2 / (t + 1) * (2 * A) := by gcongr
      _ ≤ 2 / s * (2 * A) := by gcongr
      _ = 4 * A / s := by ring

/-- The initial amplitude `2 exp gamma` gives common limit `1`, proved by an
independent adjoint identity rather than supplied as an asymptotic premise. -/
theorem jr1965CommonLimit_eq_one : jr1965CommonLimit = 1 := by
  have hP : Tendsto jr1965DelaySum atTop (𝓝 (2 * jr1965CommonLimit)) := by
    unfold jr1965DelaySum
    simpa only [two_mul] using
      tendsto_jr1965F_commonLimit.add tendsto_jr1965f_commonLimit
  have hp := suzukiStandardUpperAdjoint_scaledTail
  unfold SuzukiStandardUpperAdjointScaledTail at hp
  have hpair : Tendsto
      (upperSourcePairingFor jr1965DelaySum suzukiStandardUpperAdjoint)
      atTop (𝓝 (2 * jr1965CommonLimit)) := by
    unfold upperSourcePairingFor
    simpa only [one_mul, add_zero] using
      (hp.mul hP).add tendsto_jr1965DelaySum_adjoint_window
  have hconst : Tendsto
      (upperSourcePairingFor jr1965DelaySum suzukiStandardUpperAdjoint)
      atTop (𝓝 2) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
    exact (jr1965DelaySum_adjoint_pairing_eq_two hu).symm
  have := tendsto_nhds_unique hpair hconst
  linarith

theorem jr1965f_le_one {u : ℝ} (hu : 1 ≤ u) : jr1965f u ≤ 1 := by
  simpa only [jr1965CommonLimit_eq_one] using jr1965f_le_commonLimit hu

theorem one_le_jr1965F {u : ℝ} (hu : 1 ≤ u) : 1 ≤ jr1965F u := by
  simpa only [jr1965CommonLimit_eq_one] using commonLimit_le_jr1965F hu

theorem abs_jr1965F_sub_one_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965F u - 1| ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  simpa only [jr1965CommonLimit_eq_one] using abs_jr1965F_sub_commonLimit_le_exp hu

theorem abs_jr1965f_sub_one_le_exp {u : ℝ} (hu : 1 ≤ u) :
    |jr1965f u - 1| ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  simpa only [jr1965CommonLimit_eq_one] using abs_jr1965f_sub_commonLimit_le_exp hu

/-- Literal quantified (5.10): one positive constant, both functions, all `u >= 1`. -/
theorem exists_jr1965_delay_asymptotic :
    ∃ A > 0, ∀ u : ℝ, 1 ≤ u →
      |jr1965F u - 1| ≤ A * Real.exp (-u) ∧
      |jr1965f u - 1| ≤ A * Real.exp (-u) :=
  ⟨jr1965DelayConstant * Real.exp 2, by unfold jr1965DelayConstant; positivity,
    fun _ hu => ⟨abs_jr1965F_sub_one_le_exp hu, abs_jr1965f_sub_one_le_exp hu⟩⟩

theorem abs_jr1965g_sub_one_le_exp (ν : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |jr1965g ν u - 1| ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-u) := by
  unfold jr1965g
  split_ifs
  · exact abs_jr1965F_sub_one_le_exp hu
  · exact abs_jr1965f_sub_one_le_exp hu

theorem tendsto_jr1965F_one : Tendsto jr1965F atTop (𝓝 1) := by
  simpa only [jr1965CommonLimit_eq_one] using tendsto_jr1965F_commonLimit

theorem tendsto_jr1965f_one : Tendsto jr1965f atTop (𝓝 1) := by
  simpa only [jr1965CommonLimit_eq_one] using tendsto_jr1965f_commonLimit

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
