import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965ChenDelayAsymptotic
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized

/-!
# The actual dimension-one Section 13 hat functions

The positive extensions of `-F' / (2 exp γ)` and `f' / (2 exp γ)` give
Suzuki's two hat functions. Their source contract is derived from the
constructed Jurkat--Richert delay solution, not assumed.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

open SwitchingPrinciple.SuzukiLemma144KappaOne

private theorem delayConstant_pos : 0 < jr1965DelayConstant := by
  unfold jr1965DelayConstant
  positivity

/-- Positive extension of the normalized negative upper derivative. -/
def jr1965HatPlus (s : ℝ) : ℝ :=
  if s ≤ 3 then 1 / s ^ 2
  else (jr1965F s - jr1965f (s - 1)) / (jr1965DelayConstant * s)

/-- Positive extension of the normalized lower derivative, including its right
derivative at the initial endpoint. -/
def jr1965HatMinus (s : ℝ) : ℝ :=
  if s ≤ 2 then 2 / s ^ 2
  else (jr1965F (s - 1) - jr1965f s) / (jr1965DelayConstant * s)

/-- The actual Section 13 data, with `β̂ = 2`. -/
def jr1965Section13HatLayers : Section13HatLayers where
  betaHat := 2
  Tplus := jr1965HatPlus
  Tminus := jr1965HatMinus

theorem jr1965HatPlus_eq {s : ℝ} (hs : 1 < s) :
    jr1965HatPlus s =
      (jr1965F s - jr1965f (s - 1)) / (jr1965DelayConstant * s) := by
  unfold jr1965HatPlus
  split_ifs with h
  · rw [jr1965F_eq_of_le_three h, jr1965f_initial (by linarith)]
    change 1 / s ^ 2 =
      (jr1965DelayConstant / s - 0) / (jr1965DelayConstant * s)
    field_simp [ne_of_gt delayConstant_pos, ne_of_gt (show 0 < s by linarith)]
    ring
  · rfl

theorem jr1965HatMinus_eq {s : ℝ} (hs : 2 ≤ s) :
    jr1965HatMinus s =
      (jr1965F (s - 1) - jr1965f s) / (jr1965DelayConstant * s) := by
  unfold jr1965HatMinus
  split_ifs with h
  · have he : s = 2 := le_antisymm h hs
    subst s
    rw [jr1965f_initial (by norm_num), jr1965F_eq_of_le_three (by norm_num)]
    change 2 / (2 : ℝ) ^ 2 =
      (jr1965DelayConstant / (2 - 1) - 0) / (jr1965DelayConstant * 2)
    field_simp [ne_of_gt delayConstant_pos]
    ring
  · rfl

theorem jr1965HatPlus_pos {s : ℝ} (hs : 0 < s) : 0 < jr1965HatPlus s := by
  unfold jr1965HatPlus
  split_ifs with h
  · positivity
  · exact div_pos (sub_pos.mpr (jr1965f_sub_one_lt_jr1965F (by linarith)))
      (mul_pos delayConstant_pos hs)

theorem jr1965HatMinus_pos {s : ℝ} (hs : 0 < s) : 0 < jr1965HatMinus s := by
  unfold jr1965HatMinus
  split_ifs with h
  · positivity
  · apply div_pos _ (mul_pos delayConstant_pos hs)
    exact sub_pos.mpr ((jr1965f_lt_jr1965F hs).trans_le
      (antitoneOn_jr1965F (by change 0 < s - 1; linarith) hs (by linarith)))

private theorem continuousOn_hat_piecewise {b c : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici b)) (he : c / b ^ 2 = g b) :
    ContinuousOn (fun s : ℝ => if s ≤ b then c / s ^ 2 else g s) (Ioi 0) := by
  apply ContinuousOn.if
  · intro x hx
    have hxb : x = b := by
      have : x ∈ frontier (Iic b) := hx.2
      simpa only [frontier_Iic, mem_singleton_iff] using this
    simpa [hxb] using he
  · exact (continuousOn_const.div (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt hx))).mono inter_subset_left
  · apply hg.mono
    intro x hx
    have : x ∈ closure (Ioi b) := by
      convert hx.2 using 2
      ext a
      simp
    simpa only [closure_Ioi, mem_Ici] using this

theorem continuousOn_jr1965HatPlus : ContinuousOn jr1965HatPlus (Ioi 0) := by
  apply continuousOn_hat_piecewise
  · apply ContinuousOn.div
    · apply (continuousOn_jr1965F.mono (fun x hx => by
        change 0 < x; change 3 ≤ x at hx; linarith)).sub
      exact continuousOn_jr1965f.comp (continuousOn_id.sub continuousOn_const)
        (fun x hx => by change 0 < x - 1; change 3 ≤ x at hx; linarith)
    · exact continuousOn_const.mul continuousOn_id
    · intro x hx
      exact mul_ne_zero (ne_of_gt delayConstant_pos) (by
        change 3 ≤ x at hx; linarith)
  · rw [jr1965F_eq_of_le_three (by norm_num), jr1965f_initial (by norm_num)]
    change 1 / (3 : ℝ) ^ 2 =
      (jr1965DelayConstant / 3 - 0) / (jr1965DelayConstant * 3)
    field_simp [ne_of_gt delayConstant_pos]
    ring

theorem continuousOn_jr1965HatMinus : ContinuousOn jr1965HatMinus (Ioi 0) := by
  apply continuousOn_hat_piecewise
  · apply ContinuousOn.div
    · apply ContinuousOn.sub
      · exact continuousOn_jr1965F.comp (continuousOn_id.sub continuousOn_const)
          (fun x hx => by change 0 < x - 1; change 2 ≤ x at hx; linarith)
      · exact continuousOn_jr1965f.mono (fun x hx => by
          change 0 < x; change 2 ≤ x at hx; linarith)
    · exact continuousOn_const.mul continuousOn_id
    · intro x hx
      exact mul_ne_zero (ne_of_gt delayConstant_pos) (by
        change 2 ≤ x at hx; linarith)
  · rw [jr1965F_eq_of_le_three (by norm_num), jr1965f_initial (by norm_num)]
    change 2 / (2 : ℝ) ^ 2 =
      (jr1965DelayConstant / (2 - 1) - 0) / (jr1965DelayConstant * 2)
    field_simp [ne_of_gt delayConstant_pos]
    ring

theorem hasDerivAt_jr1965F_hat {s : ℝ} (hs : 0 < s) :
    HasDerivAt jr1965F (-jr1965DelayConstant * jr1965HatPlus s) s := by
  by_cases h : 2 < s
  · rw [jr1965HatPlus_eq (by linarith)]
    apply (hasDerivAt_jr1965F h).congr_deriv
    field_simp [ne_of_gt delayConstant_pos, ne_of_gt hs]
    ring
  · have hd := (hasDerivAt_const s jr1965DelayConstant).div
      (hasDerivAt_id s) (ne_of_gt hs)
    have he : jr1965F =ᶠ[𝓝 s] (fun x : ℝ => jr1965DelayConstant / x) := by
      filter_upwards [eventually_lt_nhds (show s < 3 by linarith)] with x hx
      exact jr1965F_eq_of_le_three hx.le
    apply (hd.congr_of_eventuallyEq he).congr_deriv
    simp only [jr1965HatPlus, if_pos (show s ≤ 3 by linarith), id_eq]
    ring

theorem hasDerivAt_jr1965f_hat {s : ℝ} (hs : 2 < s) :
    HasDerivAt jr1965f (jr1965DelayConstant * jr1965HatMinus s) s := by
  rw [jr1965HatMinus_eq hs.le]
  apply (hasDerivAt_jr1965f hs).congr_deriv
  field_simp [ne_of_gt delayConstant_pos, ne_of_gt (show 0 < s by linarith)]

theorem hasDerivAt_weighted_jr1965HatPlus {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun x => x ^ 2 * jr1965HatPlus x)
      (-s * jr1965HatMinus (s - 1)) s := by
  have hdF := hasDerivAt_mul_jr1965F (show 2 < s by linarith)
  have hdf := (hasDerivAt_jr1965f_hat (show 2 < s - 1 by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hd := (hdF.sub ((hasDerivAt_id s).mul hdf)).div_const jr1965DelayConstant
  have he : (fun x => x ^ 2 * jr1965HatPlus x) =ᶠ[𝓝 s]
      (fun x => (x * jr1965F x - x * jr1965f (x - 1)) / jr1965DelayConstant) := by
    filter_upwards [eventually_gt_nhds (show 1 < s by linarith)] with x hx
    rw [jr1965HatPlus_eq hx]
    field_simp [ne_of_gt delayConstant_pos, ne_of_gt (show 0 < x by linarith)]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp
  field_simp [ne_of_gt delayConstant_pos]
  ring

theorem hasDerivAt_weighted_jr1965HatMinus {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x ^ 2 * jr1965HatMinus x)
      (-s * jr1965HatPlus (s - 1)) s := by
  have hdF := (hasDerivAt_jr1965F_hat (show 0 < s - 1 by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  have hdf := hasDerivAt_mul_jr1965f hs
  have hd := (((hasDerivAt_id s).mul hdF).sub hdf).div_const jr1965DelayConstant
  have he : (fun x => x ^ 2 * jr1965HatMinus x) =ᶠ[𝓝 s]
      (fun x => (x * jr1965F (x - 1) - x * jr1965f x) / jr1965DelayConstant) := by
    filter_upwards [eventually_gt_nhds hs] with x hx
    rw [jr1965HatMinus_eq hx.le]
    field_simp [ne_of_gt delayConstant_pos, ne_of_gt (show 0 < x by linarith)]
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  dsimp
  field_simp [ne_of_gt delayConstant_pos]
  ring

private theorem abs_delay_sub_shift_le {g h : ℝ → ℝ}
    (hg : ∀ u, 1 ≤ u →
      |g u - 1| ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-u))
    (hh : ∀ u, 1 ≤ u →
      |h u - 1| ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-u))
    {s : ℝ} (hs : 2 ≤ s) :
    |g s - h (s - 1)| ≤
      jr1965DelayConstant * (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by
  calc
    |g s - h (s - 1)| = |(g s - 1) - (h (s - 1) - 1)| := by congr 1; ring
    _ ≤ |g s - 1| + |h (s - 1) - 1| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (g s - 1) 0 (h (s - 1) - 1))
    _ ≤ jr1965DelayConstant * Real.exp 2 * Real.exp (-s) +
        jr1965DelayConstant * Real.exp 2 * Real.exp (-(s - 1)) :=
      add_le_add (hg s (by linarith)) (hh (s - 1) (by linarith))
    _ = _ := by
      rw [show -(s - 1) = -s + 1 by ring, Real.exp_add]
      ring

private theorem div_delay_exp_bound {n s : ℝ} (hs : 2 ≤ s)
    (hn : |n| ≤ jr1965DelayConstant *
      (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s)) :
    |n / (jr1965DelayConstant * s)| ≤
      (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by
  have hC : 0 ≤ (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by positivity
  rw [abs_div, abs_of_pos (mul_pos delayConstant_pos (by linarith))]
  apply (div_le_iff₀ (mul_pos delayConstant_pos (by linarith))).2
  calc
    |n| ≤ jr1965DelayConstant * ((Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s)) :=
      hn.trans_eq (by ring)
    _ ≤ (jr1965DelayConstant * ((Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s))) *
        s := le_mul_of_one_le_right (mul_nonneg delayConstant_pos.le hC) (by linarith)
    _ = _ := by ring

theorem abs_jr1965HatPlus_le_exp {s : ℝ} (hs : 2 ≤ s) :
    |jr1965HatPlus s| ≤ (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by
  rw [jr1965HatPlus_eq (by linarith)]
  exact div_delay_exp_bound hs (abs_delay_sub_shift_le
    (fun _ hu => abs_jr1965F_sub_one_le_exp hu)
    (fun _ hu => abs_jr1965f_sub_one_le_exp hu) hs)

theorem abs_jr1965HatMinus_le_exp {s : ℝ} (hs : 2 ≤ s) :
    |jr1965HatMinus s| ≤ (Real.exp 2 * (1 + Real.exp 1)) * Real.exp (-s) := by
  rw [jr1965HatMinus_eq hs]
  apply div_delay_exp_bound hs
  rw [abs_sub_comm]
  exact abs_delay_sub_shift_le
    (fun _ hu => abs_jr1965f_sub_one_le_exp hu)
    (fun _ hu => abs_jr1965F_sub_one_le_exp hu) hs

theorem jr1965Section13HatLayers_exponentialDecay :
    Section13HatExponentialDecay jr1965Section13HatLayers := by
  intro sign
  refine ⟨Real.exp 2 * (1 + Real.exp 1), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  cases sign
  · exact abs_jr1965HatPlus_le_exp hs
  · exact abs_jr1965HatMinus_le_exp hs

theorem tendsto_weighted_jr1965Section13HatLayers (sign : ErrorSign) :
    Tendsto (weightedHat jr1965Section13HatLayers sign) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := jr1965Section13HatLayers_exponentialDecay sign
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hC] with s hs
  rw [Real.norm_eq_abs, weightedHat, abs_mul, abs_of_nonneg (sq_nonneg s)]
  calc
    s ^ 2 * |jr1965Section13HatLayers.T sign s| ≤
        s ^ 2 * (C * Real.exp (-s)) := mul_le_mul_of_nonneg_left hs (sq_nonneg s)
    _ = C * (s ^ 2 * Real.exp (-s)) := by ring

/-- Unconditional witness of all of Suzuki's source requirements (T1)--(T5). -/
theorem jr1965Section13HatSourceContract :
    Section13HatSourceContract jr1965Section13HatLayers where
  betaHat_eq := rfl
  beta_gt_one := by norm_num
  continuous := by
    intro sign
    cases sign
    · exact continuousOn_jr1965HatPlus
    · exact continuousOn_jr1965HatMinus
  positive := by
    intro sign s hs
    cases sign
    · exact jr1965HatPlus_pos hs
    · exact jr1965HatMinus_pos hs
  initial_plus := by
    intro s hs hs3
    change s ^ 2 * jr1965HatPlus s = 2 - 1
    rw [jr1965HatPlus, if_pos (show s ≤ 3 by linarith)]
    field_simp
    norm_num
  initial_minus := by
    intro s hs hs2
    change s ^ 2 * jr1965HatMinus s = 2
    rw [jr1965HatMinus, if_pos hs2]
    field_simp
  dde := by
    intro sign s hs
    cases sign
    · exact hasDerivAt_weighted_jr1965HatPlus (by norm_num [ErrorSign.epsilon] at hs ⊢; exact hs)
    · exact hasDerivAt_weighted_jr1965HatMinus (by simpa [ErrorSign.epsilon] using hs)
  weighted_tendsto_zero := tendsto_weighted_jr1965Section13HatLayers
  t5 := jr1965Section13HatLayers_exponentialDecay

end MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
