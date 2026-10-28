import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorObjects
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Suzuki §13 hat layers at sieve dimension one

This file records the literal κ=1 specialization of (13.1)--(13.7), rather than
inventing a finite parity sum for `T̂⁺,T̂⁻`.  In this branch `κ̂=κ=1` and
`β̂=β`; the weighted functions are `s² T̂±(s)`.

Suzuki defines the hat layers as solutions of a delay differential equation
with initial data and exponential decay.  Section 13 does *not* define finite
partial sums for them.  The finite-level results below mean results on a compact
interval `[a,b]`; the only limit input needed to turn the DDE into the tail
integral (13.12)/(13.14) is decay at infinity.
-/

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The weighted Section 13 unknown `s^(κ̂+1) T̂±(s)` at κ=1. -/
def weightedHat (H : Section13HatLayers) (sign : ErrorSign) (s : ℝ) : ℝ :=
  s ^ 2 * H.T sign s

/-- Literal κ=1 data from Suzuki (T1)--(T5), (13.2), and (13.7).
The derivative equation is (T3); `weighted_tendsto_zero` is the only limiting
input and follows in the paper from (T5). -/
structure Section13HatContract (H : Section13HatLayers) (β : ℝ) : Prop where
  betaHat_eq : H.betaHat = β
  beta_gt_one : 1 < β
  continuous : ∀ sign, ContinuousOn (H.T sign) (Ioi 0)
  positive : ∀ sign s, 0 < s → 0 < H.T sign s
  initial_plus : ∀ s, 0 < s → s ≤ β + 1 → weightedHat H .plus s = β - 1
  initial_minus : ∀ s, 0 < s → s ≤ β → weightedHat H .minus s = β
  dde : ∀ sign s, β + sign.epsilon < s →
    HasDerivAt (weightedHat H sign) (-s * H.T sign.opposite (s - 1)) s
  weighted_tendsto_zero : ∀ sign,
    Tendsto (weightedHat H sign) atTop (𝓝 0)


@[simp] theorem lambda_eq_perturb_mul_weightedHat
    (H : Section13HatLayers) (sign : ErrorSign) (D d ε t : ℝ) :
    lambda H sign D d ε t =
      (1 + (t + ε) ^ d / Real.log D) ^ t * weightedHat H sign t := by
  norm_num [lambda, weightedHat, Section13HatLayers.kappaHat]
  ac_rfl


/-- Multiplying two nonnegative antitone functions preserves antitonicity on a
fixed set.  This is the algebraic engine in the high-range part of Claim
14.6(ii), after (14.15). -/
theorem AntitoneOn.mul_nonneg_on {f g : ℝ → ℝ} {S : Set ℝ}
    (hf : AntitoneOn f S) (hg : AntitoneOn g S)
    (hf0 : ∀ x ∈ S, 0 ≤ f x) (hg0 : ∀ x ∈ S, 0 ≤ g x) :
    AntitoneOn (fun x => f x * g x) S := by
  intro x hx y hy hxy
  exact mul_le_mul (hf hx hy hxy) (hg hx hy hxy) (hg0 y hy) (hf0 x hx)

/-- The elementary ratio factor in (14.15) is antitone on `(1,∞)` whenever
`1+Δ ≥ 0`. -/
theorem ratio_rpow_antitoneOn_Ioi {Δ : ℝ} (hΔ : -1 ≤ Δ) :
    AntitoneOn (fun t : ℝ => (t / (t - 1)) ^ (1 + Δ)) (Ioi 1) := by
  intro x hx y hy hxy
  have hxm : 0 < x - 1 := sub_pos.mpr hx
  have hym : 0 < y - 1 := sub_pos.mpr hy
  have hratio : y / (y - 1) ≤ x / (x - 1) := by
    rw [div_le_div_iff₀ hym hxm]
    nlinarith
  exact Real.rpow_le_rpow
    (div_nonneg (zero_lt_one.trans hy).le (sub_nonneg.mpr hy.le)) hratio (by linarith)

/-- A source-neutral high-range form of Claim 14.6(ii).  It makes explicit that
(14.15) reduces the claim to antitonicity of the shifted `Λ₁` factor and of the
ratio power.  Suzuki treats the short remaining interval separately using
(T4); it is not a consequence of Claim 14.6(i) alone. -/
theorem qD_mul_antitoneOn_of_factors
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ : ℝ) {S : Set ℝ}
    (hLambda : AntitoneOn (fun t => lambda H sign.opposite D d 1 (t - 1)) S)
    (hRatio : AntitoneOn (fun t : ℝ => (t / (t - 1)) ^ (1 + Δ)) S)
    (hLambda0 : ∀ t ∈ S, 0 ≤ lambda H sign.opposite D d 1 (t - 1))
    (hRatio0 : ∀ t ∈ S, 0 ≤ (t / (t - 1)) ^ (1 + Δ))
    (hgt1 : ∀ t ∈ S, 1 < t) :
    AntitoneOn (fun t => qD H sign.opposite D d Δ t * t) S := by
  intro x hx y hy hxy
  change qD H sign.opposite D d Δ y * y ≤ qD H sign.opposite D d Δ x * x
  rw [← equation14_15 H sign.opposite D d Δ x (hgt1 x hx),
      ← equation14_15 H sign.opposite D d Δ y (hgt1 y hy)]
  exact AntitoneOn.mul_nonneg_on hLambda hRatio hLambda0 hRatio0 hx hy hxy

/-- High-range Claim 14.6(ii) with the ratio monotonicity discharged.  The only
remaining analytic input is decrease of the shifted `Λ₁` factor. -/
theorem qD_mul_antitoneOn_of_shifted_lambda
    (H : Section13HatLayers) (sign : ErrorSign) (D d Δ : ℝ) {S : Set ℝ}
    (hΔ : -1 ≤ Δ) (hS : S ⊆ Ioi (1 : ℝ))
    (hLambda : AntitoneOn (fun t => lambda H sign.opposite D d 1 (t - 1)) S)
    (hLambda0 : ∀ t ∈ S, 0 ≤ lambda H sign.opposite D d 1 (t - 1)) :
    AntitoneOn (fun t => qD H sign.opposite D d Δ t * t) S := by
  apply qD_mul_antitoneOn_of_factors H sign D d Δ hLambda
  · exact (ratio_rpow_antitoneOn_Ioi hΔ).mono hS
  · exact hLambda0
  · intro t ht
    exact Real.rpow_nonneg
      (div_nonneg (zero_lt_one.trans (hS ht)).le (sub_nonneg.mpr (hS ht).le)) _
  · exact fun t ht => hS ht


/-- The delayed positive integrand in the κ=1 Section 13 DDE. -/
def hatTailIntegrand (H : Section13HatLayers) (sign : ErrorSign) (t : ℝ) : ℝ :=
  t * H.T sign.opposite (t - 1)


/-- The delayed DDE integrand is integrable on every tail beyond the threshold. -/
theorem integrableOn_hatTailIntegrand_Ioi
    {H : Section13HatLayers} {β a : ℝ} (hH : Section13HatContract H β)
    (sign : ErrorSign) (ha : β + sign.epsilon < a) :
    IntegrableOn (hatTailIntegrand H sign) (Ioi a) := by
  let f : ℝ → ℝ := weightedHat H sign
  let f' : ℝ → ℝ := fun t => -hatTailIntegrand H sign t
  have hcont : ContinuousWithinAt f (Ici a) a :=
    (hH.dde sign a ha).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x := by
    intro x hx
    simpa [f, f', hatTailIntegrand, neg_mul] using hH.dde sign x (ha.trans hx)
  have hnonpos : ∀ x ∈ Ioi a, f' x ≤ 0 := by
    intro x hx
    have hx1 : 1 < x := by
      have hβ : 1 < β := hH.beta_gt_one
      have hax : a < x := hx
      cases sign <;> simp [ErrorSign.epsilon] at ha <;> linarith
    dsimp only [f', hatTailIntegrand]
    exact neg_nonpos.mpr (mul_nonneg (zero_le_one.trans hx1.le)
      (le_of_lt (hH.positive sign.opposite (x - 1) (sub_pos.mpr hx1))))
  have hi : IntegrableOn f' (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hnonpos
      (by simpa only [f] using hH.weighted_tendsto_zero sign)
  have hineg := hi.neg
  change IntegrableOn (fun t => -f' t) (Ioi a) at hineg
  dsimp only [f'] at hineg
  simpa only [neg_neg] using hineg

/-- κ=1 tail identity obtained by integrating the Section 13 DDE to infinity. -/
theorem integral_Ioi_hatTailIntegrand
    {H : Section13HatLayers} {β a : ℝ} (hH : Section13HatContract H β)
    (sign : ErrorSign) (ha : β + sign.epsilon < a) :
    (∫ t in Ioi a, hatTailIntegrand H sign t) = weightedHat H sign a := by
  let f : ℝ → ℝ := weightedHat H sign
  let f' : ℝ → ℝ := fun t => -hatTailIntegrand H sign t
  have hcont : ContinuousWithinAt f (Ici a) a :=
    (hH.dde sign a ha).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x := by
    intro x hx
    simpa [f, f', hatTailIntegrand, neg_mul] using hH.dde sign x (ha.trans hx)
  have hnonpos : ∀ x ∈ Ioi a, f' x ≤ 0 := by
    intro x hx
    have hx1 : 1 < x := by
      have hβ : 1 < β := hH.beta_gt_one
      have hax : a < x := hx
      cases sign <;> simp [ErrorSign.epsilon] at ha <;> linarith
    dsimp only [f', hatTailIntegrand]
    exact neg_nonpos.mpr (mul_nonneg (zero_le_one.trans hx1.le)
      (le_of_lt (hH.positive sign.opposite (x - 1) (sub_pos.mpr hx1))))
  have h := integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hnonpos
    (by simpa only [f] using hH.weighted_tendsto_zero sign)
  simpa only [f', MeasureTheory.integral_neg, zero_sub, neg_inj] using h


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
