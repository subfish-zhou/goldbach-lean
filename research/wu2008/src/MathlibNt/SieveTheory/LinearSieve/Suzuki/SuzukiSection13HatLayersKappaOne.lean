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

@[simp] theorem kappaHat_eq_one (H : Section13HatLayers) : H.kappaHat = 1 := rfl

@[simp] theorem lambda_eq_perturb_mul_weightedHat
    (H : Section13HatLayers) (sign : ErrorSign) (D d ε t : ℝ) :
    lambda H sign D d ε t =
      (1 + (t + ε) ^ d / Real.log D) ^ t * weightedHat H sign t := by
  norm_num [lambda, weightedHat, Section13HatLayers.kappaHat]
  ac_rfl

/-- On every finite interval strictly beyond the delay threshold, (T3) and
positivity already imply that `s² T̂±(s)` is antitone.  No limiting theorem is
used here. -/
theorem weightedHat_antitoneOn_Icc
    {H : Section13HatLayers} {β a b : ℝ} (hH : Section13HatContract H β)
    (sign : ErrorSign) (ha : β + sign.epsilon < a) :
    AntitoneOn (weightedHat H sign) (Icc a b) := by
  have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
  have hthreshold : 0 < β + sign.epsilon := by linarith [hH.beta_gt_one]
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact (continuousOn_id.pow 2).mul (hH.continuous sign) |>.mono (by
      intro x hx
      exact hthreshold.trans (ha.trans_le hx.1))
  · intro x hx
    have hx' : x ∈ Icc a b := interior_subset hx
    exact (hH.dde sign x (ha.trans_le hx'.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc a b := interior_subset hx
    rw [(hH.dde sign x (ha.trans_le hx'.1)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (le_of_lt (hthreshold.trans (ha.trans_le hx'.1))))
      (le_of_lt (hH.positive sign.opposite (x - 1) (by
        linarith [hH.beta_gt_one, ha.trans_le hx'.1])))

/-- A finite-interval product criterion isolating exactly the local estimate
needed in Claim 14.6(i).  This is the rigorous content of the step from
(14.16)+(T3) to a decreasing `Λ`: once the displayed derivative is nonpositive,
ordinary one-variable calculus supplies antitonicity. -/
theorem lambda_antitoneOn_Icc_of_deriv_nonpos
    (H : Section13HatLayers) (sign : ErrorSign) (D d ε a b : ℝ)
    (hcont : ContinuousOn (lambda H sign D d ε) (Icc a b))
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun x => lambda H sign D d ε x) t)
    (hderiv : ∀ t ∈ Ioo a b, deriv (lambda H sign D d ε) t ≤ 0) :
    AntitoneOn (lambda H sign D d ε) (Icc a b) := by
  exact antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
    (fun t ht => (hdiff t (by simpa only [interior_Icc] using ht)).differentiableWithinAt)
    (fun t ht => hderiv t (by simpa only [interior_Icc] using ht))

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

/-- Pointwise convergence preserves antitonicity.  Thus any genuine finite
construction of the Section 13 solutions needs only pointwise convergence to
pass weighted monotonicity to the limit; uniform convergence is required only
for continuity/differentiation, not for this order statement. -/
theorem antitoneOn_of_pointwise_limit
    {u : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {S : Set ℝ}
    (hu : ∀ n, AntitoneOn (u n) S)
    (hlim : ∀ x ∈ S, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    AntitoneOn f S := by
  intro x hx y hy hxy
  exact le_of_tendsto_of_tendsto (hlim y hy) (hlim x hx)
    (Filter.Eventually.of_forall (fun n => hu n hx hy hxy))

/-- Exact separation of finite and limiting obligations for Claim 14.6(i). -/
structure Claim14_6FiniteApproximation
    (H : Section13HatLayers) (sign : ErrorSign) (D d ε a b : ℝ) where
  approx : ℕ → ℝ → ℝ
  antitone : ∀ n, AntitoneOn (approx n) (Icc a b)
  pointwise : ∀ x ∈ Icc a b,
    Tendsto (fun n => approx n x) atTop (𝓝 (lambda H sign D d ε x))

/-- Once a source construction supplies finite antitone approximants and their
pointwise limit, Claim 14.6(i) on that compact interval is automatic. -/
theorem claim14_6_i_of_finiteApproximation
    {H : Section13HatLayers} {sign : ErrorSign} {D d ε a b : ℝ}
    (h : Claim14_6FiniteApproximation H sign D d ε a b) :
    AntitoneOn (lambda H sign D d ε) (Icc a b) :=
  antitoneOn_of_pointwise_limit h.antitone h.pointwise

/-- The delayed positive integrand in the κ=1 Section 13 DDE. -/
def hatTailIntegrand (H : Section13HatLayers) (sign : ErrorSign) (t : ℝ) : ℝ :=
  t * H.T sign.opposite (t - 1)

/-- The DDE integrated on a finite interval. -/
theorem integral_hatTailIntegrand
    {H : Section13HatLayers} {β a b : ℝ} (hH : Section13HatContract H β)
    (sign : ErrorSign) (ha : β + sign.epsilon < a) (hab : a ≤ b) :
    (∫ t in a..b, hatTailIntegrand H sign t) =
      weightedHat H sign a - weightedHat H sign b := by
  let g : ℝ → ℝ := fun t => hatTailIntegrand H sign t
  have hcont : ContinuousOn g (Icc a b) := by
    apply continuousOn_id.mul
    apply (hH.continuous sign.opposite).comp
      (continuousOn_id.sub continuousOn_const)
    intro x hx
    have heps : 0 ≤ sign.epsilon := by cases sign <;> simp [ErrorSign.epsilon]
    have : 1 < x := by linarith [hH.beta_gt_one, ha, hx.1]
    exact sub_pos.mpr this
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivAt (-weightedHat H sign) (g x) x := by
    intro x hx
    simpa [g, hatTailIntegrand, neg_mul] using
      (hH.dde sign x (ha.trans_le hx.1)).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (HasDerivAt.continuousOn hderiv)
    (fun x hx => hderiv x ⟨hx.1.le, hx.2.le⟩)
    (hcont.intervalIntegrable_of_Icc hab)
  change (∫ t in a..b, g t) = _
  rw [hFTC]
  change -weightedHat H sign b - (-weightedHat H sign a) = _
  ring

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
