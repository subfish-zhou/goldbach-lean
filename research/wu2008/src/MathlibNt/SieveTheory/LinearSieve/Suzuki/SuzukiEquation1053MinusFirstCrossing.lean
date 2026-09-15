import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiEquation1053NonCircular
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

/-!
# Source-correct minus first crossing and window order for (10.53)

Unlike the withdrawn right-endpoint-maximum model, the source chooses the first
point where `(log W₋)'` becomes nonnegative.  The resulting history makes `W₋`
antitone up to the crossing.  Thus the upper endpoint consumed by the pairing
integral is the *left* endpoint `s - 1`, not `s`.
-/

namespace Section10Equation1053MinusFirstCrossing

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10Equation1053
open Section10Equation1053NonCircular

/-- Source-facing data for the first minus crossing.  `slope` is the actual
logarithmic derivative.  The first two sign fields say it is negative on the
initial interval and remains negative after `s₀` until the least crossing `s`;
`crossing_nonneg` records membership of `s` in the closed failure set. -/
structure MinusFirstCrossing
    (R ξ : ℝ → ℝ) (c β s₀ : ℝ) where
  s : ℝ
  slope : ℝ → ℝ
  beta_lt_s₀ : β < s₀
  s₀_lt_s : s₀ < s
  beta_add_one_le_s : β + 1 ≤ s
  slope_continuousAt : ContinuousAt slope s
  log_continuousOn : ContinuousOn (logEnvelopeMinus R ξ c) (Icc β s)
  hasDeriv : ∀ u ∈ Ioc β s,
    HasDerivAt (logEnvelopeMinus R ξ c) (slope u) u
  initial_neg : ∀ u ∈ Icc β s₀, slope u < 0
  before_crossing_neg : ∀ u, s₀ < u → u < s → slope u < 0
  crossing_nonneg : 0 ≤ slope s

lemma MinusFirstCrossing.slope_neg_before
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : MinusFirstCrossing R ξ c β s₀)
    {u : ℝ} (hβu : β ≤ u) (hus : u < w.s) :
    w.slope u < 0 := by
  by_cases hu : u ≤ s₀
  · exact w.initial_neg u ⟨hβu, hu⟩
  · exact w.before_crossing_neg u (lt_of_not_ge hu) hus

/-- `s` really is the least point at or after `s₀` where the logarithmic
derivative is nonnegative. -/
lemma MinusFirstCrossing.isLeast_nonnegative
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : MinusFirstCrossing R ξ c β s₀) :
    IsLeast {u : ℝ | s₀ ≤ u ∧ 0 ≤ w.slope u} w.s := by
  constructor
  · exact ⟨w.s₀_lt_s.le, w.crossing_nonneg⟩
  · intro u hu
    by_contra hsu
    have hus : u < w.s := lt_of_not_ge hsu
    have hβu : β ≤ u := le_trans w.beta_lt_s₀.le hu.1
    exact (not_lt_of_ge hu.2) (w.slope_neg_before hβu hus)

/-- Continuity of the logarithmic derivative turns the weak sign at the least
crossing into equality. -/
lemma MinusFirstCrossing.slope_at_crossing_eq_zero
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : MinusFirstCrossing R ξ c β s₀) :
    w.slope w.s = 0 := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  have hlim : Tendsto w.slope (𝓝[<] w.s) (𝓝 (w.slope w.s)) :=
    w.slope_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ u in 𝓝[<] w.s, w.slope u ≤ 0 := by
    filter_upwards [eventually_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hβs)] with u hus hβu
    exact (w.slope_neg_before hβu.le hus).le
  exact le_antisymm (le_of_tendsto hlim hevent) w.crossing_nonneg

/-- The least crossing is a stationary point of `log W₋`. -/
lemma MinusFirstCrossing.stationary
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : MinusFirstCrossing R ξ c β s₀) :
    HasDerivAt (logEnvelopeMinus R ξ c) 0 w.s := by
  have hsI : w.s ∈ Ioc β w.s :=
    ⟨w.beta_lt_s₀.trans w.s₀_lt_s, le_rfl⟩
  simpa [w.slope_at_crossing_eq_zero] using w.hasDeriv w.s hsI

/-- In the specialized `a=2,b=1` DDE, the stationary conclusion is exactly
Suzuki's algebraic stationary equation. -/
lemma MinusFirstCrossing.normalizedMinusBase_eq
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hξ : Proposition1020Xi ξ)
    (w : MinusFirstCrossing R ξ c β s₀) :
    normalizedMinusBase R ξ w.s = c := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  have hs0 : 0 < w.s := lt_of_lt_of_le
    (by linarith [h.beta_ge_one]) hβs.le
  have hRs : 0 < R w.s := h.positive w.s (by linarith)
  have hd := lemma1028_logEnvelopeMinus_hasDerivAt hξ (c := c) hs0 hRs
    (h.original_dde w.s hβs)
  have hz := w.stationary
  have heq := hz.unique hd
  dsimp [normalizedMinusBase] at *
  linarith

/-- First-crossing history forces `log W₋` to decrease on the complete prefix. -/
lemma MinusFirstCrossing.log_antitoneOn
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (w : MinusFirstCrossing R ξ c β s₀) :
    AntitoneOn (logEnvelopeMinus R ξ c) (Icc β w.s) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc β w.s) w.log_continuousOn
  · intro u hu
    have huIoo : u ∈ Ioo β w.s := by
      simpa only [interior_Icc] using hu
    exact (w.hasDeriv u ⟨huIoo.1, huIoo.2.le⟩).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    exact (w.slope_neg_before hu.1.le hu.2).le

lemma envelopeMinus_eq_exp_logEnvelopeMinus_of_pos
    {R ξ : ℝ → ℝ} {c t : ℝ} (hRt : 0 < R t) :
    envelopeMinus R ξ c t = Real.exp (logEnvelopeMinus R ξ c t) := by
  rw [logEnvelopeMinus, envelopeMinus, phiMinus]
  calc
    R t * Real.exp (xiPhase ξ t - c * t) =
        Real.exp (Real.log (R t)) * Real.exp (xiPhase ξ t - c * t) := by
          rw [Real.exp_log hRt]
    _ = Real.exp (Real.log (R t) + (xiPhase ξ t - c * t)) := by
          rw [Real.exp_add]
    _ = Real.exp (Real.log (R t) + xiPhase ξ t - c * t) := by
          congr 1
          ring

/-- Since the exponential is increasing, the logarithmic first-crossing
history makes the weighted envelope itself antitone on `[β,s]`. -/
lemma MinusFirstCrossing.envelope_antitoneOn
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (w : MinusFirstCrossing R ξ c β s₀) :
    AntitoneOn (envelopeMinus R ξ c) (Icc β w.s) := by
  intro x hx y hy hxy
  have hRx : 0 < R x := h.positive x (by linarith [hx.1])
  have hRy : 0 < R y := h.positive y (by linarith [hy.1])
  rw [envelopeMinus_eq_exp_logEnvelopeMinus_of_pos hRx,
    envelopeMinus_eq_exp_logEnvelopeMinus_of_pos hRy]
  exact Real.exp_le_exp.mpr (w.log_antitoneOn hx hy hxy)

/-- The source's full minus-window order:
`W₋(s-1) ≥ W₋(t) ≥ W₋(s)` for `t ∈ [s-1,s]`. -/
theorem MinusFirstCrossing.window_order
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (w : MinusFirstCrossing R ξ c β s₀)
    {t : ℝ} (ht : t ∈ Icc (w.s - 1) w.s) :
    envelopeMinus R ξ c t ≤ envelopeMinus R ξ c (w.s - 1) ∧
      envelopeMinus R ξ c w.s ≤ envelopeMinus R ξ c t := by
  have hleftI : w.s - 1 ∈ Icc β w.s := by
    constructor <;> linarith [w.beta_add_one_le_s]
  have htI : t ∈ Icc β w.s := by
    exact ⟨by linarith [w.beta_add_one_le_s, ht.1], ht.2⟩
  have hsI : w.s ∈ Icc β w.s :=
    ⟨by linarith [w.beta_add_one_le_s], le_rfl⟩
  exact ⟨w.envelope_antitoneOn h hleftI htI ht.1,
    w.envelope_antitoneOn h htI hsI ht.2⟩

/-- Source-correct pairing comparison.  The upper bound is `W₋(s-1)`.
Using `W₋(s)` here would reverse the first inequality in `window_order`. -/
theorem pairing_le_leftEndpoint_kernel
    {R ξ : ℝ → ℝ} {c β s₀ : ℝ}
    (h : FirstCrossingDDEApparatus R β)
    (hadj : h.adjoint = explicitKappaOneAdjointPlus)
    (w : MinusFirstCrossing R ξ c β s₀)
    (hs2 : 2 ≤ w.s)
    (hprodInt : IntervalIntegrable
      (fun t => envelopeMinus R ξ c t *
        Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s)
    (hkernelInt : IntervalIntegrable
      (fun t => Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t))
      volume (w.s - 1) w.s) :
    w.s * explicitKappaOneAdjointPlus w.s * R w.s ≤
      envelopeMinus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) := by
  have hβs : β < w.s := w.beta_lt_s₀.trans w.s₀_lt_s
  rw [explicit_pairing_weighted_identity h hadj hβs hs2 (ξ := ξ) (c := c)]
  calc
    (∫ t in w.s - 1..w.s,
        envelopeMinus R ξ c t *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) ≤
      ∫ t in w.s - 1..w.s,
        envelopeMinus R ξ c (w.s - 1) *
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t) := by
            apply intervalIntegral.integral_mono_on (by linarith)
            · exact hprodInt
            · exact hkernelInt.const_mul _
            · intro t ht
              exact mul_le_mul_of_nonneg_right
                ((w.window_order h ht).1) (Real.exp_pos _).le
    _ = envelopeMinus R ξ c (w.s - 1) *
        (∫ t in w.s - 1..w.s,
          Real.exp (-psiMinus explicitKappaOneAdjointPlus ξ c t)) := by
            rw [intervalIntegral.integral_const_mul]


end Section10Equation1053MinusFirstCrossing
