import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDDEUnitShiftRatioSanitized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PQBridge

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000


/-- Signed Iwaniec pairing, retaining the coefficient `b`. -/
noncomputable def section10SignedPairing (b : ℝ) (R r : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * r s * R s - b * ∫ t in s - 1..s, r (t + 1) * R t

private theorem movingWindow_hasDerivAt
    {f : ℝ → ℝ} (hf : Continuous f) (s : ℝ) :
    HasDerivAt (fun u => ∫ t in u - 1..u, f t) (f s - f (s - 1)) s := by
  have hi₁ : IntervalIntegrable f volume (s - 1) s := hf.intervalIntegrable _ _
  have hi₂ : IntervalIntegrable f volume s s := hf.intervalIntegrable _ _
  have hl0 := intervalIntegral.integral_hasDerivAt_left hi₁
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hl := hl0.comp s ((hasDerivAt_id s).sub_const 1)
  have hr := intervalIntegral.integral_hasDerivAt_right hi₂
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hsum := hl.add hr
  have heq : (fun u => (∫ t in u - 1..s, f t) + ∫ t in s..u, f t) =
      (fun u => ∫ t in u - 1..u, f t) := by
    funext u
    exact intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hev :
      (((fun u => ∫ t in u..s, f t) ∘ fun x => id x - 1) +
          fun u => ∫ t in s..u, f t) =ᶠ[𝓝 s]
        (fun u => ∫ t in u - 1..u, f t) := by
    filter_upwards [] with u
    simp only [Pi.add_apply, Function.comp_apply, id_eq]
    exact congrFun heq u
  have hsum' := hsum.congr_of_eventuallyEq hev.symm
  apply hsum'.congr_deriv
  ring

/-- Lemma 10.1, pointwise differential form: an original DDE solution paired
with an adjoint solution has zero pairing derivative. -/
theorem section10SignedPairing_hasDerivAt_zero
    {a b β s : ℝ} {R r : ℝ → ℝ}
    (hRcont : Continuous R) (hrcont : Continuous r)
    (_hs : β < s) (hs0 : s ≠ 0)
    (hR : HasDerivAt R (-(a * R s + b * R (s - 1)) / s) s)
    (hr : HasDerivAt (fun u => u * r u) (a * r s + b * r (s + 1)) s) :
    HasDerivAt (section10SignedPairing b R r) 0 s := by
  let f : ℝ → ℝ := fun t => r (t + 1) * R t
  have hf : Continuous f := (hrcont.comp (continuous_id.add continuous_const)).mul hRcont
  have hint := movingWindow_hasDerivAt hf s
  have hprod := hr.mul hR
  have hout := hprod.sub (hint.const_mul b)
  have hev :
      ((fun u => u * r u) * R - fun y => b * ∫ t in y - 1..y, f t) =ᶠ[𝓝 s]
        section10SignedPairing b R r := by
    filter_upwards [] with u
    rfl
  have hout' := hout.congr_of_eventuallyEq hev.symm
  apply hout'.congr_deriv
  simp only [f, sub_add_cancel]
  field_simp [hs0]
  ring

/-- Lemma 10.1 on an interval.  This is the actual comparison-side constancy
bridge; pairing vanishing is not assumed. -/
theorem section10SignedPairing_eq_of_dde
    {a b β x y : ℝ} {R r : ℝ → ℝ}
    (hxy : x ≤ y) (hβ : 1 ≤ β) (hx : β < x)
    (hRcont : Continuous R) (hrcont : Continuous r)
    (hR : ∀ s, β < s →
      HasDerivAt R (-(a * R s + b * R (s - 1)) / s) s)
    (hr : ∀ s, 0 < s →
      HasDerivAt (fun u => u * r u) (a * r s + b * r (s + 1)) s) :
    section10SignedPairing b R r y = section10SignedPairing b R r x := by
  have hx0 : 0 < x := by
    linarith
  have hd : ∀ s ∈ Icc x y, HasDerivAt (section10SignedPairing b R r) 0 s := by
    intro s hs
    have hβs : β < s := hx.trans_le hs.1
    exact section10SignedPairing_hasDerivAt_zero hRcont hrcont hβs
      (ne_of_gt (hx0.trans_le hs.1)) (hR s hβs) (hr s (hx0.trans_le hs.1))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
    (HasDerivAt.continuousOn hd)
    (fun s hs => hd s ⟨hs.1.le, hs.2.le⟩)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume x y)
  norm_num at hFTC
  linarith


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
