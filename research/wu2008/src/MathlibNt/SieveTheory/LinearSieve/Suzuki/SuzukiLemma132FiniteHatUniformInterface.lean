import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-!
# Uniform finite-layer / hat-layer bridge for `Σ₁₁`

At `κ = κ̂ = 1`, Suzuki's (9.6) is `finiteSourceLayer 1 2 M x`.
The finite statement (13.13) in the proof of Lemma 13.2 is

`x * T_M(x) ≤ C * x^2 * T̂^(parity M)(x)`

with one `C = C(κ)` for every depth `M ≥ 1` and every `x ∈ I_M`.
The proposition below freezes exactly that still-missing source edge.  In
particular, it does not manufacture a coefficient by dividing one target value
by another.
-/

/-- Exact `κ = 1`, `β = 2` specialization of Suzuki (13.13).  The single
constant is outside both the depth and coordinate quantifiers. -/
def Section13FiniteLayerHatUniform (H : Section13HatLayers) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) (x : ℝ),
    1 ≤ M →
    x ∈ KappaOneModel.parityDomain 2 M →
    x * finiteSourceLayer 1 2 M x ≤
      C * x ^ 2 * H.T (ErrorSign.ofDepth M) x

/-- Cancellation of the positive source coordinate converts source (13.13)
into the unweighted form consumed by the `Σ₁₁` endpoint.  The same `C` remains
uniform in `M` and `x`. -/
theorem finiteSourceLayer_le_uniform_mul_hat
    {H : Section13HatLayers}
    (hbridge : Section13FiniteLayerHatUniform H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) (x : ℝ),
      1 ≤ M →
      0 < x →
      x ∈ KappaOneModel.parityDomain 2 M →
      finiteSourceLayer 1 2 M x ≤
        C * (x * H.T (ErrorSign.ofDepth M) x) := by
  obtain ⟨C, hC, hmajor⟩ := hbridge
  refine ⟨C, hC, ?_⟩
  intro M x hM hx hxdom
  apply le_of_mul_le_mul_left _ hx
  calc
    x * finiteSourceLayer 1 2 M x ≤
        C * x ^ 2 * H.T (ErrorSign.ofDepth M) x := hmajor M x hM hxdom
    _ = x * (C * (x * H.T (ErrorSign.ofDepth M) x)) := by ring

/-- The literal predecessor/sign form required in Case I: depth `N-1` has the
sign opposite to depth `N`.  One constant works simultaneously for every
`N ≥ 2` and every legal moving coordinate `s`. -/
theorem finiteSourceLayer_pred_le_uniform_oppositeHat
    {H : Section13HatLayers}
    (hbridge : Section13FiniteLayerHatUniform H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (s : ℝ),
      2 ≤ N →
      2 ≤ s →
      s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
      finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
        C * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) := by
  obtain ⟨C, hC, hmajor⟩ := finiteSourceLayer_le_uniform_mul_hat hbridge
  refine ⟨C, hC, ?_⟩
  intro N s hN hs hsdom
  have hpred : 1 ≤ N - 1 := by omega
  have hx : 0 < s - 1 := by linarith
  have h := hmajor (N - 1) (s - 1) hpred hx hsdom
  rw [ErrorSign.ofDepth_pred_eq_opposite (by omega : 1 ≤ N)] at h
  exact h

/-- Explicit moving-window packaging.  The bound does not acquire a new
coefficient when `s` or the outer endpoint `σ` moves. -/
theorem finiteSourceLayer_pred_le_uniform_oppositeHat_on_window
    {H : Section13HatLayers}
    (hbridge : Section13FiniteLayerHatUniform H) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (s σ : ℝ),
      2 ≤ N →
      2 ≤ s →
      s ≤ σ →
      s - 1 ∈ KappaOneModel.parityDomain 2 (N - 1) →
      finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
        C * ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) := by
  obtain ⟨C, hC, h⟩ := finiteSourceLayer_pred_le_uniform_oppositeHat hbridge
  exact ⟨C, hC, fun N s _σ hN hs _hsσ hdom => h N s hN hs hdom⟩


end MathlibNt.SieveTheory
