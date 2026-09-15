import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118KappaOneBoundaryAdjoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveAmplitudeLimit

/-!
# Suzuki Proposition 11.8: source parity series and the boundary pairing

This module uses the actual source layers `fₙ` of (9.1)--(9.2), not the
Section-13 hat solutions.  At `κ = 1`, `β = 2`, equation (9.5) is

* `T⁺(s) = ∑' k, f_{2k+1}(s)` on `s > 1`;
* `T⁻(s) = ∑' k, f_{2(k+1)}(s)` on `s ≥ 2`.

As on printed pp. 63--65, Proposition 11.8 extends
`P = T⁺ - T⁻ + 2` and `Q = T⁺ + T⁻` from `s ≥ β` to the initial interval by
`s P(s) = s Q(s) = A`.  We then evaluate the genuine Section-10 Iwaniec
pairing of this source `Q` with `q(s)=s-1` at `β=2`.
-/

open scoped Classical BigOperators Interval
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- Suzuki (9.5), positive/odd parity source series `T⁺`. -/
noncomputable def suzukiProposition118SourceTPlus (s : ℝ) : ℝ :=
  ∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) s

/-- Suzuki (9.5), negative/even parity source series `T⁻`. -/
noncomputable def suzukiProposition118SourceTMinus (s : ℝ) : ℝ :=
  ∑' k : ℕ, suzukiLayer 1 2 (2 * (k + 1)) s

@[simp] theorem suzukiProposition118SourceTMinus_eq (s : ℝ) :
    suzukiProposition118SourceTMinus s = suzukiEvenSourceLowerLayerLimit s := rfl

/-- Every odd source layer is nonnegative on its exact source domain `s > 1`. -/
theorem suzukiLayer_one_two_odd_nonneg {s : ℝ} (hs : 1 < s) (k : ℕ) :
    0 ≤ suzukiLayer 1 2 (2 * k + 1) s := by
  apply suzukiLayer_one_nonneg_on_parityDomain (by norm_num : (1 : ℝ) < 2)
  simp [suzukiParityDomainOne, KappaOneModel.parityDomain]
  linarith

/-- The production all-depth comparison gives one bound for all odd source
partial sums at every fixed point of the exact odd domain. -/
theorem suzukiOddSourceUpperPartialSum_bounded_of_sourceContract_at
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 < s) :
    ∃ B : ℝ, ∀ m : ℕ, suzukiOddSourceUpperPartialSum m s ≤ B := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨C * s * H.T .plus s, ?_⟩
  intro m
  cases m with
  | zero =>
      simp [suzukiOddSourceUpperPartialSum]
      exact mul_nonneg
        (mul_nonneg (le_trans (by norm_num) hC) (le_of_lt (by linarith : 0 < s)))
        (le_of_lt (hH.positive .plus s (by linarith)))
  | succ m =>
      have hOdd : Odd (2 * m + 1) := Nat.odd_iff.mpr (by omega)
      have hdom : s ∈ KappaOneModel.parityDomain 2 (2 * m + 1) := by
        simp [KappaOneModel.parityDomain]
        linarith
      have hbound := hall (2 * m + 1) s (by omega) hdom
      rw [ErrorSign.ofDepth_of_odd hOdd] at hbound
      apply le_of_mul_le_mul_left _ (by linarith : 0 < s)
      rw [← finiteSourceLayer_two_mul_add_one_eq_oddPartialSum]
      calc
        s * finiteSourceLayer 1 2 (2 * m + 1) s ≤
            C * s ^ 2 * H.T .plus s := hbound
        _ = s * (C * s * H.T .plus s) := by ring

/-- Real summability of the actual odd source series throughout `I⁺=(1,∞)`. -/
theorem summable_suzukiProposition118SourceTPlus_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 1 < s) :
    Summable (fun k : ℕ => suzukiLayer 1 2 (2 * k + 1) s) := by
  obtain ⟨B, hB⟩ :=
    suzukiOddSourceUpperPartialSum_bounded_of_sourceContract_at hH hs
  apply summable_of_sum_range_le (fun k => suzukiLayer_one_two_odd_nonneg hs k)
  intro m
  simpa [suzukiOddSourceUpperPartialSum] using hB m

/-- Real summability of the actual even source series throughout `I⁻=[2,∞)`. -/
theorem summable_suzukiProposition118SourceTMinus_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    Summable (fun k : ℕ => suzukiLayer 1 2 (2 * (k + 1)) s) :=
  summable_suzukiLayer_one_two_even_of_sourceContract hH hs

/-- Proposition 9.4(vii), obtained as the real limit of the finite
Proposition-9.3 identity, on the closed part of the first odd strip. -/
theorem mul_suzukiProposition118SourceTPlus_eq_amplitude_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs1 : 1 < s) (hs3 : s ≤ 3) :
    s * suzukiProposition118SourceTPlus s =
      SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude - s := by
  have hsSum :=
    (summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs1).hasSum.tendsto_sum_nat
  have hAmp := tendsto_suzukiFiniteLowerAmplitude hH
  have hfinite : ∀ m : ℕ, 1 ≤ m →
      s * suzukiOddSourceUpperPartialSum m s = suzukiFiniteLowerAmplitude m - s := by
    intro m hm
    exact mul_suzukiOddSourceUpperPartialSum_eq_finiteAmplitude_sub hm hs1.le hs3
  have hevent : ∀ᶠ m in atTop,
      s * suzukiOddSourceUpperPartialSum m s = suzukiFiniteLowerAmplitude m - s := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact hfinite m hm
  have hleft : Tendsto (fun m => s * suzukiOddSourceUpperPartialSum m s) atTop
      (𝓝 (s * suzukiProposition118SourceTPlus s)) :=
    tendsto_const_nhds.mul hsSum
  have hright : Tendsto (fun m => suzukiFiniteLowerAmplitude m - s) atTop
      (𝓝 (SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude - s)) :=
    hAmp.sub tendsto_const_nhds
  have hevent' : ∀ᶠ m in atTop,
      suzukiFiniteLowerAmplitude m - s =
        s * suzukiOddSourceUpperPartialSum m s :=
    hevent.mono (fun _ h => h.symm)
  exact tendsto_nhds_unique hleft (hright.congr' hevent')

/-- The genuine source `Q` of Proposition 11.8.  Below `β=2` this is precisely
its source-prescribed initial history, not a Section-13 hat function. -/
noncomputable def suzukiProposition118SourceQ (s : ℝ) : ℝ :=
  if s < 2 then SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude / s
  else suzukiProposition118SourceTPlus s + suzukiProposition118SourceTMinus s

/-- The genuine source `P` of Proposition 11.8. -/
noncomputable def suzukiProposition118SourceP (s : ℝ) : ℝ :=
  if s < 2 then SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude / s
  else suzukiProposition118SourceTPlus s - suzukiProposition118SourceTMinus s + 2

/-- The exact initial-history equation `s Q(s)=A`, printed before and in the
proof of Proposition 11.8. -/
theorem suzukiProposition118SourceQ_initial {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    s * suzukiProposition118SourceQ s =
      SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude := by
  rw [suzukiProposition118SourceQ, if_pos hs2]
  field_simp [ne_of_gt (by linarith : 0 < s)]

/-- The exact initial-history equation `s P(s)=A`. -/
theorem suzukiProposition118SourceP_initial {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    s * suzukiProposition118SourceP s =
      SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude := by
  rw [suzukiProposition118SourceP, if_pos hs2]
  field_simp [ne_of_gt (by linarith : 0 < s)]

/-- At `β=2`, the source series has the boundary value
`Q(2)=(A-B)/2`, deduced from the actual odd/even real series. -/
theorem suzukiProposition118SourceQ_at_two
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiProposition118SourceQ 2 =
      (SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude -
        suzukiLowerBoundaryLimit) / 2 := by
  rw [suzukiProposition118SourceQ, if_neg (by norm_num : ¬ (2 : ℝ) < 2)]
  have hplus := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
    (s := (2 : ℝ)) (by norm_num) (by norm_num)
  simp only [suzukiProposition118SourceTMinus_eq]
  unfold suzukiLowerBoundaryLimit at ⊢
  linarith

/-- The source Iwaniec pairing `⟨Q,q⟩` from Section 10, with `b=κ=1`. -/
noncomputable def suzukiProposition118SourceQPairing (s : ℝ) : ℝ :=
  section10SignedPairing 1 suzukiProposition118SourceQ
    suzukiProposition118KappaOneSourceAdjoint s

/-- On the initial pairing window `[1,2]`, the integral term is exactly `A`.
The exceptional boundary point `t=2`, where source `Q` switches from its
initial history to the convergent parity series, is null for integration. -/
theorem suzukiProposition118SourceQ_initialWindowIntegral :
    (∫ t in (1 : ℝ)..2,
      suzukiProposition118KappaOneSourceAdjoint (t + 1) *
        suzukiProposition118SourceQ t) =
      SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude := by
  let A : ℝ := SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude
  have hcongr :
      (∫ t in (1 : ℝ)..2,
        suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQ t) = ∫ _t in (1 : ℝ)..2, A := by
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
      rw [ae_iff]
      simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
        (measure_singleton (μ := volume) (2 : ℝ))
    filter_upwards [hne] with t ht2
    intro ht
    rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
    have htlt : t < 2 := lt_of_le_of_ne ht.2 (fun h => ht2 h)
    rw [suzukiProposition118SourceQ, if_pos htlt]
    dsimp [suzukiProposition118KappaOneSourceAdjoint, A]
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_const]
  norm_num [A]

/-- Proposition 11.8(iii)'s boundary evaluation for the genuine source series:
`⟨Q,q⟩(β)` is exactly the previously frozen scalar `-B + A q(β-1)`.
There is no pairing-zero or conclusion-shaped premise. -/
theorem suzukiProposition118SourceQPairing_at_lowerBoundary
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    suzukiProposition118SourceQPairing 2 =
      suzukiProposition118LowerBoundaryPairingScalar
        SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude := by
  rw [suzukiProposition118SourceQPairing, section10SignedPairing,
    show (2 : ℝ) - 1 = 1 by norm_num,
    suzukiProposition118SourceQ_initialWindowIntegral,
    suzukiProposition118SourceQ_at_two hH,
    suzukiProposition118LowerBoundaryPairingScalar_eq_neg]
  norm_num [suzukiProposition118KappaOneSourceAdjoint]
  ring


end MathlibNt.SieveTheory
