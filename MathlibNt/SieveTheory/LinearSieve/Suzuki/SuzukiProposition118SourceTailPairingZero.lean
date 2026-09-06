import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceSeriesPairing
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Proposition 11.8: decay of the genuine source Q and pairing at infinity

This file never identifies the source series with the Section-13 hat solution.
Instead it applies the production finite-depth domination from Lemma 13.2 to
finite odd/even source partial sums, passes to their genuine `tsum` limits, and
only then invokes the hat contract's (T5) decay.
-/

open scoped Classical BigOperators Interval
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The finite-depth source/hat comparison survives the two parity `tsum`
limits.  This is domination, not an identification of source and hat layers. -/
theorem suzukiProposition118SourceParitySeries_le_hat
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 2 ≤ s →
      suzukiProposition118SourceTPlus s ≤ C * s * H.T .plus s ∧
      suzukiProposition118SourceTMinus s ≤ C * s * H.T .minus s := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨C, le_trans (by norm_num) hC, ?_⟩
  intro s hs
  have hspos : 0 < s := by linarith
  constructor
  · have hpartial : ∀ m : ℕ,
        suzukiOddSourceUpperPartialSum m s ≤ C * s * H.T .plus s := by
      intro m
      cases m with
      | zero =>
          simp [suzukiOddSourceUpperPartialSum]
          exact mul_nonneg (mul_nonneg (le_trans (by norm_num) hC) hspos.le)
            (hH.positive .plus s hspos).le
      | succ m =>
          have hOdd : Odd (2 * m + 1) := Nat.odd_iff.mpr (by omega)
          have hdom : s ∈ KappaOneModel.parityDomain 2 (2 * m + 1) := by
            simp [KappaOneModel.parityDomain]
            linarith
          have hbound := hall (2 * m + 1) s (by omega) hdom
          rw [ErrorSign.ofDepth_of_odd hOdd] at hbound
          apply le_of_mul_le_mul_left _ hspos
          rw [← finiteSourceLayer_two_mul_add_one_eq_oddPartialSum]
          calc
            s * finiteSourceLayer 1 2 (2 * m + 1) s ≤
                C * s ^ 2 * H.T .plus s := hbound
            _ = s * (C * s * H.T .plus s) := by ring
    have hlim :=
      (summable_suzukiProposition118SourceTPlus_of_sourceContract hH
        (by linarith : 1 < s)).hasSum.tendsto_sum_nat
    exact le_of_tendsto' hlim (by
      intro m
      simpa [suzukiProposition118SourceTPlus, suzukiOddSourceUpperPartialSum] using
        hpartial m)
  · have hpartial : ∀ m : ℕ,
        suzukiEvenSourceLowerPartialSum m s ≤ C * s * H.T .minus s := by
      intro m
      cases m with
      | zero =>
          simp [suzukiEvenSourceLowerPartialSum]
          exact mul_nonneg (mul_nonneg (le_trans (by norm_num) hC) hspos.le)
            (hH.positive .minus s hspos).le
      | succ m =>
          have hEven : Even (2 * (m + 1)) := even_two_mul (m + 1)
          have hdom : s ∈ KappaOneModel.parityDomain 2 (2 * (m + 1)) := by
            simp [KappaOneModel.parityDomain, Nat.even_iff.mp hEven, hs]
          have hbound := hall (2 * (m + 1)) s (by omega) hdom
          rw [ErrorSign.ofDepth_of_even hEven] at hbound
          rw [suzukiEvenSourceLowerPartialSum_eq_finiteSourceLayer]
          apply le_of_mul_le_mul_left _ hspos
          calc
            s * finiteSourceLayer 1 2 (2 * (m + 1)) s ≤
                C * s ^ 2 * H.T .minus s := hbound
            _ = s * (C * s * H.T .minus s) := by ring
    have hlim :=
      (summable_suzukiProposition118SourceTMinus_of_sourceContract hH hs).hasSum.tendsto_sum_nat
    exact le_of_tendsto' hlim (by
      intro m
      simpa [suzukiProposition118SourceTMinus, suzukiEvenSourceLowerPartialSum] using
        hpartial m)

/-- On its series range, the genuine source `Q=T⁺+T⁻` is nonnegative and is
bounded by the sum of the two Section-13 hat majorants. -/
theorem suzukiProposition118SourceQ_nonneg_and_le_hat
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 2 ≤ s →
      0 ≤ suzukiProposition118SourceQ s ∧
      suzukiProposition118SourceQ s ≤ C * s * (H.T .plus s + H.T .minus s) := by
  obtain ⟨C, hC, hseries⟩ := suzukiProposition118SourceParitySeries_le_hat hH
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hs1 : 1 < s := by linarith
  have hplus0 : 0 ≤ suzukiProposition118SourceTPlus s :=
    tsum_nonneg (suzukiLayer_one_two_odd_nonneg hs1)
  have hminus0 : 0 ≤ suzukiProposition118SourceTMinus s :=
    tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg hs k)
  rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr hs)]
  refine ⟨add_nonneg hplus0 hminus0, ?_⟩
  rcases hseries s hs with ⟨hp, hm⟩
  calc
    suzukiProposition118SourceTPlus s + suzukiProposition118SourceTMinus s ≤
        C * s * H.T .plus s + C * s * H.T .minus s := add_le_add hp hm
    _ = C * s * (H.T .plus s + H.T .minus s) := by ring

/-- Quantitative eventual decay of the genuine source.  The extra factor `s`
comes from the finite source/hat comparison and is retained explicitly. -/
theorem suzukiProposition118SourceQ_eventually_le_mul_exp
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in atTop,
      0 ≤ suzukiProposition118SourceQ s ∧
      suzukiProposition118SourceQ s ≤ D * s * Real.exp (-s) := by
  obtain ⟨C, hC, hQ⟩ := suzukiProposition118SourceQ_nonneg_and_le_hat hH
  rcases hH.t5 .plus with ⟨Cp, hCp, hp⟩
  rcases hH.t5 .minus with ⟨Cm, hCm, hm⟩
  refine ⟨C * (Cp + Cm), mul_nonneg hC (add_nonneg hCp hCm), ?_⟩
  filter_upwards [hp, hm, eventually_ge_atTop (2 : ℝ)] with s hps hms hs
  have hs0 : 0 ≤ s := by linarith
  have hTp0 := (hH.positive .plus s (by linarith : 0 < s)).le
  have hTm0 := (hH.positive .minus s (by linarith : 0 < s)).le
  have hsum : H.T .plus s + H.T .minus s ≤ (Cp + Cm) * Real.exp (-s) := by
    rw [← abs_of_nonneg hTp0, ← abs_of_nonneg hTm0]
    linarith
  rcases hQ s hs with ⟨hQ0, hQle⟩
  refine ⟨hQ0, hQle.trans ?_⟩
  calc
    C * s * (H.T .plus s + H.T .minus s) ≤
        C * s * ((Cp + Cm) * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC hs0)
    _ = (C * (Cp + Cm)) * s * Real.exp (-s) := by ring

/-- The weighted genuine source has the explicit eventual majorant
`D s³ e⁻ˢ`. -/
theorem suzukiProposition118SourceQ_weighted_eventual_bound
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s : ℝ in atTop,
      0 ≤ s ^ 2 * suzukiProposition118SourceQ s ∧
      s ^ 2 * suzukiProposition118SourceQ s ≤
        D * (s ^ 3 * Real.exp (-s)) := by
  obtain ⟨D, hD, hQ⟩ := suzukiProposition118SourceQ_eventually_le_mul_exp hH
  refine ⟨D, hD, ?_⟩
  filter_upwards [hQ, eventually_ge_atTop (0 : ℝ)] with s hQp hs
  rcases hQp with ⟨hQ0, hQle⟩
  refine ⟨mul_nonneg (sq_nonneg s) hQ0, ?_⟩
  calc
    s ^ 2 * suzukiProposition118SourceQ s ≤ s ^ 2 * (D * s * Real.exp (-s)) :=
      mul_le_mul_of_nonneg_left hQle (sq_nonneg s)
    _ = D * (s ^ 3 * Real.exp (-s)) := by ring

/-- Consequently `s² Q(s) → 0` for the genuine source `Q`. -/
theorem tendsto_suzukiProposition118SourceQ_weighted_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (fun s : ℝ => s ^ 2 * suzukiProposition118SourceQ s) atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ := suzukiProposition118SourceQ_weighted_eventual_bound hH
  apply squeeze_zero' (hbound.mono fun _ hs => hs.1)
    (hbound.mono fun _ hs => hs.2)
  simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul D

/-- The moving-window integral in the source pairing tends to zero.  Its control
uses nonnegativity and the same genuine-source exponential majorant. -/
theorem tendsto_suzukiProposition118SourceQ_pairing_integral_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (fun s : ℝ => ∫ t in s - 1..s,
      suzukiProposition118KappaOneSourceAdjoint (t + 1) *
        suzukiProposition118SourceQ t) atTop (𝓝 0) := by
  obtain ⟨D, hD, hQ⟩ := suzukiProposition118SourceQ_eventually_le_mul_exp hH
  rcases eventually_atTop.1 hQ with ⟨A, hA⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (show Tendsto (fun s : ℝ => (D * Real.exp 1) *
        (s ^ 2 * Real.exp (-s))) atTop (𝓝 0) by
      simpa using tendsto_const_nhds.mul
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2))
  filter_upwards [eventually_ge_atTop (max 3 (A + 1))] with s hs
  have hs3 : 3 ≤ s := le_trans (le_max_left _ _) hs
  have hAs : A + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hab : s - 1 ≤ s := by linarith
  have hint :
      ‖∫ t in s - 1..s,
        suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQ t‖ ≤
        (D * Real.exp 1 * s ^ 2 * Real.exp (-s)) * |s - (s - 1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Ioc (s - 1) s := by simpa [uIoc_of_le hab] using ht
    have htA : A ≤ t := by linarith [ht'.1, hAs]
    rcases hA t htA with ⟨hQt0, hQt⟩
    have ht0 : 0 ≤ t := by linarith [ht'.1, hs3]
    have hts : t ≤ s := ht'.2
    rw [suzukiProposition118KappaOneSourceAdjoint]
    norm_num only [add_sub_cancel_right]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hQt0)]
    calc
      t * suzukiProposition118SourceQ t ≤ t * (D * t * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left hQt ht0
      _ ≤ D * s ^ 2 * Real.exp (-t) := by
        have htt : t * t ≤ s * s := mul_self_le_mul_self ht0 hts
        calc
          t * (D * t * Real.exp (-t)) =
              (D * Real.exp (-t)) * (t * t) := by ring
          _ ≤ (D * Real.exp (-t)) * (s * s) :=
            mul_le_mul_of_nonneg_left htt (mul_nonneg hD (Real.exp_pos (-t)).le)
          _ = D * s ^ 2 * Real.exp (-t) := by ring
      _ ≤ D * s ^ 2 * (Real.exp 1 * Real.exp (-s)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (sq_nonneg s))
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [ht'.1])
      _ = D * Real.exp 1 * s ^ 2 * Real.exp (-s) := by ring
  rw [show |s - (s - 1)| = 1 by rw [abs_eq_self.mpr] <;> linarith, mul_one] at hint
  simpa [mul_assoc, mul_left_comm, mul_comm] using hint

/-- The point term in the source pairing tends to zero by weighted source
decay and the linear source adjoint. -/
theorem tendsto_suzukiProposition118SourceQ_pairing_point_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (fun s : ℝ => s * suzukiProposition118KappaOneSourceAdjoint s *
      suzukiProposition118SourceQ s) atTop (𝓝 0) := by
  obtain ⟨D, hD, hbound⟩ := suzukiProposition118SourceQ_weighted_eventual_bound hH
  have hpoint : ∀ᶠ s : ℝ in atTop,
      0 ≤ s * suzukiProposition118KappaOneSourceAdjoint s *
        suzukiProposition118SourceQ s ∧
      s * suzukiProposition118KappaOneSourceAdjoint s *
        suzukiProposition118SourceQ s ≤ s ^ 2 * suzukiProposition118SourceQ s := by
    filter_upwards [hbound, eventually_ge_atTop (2 : ℝ)] with s hbound_s hs
    have hs0 : 0 < s := by linarith
    have hQ0 : 0 ≤ suzukiProposition118SourceQ s :=
      nonneg_of_mul_nonneg_right hbound_s.1 (sq_pos_of_pos hs0)
    rw [suzukiProposition118KappaOneSourceAdjoint]
    constructor
    · exact mul_nonneg (mul_nonneg hs0.le (by linarith)) hQ0
    · exact mul_le_mul_of_nonneg_right (by nlinarith : s * (s - 1) ≤ s ^ 2) hQ0
  exact squeeze_zero' (hpoint.mono fun _ hs => hs.1)
    (hpoint.mono fun _ hs => hs.2)
    (tendsto_suzukiProposition118SourceQ_weighted_zero hH)

/-- The genuine Proposition-11.8 source pairing tends to zero at infinity. -/
theorem tendsto_suzukiProposition118SourceQPairing_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto suzukiProposition118SourceQPairing atTop (𝓝 0) := by
  have hp := tendsto_suzukiProposition118SourceQ_pairing_point_zero hH
  have hi := tendsto_suzukiProposition118SourceQ_pairing_integral_zero hH
  change Tendsto
    (section10SignedPairing 1 suzukiProposition118SourceQ
      suzukiProposition118KappaOneSourceAdjoint) atTop (𝓝 0)
  rw [show section10SignedPairing 1 suzukiProposition118SourceQ
      suzukiProposition118KappaOneSourceAdjoint =
      (fun s : ℝ => s * suzukiProposition118KappaOneSourceAdjoint s *
        suzukiProposition118SourceQ s -
        ∫ t in s - 1..s,
          suzukiProposition118KappaOneSourceAdjoint (t + 1) *
            suzukiProposition118SourceQ t) by
    funext s
    simp [section10SignedPairing]
  ]
  simpa using hp.sub hi


end MathlibNt.SieveTheory
