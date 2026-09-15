import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerEvenLimit
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118InitialStripReduction

/-!
# Real convergence of the even lower source layers

This module turns the all-depth source/hat comparison proved in the production
Lemma 13.2 development into genuine real summability.  In particular, the
`ENNReal` supremum used by `SuzukiFiniteSourceLayerEvenLimit` is finite whenever
the production Section-13 source contract is available.  No finite scan and no
caller-supplied summable sequence occurs here.
-/

open scoped Classical BigOperators ENNReal
open Finset Filter Topology Set

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- The production all-depth comparison supplies a single bound for every even
partial sum at a fixed lower-parity coordinate. -/
theorem suzukiEvenSourceLowerPartialSum_bounded_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    ∃ B : ℝ, ∀ m : ℕ, suzukiEvenSourceLowerPartialSum m s ≤ B := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  refine ⟨C * s * H.T .minus s, ?_⟩
  intro m
  cases m with
  | zero =>
      simp [suzukiEvenSourceLowerPartialSum]
      exact mul_nonneg
        (mul_nonneg (le_trans (by norm_num) hC) (le_trans (by norm_num) hs))
        (le_of_lt (hH.positive .minus s (by linarith)))
  | succ m =>
      have hEven : Even (2 * (m + 1)) := even_two_mul (m + 1)
      have hdom : s ∈ KappaOneModel.parityDomain 2 (2 * (m + 1)) := by
        simp [KappaOneModel.parityDomain, Nat.even_iff.mp hEven, hs]
      have hbound := hall (2 * (m + 1)) s (by omega) hdom
      rw [ErrorSign.ofDepth_of_even hEven] at hbound
      rw [suzukiEvenSourceLowerPartialSum_eq_finiteSourceLayer]
      have hspos : 0 < s := by linarith
      apply le_of_mul_le_mul_left _ hspos
      calc
        s * finiteSourceLayer 1 2 (2 * (m + 1)) s ≤
            C * s ^ 2 * H.T .minus s := hbound
        _ = s * (C * s * H.T .minus s) := by ring

/-- The actual even lower-layer sequence is summable; the majorization is
produced by the production all-depth source/hat theorem, rather than accepted as
an abstract `Summable` premise. -/
theorem summable_suzukiLayer_one_two_even_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    Summable (fun k : ℕ => suzukiLayer 1 2 (2 * (k + 1)) s) := by
  obtain ⟨B, hB⟩ :=
    suzukiEvenSourceLowerPartialSum_bounded_of_sourceContract hH hs
  apply summable_of_sum_range_le (fun k => suzukiLayer_one_two_even_nonneg hs k)
  intro m
  simpa [suzukiEvenSourceLowerPartialSum] using hB m

/-- The finite real value of the even lower source-layer series. -/
noncomputable def suzukiEvenSourceLowerLayerLimit (s : ℝ) : ℝ :=
  ∑' k : ℕ, suzukiLayer 1 2 (2 * (k + 1)) s

/-- Real partial sums converge to the genuine `tsum`. -/
theorem tendsto_suzukiEvenSourceLowerPartialSum_real
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    Tendsto (fun m => suzukiEvenSourceLowerPartialSum m s) atTop
      (𝓝 (suzukiEvenSourceLowerLayerLimit s)) := by
  exact (summable_suzukiLayer_one_two_even_of_sourceContract hH hs).hasSum.tendsto_sum_nat

/-- The unconditional extended supremum is the `ofReal` image of the real
series value. -/
theorem suzukiEvenSourceLowerLayerSup_eq_ofReal_limit
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiEvenSourceLowerLayerSup s =
      ENNReal.ofReal (suzukiEvenSourceLowerLayerLimit s) := by
  have hReal := tendsto_suzukiEvenSourceLowerPartialSum_real hH hs
  have hOfReal := ENNReal.tendsto_ofReal hReal
  exact (tendsto_nhds_unique
    (tendsto_suzukiEvenSourceLowerPartialSum_ofReal hs) hOfReal)

/-- In particular the lower-layer supremum is finite. -/
theorem suzukiEvenSourceLowerLayerSup_ne_top_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 ≤ s) :
    suzukiEvenSourceLowerLayerSup s ≠ ∞ := by
  rw [suzukiEvenSourceLowerLayerSup_eq_ofReal_limit hH hs]
  exact ENNReal.ofReal_ne_top

/-- Proposition 11.8's compact-strip consequence is produced from the same
all-depth source comparison.  Compactness is used only in the real coordinate;
there is no scan over depths. -/
theorem proposition118_initialStripSourceBound_of_sourceContract
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Proposition118InitialStripSourceBound := by
  obtain ⟨C, hC, hall⟩ := lemma132_finiteLayerHatUniform_slack hH
  let f : ErrorSign → ℝ → ℝ := fun sign x => C * x ^ 2 * H.T sign x
  have hf : ∀ sign, ContinuousOn (f sign) (Icc (1 : ℝ) 4) := by
    intro sign
    apply (continuousOn_const.mul (continuousOn_id.pow 2)).mul
    exact (hH.continuous sign).mono (by
      intro x hx
      exact hx.1.trans_lt' (by norm_num))
  obtain ⟨xp, hxp, hpmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) 4).Nonempty by exact ⟨1, by norm_num⟩) (hf .plus)
  obtain ⟨xm, hxm, hmmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) 4).Nonempty by exact ⟨1, by norm_num⟩) (hf .minus)
  refine ⟨max (f .plus xp) (f .minus xm), ?_, ?_⟩
  · have hfp0 : 0 ≤ f .plus xp := by
      exact mul_nonneg
        (mul_nonneg (le_trans (by norm_num) hC) (sq_nonneg xp))
        (le_of_lt (hH.positive .plus xp (by linarith [hxp.1])))
    exact hfp0.trans (le_max_left _ _)
  · intro N x hN hxdom hx4
    have hx1 : 1 ≤ x := by
      unfold KappaOneModel.parityDomain at hxdom
      split at hxdom <;> simp_all <;> linarith
    have hxI : x ∈ Icc (1 : ℝ) 4 := ⟨hx1, hx4⟩
    have hsource := hall N x hN hxdom
    rcases Nat.even_or_odd N with hEven | hOdd
    · rw [ErrorSign.ofDepth_of_even hEven] at hsource
      exact hsource.trans ((hmmax hxI).trans (le_max_right _ _))
    · rw [ErrorSign.ofDepth_of_odd hOdd] at hsource
      exact hsource.trans ((hpmax hxI).trans (le_max_left _ _))


end MathlibNt.SieveTheory
