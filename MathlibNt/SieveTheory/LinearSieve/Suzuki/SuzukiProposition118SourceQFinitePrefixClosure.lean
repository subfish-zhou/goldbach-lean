import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceQFiniteTelescoping

/-!
# Finite-prefix closure of Suzuki Proposition 11.8 at `κ = 1`

This module independently closes the source-pairing route through genuine finite
prefixes.  The finite weighted DDE is integrated on the two smooth pieces around
`s = 3`; the terminal layer is then removed by dominated convergence, and the
finite pairings converge to the genuine source pairing.
-/

open scoped Classical BigOperators Interval ENNReal
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- At every fixed point, the genuine finite source prefixes converge to the
actual source `Q`. -/
theorem tendsto_suzukiProposition118SourceQPrefix
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) (s : ℝ) :
    Tendsto (fun m => suzukiProposition118SourceQPrefix m s) atTop
      (𝓝 (suzukiProposition118SourceQ s)) := by
  by_cases hs : s < 2
  · rw [suzukiProposition118SourceQ, if_pos hs]
    have h := (tendsto_suzukiFiniteLowerAmplitude hH).div_const s
    apply h.congr'
    filter_upwards [] with m
    rw [suzukiProposition118SourceQPrefix, if_pos hs]
  · have hs2 : 2 ≤ s := le_of_not_gt hs
    rw [suzukiProposition118SourceQ, if_neg hs]
    have hp :=
      (summable_suzukiProposition118SourceTPlus_of_sourceContract hH
        (by linarith : 1 < s)).hasSum.tendsto_sum_nat
    have hm :=
      (summable_suzukiProposition118SourceTMinus_of_sourceContract hH hs2).hasSum.tendsto_sum_nat
    have hadd := hp.add hm
    apply hadd.congr'
    filter_upwards [] with m
    simp only [suzukiProposition118SourceQPrefix, if_neg hs,
      suzukiOddSourceUpperPartialSum, suzukiEvenSourceLowerPartialSum]

/-- Every finite source prefix is continuous on the closed series range. -/
theorem continuousOn_suzukiProposition118SourceQPrefix_Ici (m : ℕ) :
    ContinuousOn (suzukiProposition118SourceQPrefix m) (Ici 2) := by
  have hlayer : ∀ n : ℕ, ContinuousOn (suzukiLayer 1 2 n) (Ici 2) := by
    intro n
    have hreg := (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) n).continuous
    have hsub : Ici (2 : ℝ) ⊆ KappaOneModel.closedDomain 2 n := by
      intro s hs
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici] at hs ⊢
      have heps : KappaOneModel.eps n ≤ 1 := by
        unfold KappaOneModel.eps
        omega
      have : (2 : ℝ) - KappaOneModel.eps n ≤ 2 := by
        exact sub_le_self 2 (Nat.cast_nonneg _)
      linarith
    exact (hreg.mono hsub).congr fun s _ =>
      (KappaOneModel.layer_eq_suzukiLayer 2 n s).symm
  have hodd : ContinuousOn (suzukiOddSourceUpperPartialSum m) (Ici 2) := by
    unfold suzukiOddSourceUpperPartialSum
    fun_prop
  have heven : ContinuousOn (suzukiEvenSourceLowerPartialSum m) (Ici 2) := by
    unfold suzukiEvenSourceLowerPartialSum
    fun_prop
  apply (hodd.add heven).congr
  intro s hs
  rw [suzukiProposition118SourceQPrefix, if_neg (not_lt.mpr hs)]
  rfl

/-- On the series range the finite prefix is nonnegative and lies below the
actual source series. -/
theorem suzukiProposition118SourceQPrefix_nonneg_le
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (m : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ suzukiProposition118SourceQPrefix m s ∧
      suzukiProposition118SourceQPrefix m s ≤ suzukiProposition118SourceQ s := by
  have hs1 : 1 < s := by linarith
  have hp0 : ∀ k, 0 ≤ suzukiLayer 1 2 (2 * k + 1) s :=
    suzukiLayer_one_two_odd_nonneg hs1
  have hm0 : ∀ k, 0 ≤ suzukiLayer 1 2 (2 * (k + 1)) s :=
    fun k => suzukiLayer_one_two_even_nonneg hs k
  have hps := summable_suzukiProposition118SourceTPlus_of_sourceContract hH hs1
  have hms := summable_suzukiProposition118SourceTMinus_of_sourceContract hH hs
  rw [suzukiProposition118SourceQPrefix, if_neg (not_lt.mpr hs),
    suzukiProposition118SourceQ, if_neg (not_lt.mpr hs)]
  constructor
  · exact add_nonneg (Finset.sum_nonneg fun k _ => hp0 k)
      (Finset.sum_nonneg fun k _ => hm0 k)
  · exact add_le_add
      (hps.sum_le_tsum (Finset.range m) (fun k _ => hp0 k))
      (hms.sum_le_tsum (Finset.range m) (fun k _ => hm0 k))

/-- For every fixed pairing coordinate `y ≥ 3`, finite-prefix pairings converge
pointwise to the genuine source pairing.  The moving integral is passed to the
limit on its compact window by domination from the source/hat comparison. -/
theorem tendsto_suzukiProposition118SourceQPrefix_pairing
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {y : ℝ} (hy : 3 ≤ y) :
    Tendsto
      (fun m => section10SignedPairing 1
        (suzukiProposition118SourceQPrefix m)
        suzukiProposition118KappaOneSourceAdjoint y)
      atTop (𝓝 (suzukiProposition118SourceQPairing y)) := by
  let S : Set ℝ := Ioc (y - 1) y
  obtain ⟨C, hC, hQ⟩ := suzukiProposition118SourceQ_nonneg_and_le_hat hH
  let G : ℝ → ℝ := fun t => |t| *
    (C * t * (H.T .plus t + H.T .minus t))
  have hSsub : S ⊆ Icc (y - 1) y := Ioc_subset_Icc_self
  have hpos : Icc (y - 1) y ⊆ Ioi (0 : ℝ) := by
    intro t ht
    simp only [Set.mem_Icc, Set.mem_Ioi] at ht ⊢
    linarith [ht.1]
  have hpcont : ContinuousOn (H.T .plus) (Icc (y - 1) y) :=
    (hH.toSection13HatContract.continuous .plus).mono hpos
  have hmcont : ContinuousOn (H.T .minus) (Icc (y - 1) y) :=
    (hH.toSection13HatContract.continuous .minus).mono hpos
  have hGcont : ContinuousOn G (Icc (y - 1) y) := by
    dsimp [G]
    fun_prop
  have hGintOn : IntegrableOn G S volume :=
    hGcont.integrableOn_Icc.mono_set hSsub
  have hmeas : ∀ m : ℕ, AEStronglyMeasurable
      (fun t => suzukiProposition118KappaOneSourceAdjoint (t + 1) *
        suzukiProposition118SourceQPrefix m t) (volume.restrict S) := by
    intro m
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ((continuous_id.add continuous_const).sub continuous_const).continuousOn.mul
    exact (continuousOn_suzukiProposition118SourceQPrefix_Ici m).mono fun t ht => by
      change 2 ≤ t
      linarith [ht.1]
  have hbound : ∀ m : ℕ, ∀ᵐ t ∂volume.restrict S,
      ‖suzukiProposition118KappaOneSourceAdjoint (t + 1) *
        suzukiProposition118SourceQPrefix m t‖ ≤ G t := by
    intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht2 : 2 ≤ t := by
      dsimp [S] at ht
      linarith [ht.1]
    rcases suzukiProposition118SourceQPrefix_nonneg_le hH m ht2 with ⟨hpre0, hpreQ⟩
    rcases hQ t ht2 with ⟨hQ0, hQle⟩
    have ht0 : 0 ≤ t := by linarith
    have hmaj0 : 0 ≤ C * t * (H.T .plus t + H.T .minus t) :=
      le_trans hQ0 hQle
    rw [suzukiProposition118KappaOneSourceAdjoint]
    norm_num only [add_sub_cancel_right]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 hpre0)]
    dsimp [G]
    rw [abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_left (hpreQ.trans hQle) ht0
  have hlim : ∀ᵐ t ∂volume.restrict S,
      Tendsto
        (fun m => suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQPrefix m t)
        atTop
        (𝓝 (suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQ t)) := by
    filter_upwards [] with t
    exact tendsto_const_nhds.mul (tendsto_suzukiProposition118SourceQPrefix hH t)
  have hint := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict S) G hmeas hGintOn hbound hlim
  have hint' : Tendsto
      (fun m => ∫ t in y - 1..y,
        suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQPrefix m t)
      atTop
      (𝓝 (∫ t in y - 1..y,
        suzukiProposition118KappaOneSourceAdjoint (t + 1) *
          suzukiProposition118SourceQ t)) := by
    simpa only [intervalIntegral.integral_of_le (by linarith : y - 1 ≤ y), S] using hint
  have hpoint : Tendsto
      (fun m => y * suzukiProposition118KappaOneSourceAdjoint y *
        suzukiProposition118SourceQPrefix m y)
      atTop
      (𝓝 (y * suzukiProposition118KappaOneSourceAdjoint y *
        suzukiProposition118SourceQ y)) :=
    (tendsto_const_nhds.mul tendsto_const_nhds).mul
      (tendsto_suzukiProposition118SourceQPrefix hH y)
  have hall := hpoint.sub hint'
  change Tendsto
    (fun m => section10SignedPairing 1
      (suzukiProposition118SourceQPrefix m)
      suzukiProposition118KappaOneSourceAdjoint y)
    atTop
    (𝓝 (section10SignedPairing 1 suzukiProposition118SourceQ
      suzukiProposition118KappaOneSourceAdjoint y))
  simpa only [section10SignedPairing, one_mul] using hall

end MathlibNt.SieveTheory
