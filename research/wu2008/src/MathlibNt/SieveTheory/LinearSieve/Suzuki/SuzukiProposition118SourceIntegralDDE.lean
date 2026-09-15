import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceTailPairingZero
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceQFinitePrefixClosure
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion

/-!
# Integral DDE for the genuine Proposition 11.8 source

This module derives the integral delay equation directly from Suzuki's finite
continuous-layer recursion, and then feeds it to the Section-10 Iwaniec pairing.
No DDE or pairing conclusion is assumed.
-/

open scoped Classical BigOperators Interval ENNReal
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Above its parity threshold, a recursive source layer has the unclipped
integral representation.  The integrand vanishes beyond the nominal upper
endpoint, so this remains true when `s` itself is beyond that endpoint. -/
private theorem weighted_suzukiLayer_eq_integral_to_upper
    {β s : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hs : β + sourceEpsilon n ≤ s) :
    s * suzukiLayer 1 β n s =
      ∫ t in s..(β + n), suzukiLayer 1 β (n - 1) (t - 1) := by
  exact suzukiLayer_weighted_eq_integral_to_upper hβ hn hs

/-- Termwise finite-layer integral recurrence on a common parity threshold. -/
private theorem weighted_suzukiLayer_sub
    {β x y : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hx : β + sourceEpsilon n ≤ x) (hxy : x ≤ y) :
    y * suzukiLayer 1 β n y - x * suzukiLayer 1 β n x =
      -(∫ t in x..y, suzukiLayer 1 β (n - 1) (t - 1)) := by
  have hy : β + sourceEpsilon n ≤ y := hx.trans hxy
  rw [weighted_suzukiLayer_eq_integral_to_upper hβ hn hy,
    weighted_suzukiLayer_eq_integral_to_upper hβ hn hx]
  have intervalIntegrable_of_threshold : ∀ {a b : ℝ},
      β + sourceEpsilon n ≤ a → β + sourceEpsilon n ≤ b →
      IntervalIntegrable (fun t => suzukiLayer 1 β (n - 1) (t - 1))
        volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    have hm : ContinuousOn
        (fun t => KappaOneModel.layer β (n - 1) (t - 1)) (Set.uIcc a b) := by
      apply (KappaOneModel.regular hβ (n - 1)).continuous.comp
        (continuous_id.sub continuous_const).continuousOn
      intro t ht
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici]
      have hpar : n % 2 + (n - 1) % 2 = 1 := by omega
      have hparR : ((n % 2 : ℕ) : ℝ) + ((n - 1) % 2 : ℕ) = 1 := by
        exact_mod_cast hpar
      have ha' : β + (n % 2 : ℕ) ≤ a := by simpa [sourceEpsilon] using ha
      have hb' : β + (n % 2 : ℕ) ≤ b := by simpa [sourceEpsilon] using hb
      have htLower : β + (n % 2 : ℕ) ≤ t := by
        rw [Set.mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ha'.trans ht.1
        · exact hb'.trans ht.1
      dsimp
      linarith
    exact hm.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer β (n - 1) (t - 1)).symm
  have hb : β + sourceEpsilon n ≤ β + n := by
    have heps : sourceEpsilon n ≤ n := by unfold sourceEpsilon; omega
    have hepsR : (sourceEpsilon n : ℝ) ≤ (n : ℝ) := by exact_mod_cast heps
    linarith
  have hxi := intervalIntegrable_of_threshold hx hb
  have hyi := intervalIntegrable_of_threshold hy hb
  have hxyi := intervalIntegrable_of_threshold hx hy
  have hadd := intervalIntegral.integral_add_adjacent_intervals hxyi hyi
  linarith

/-- Nonnegative Tonelli/`tsum` exchange on an oriented compact interval.  The
summability hypothesis is on the (nonnegative) layer integrals themselves. -/
private theorem intervalIntegral_tsum_of_nonneg
    {f : ℕ → ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hint : ∀ k, IntervalIntegrable (f k) volume x y)
    (hnonneg : ∀ k, ∀ t ∈ Set.Icc x y, 0 ≤ f k t)
    (hsum : Summable (fun k => ∫ t in x..y, f k t)) :
    (∫ t in x..y, ∑' k, f k t) = ∑' k, ∫ t in x..y, f k t := by
  let g : ℕ → ℝ → ℝ := fun k => (Set.Ioc x y).indicator (f k)
  have hgint : ∀ k, Integrable (g k) volume := by
    intro k
    simpa [g] using (hint k).1.integrable_indicator measurableSet_Ioc
  have hgmeas : ∀ k, AEStronglyMeasurable (g k) volume :=
    fun k => (hgint k).aestronglyMeasurable
  have hg0 : ∀ k, 0 ≤ᵐ[volume] g k := by
    intro k
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Ioc x y
    · simp [g, ht, hnonneg k t ⟨ht.1.le, ht.2⟩]
    · simp [g, ht]
  have hint0 : ∀ k, 0 ≤ ∫ t in x..y, f k t := by
    intro k
    exact intervalIntegral.integral_nonneg hxy (hnonneg k)
  have hlin : ∀ k, (∫⁻ t, ‖g k t‖ₑ ∂volume) =
      ENNReal.ofReal (∫ t in x..y, f k t) := by
    intro k
    have hof := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hgint k) (hg0 k)
    rw [MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hxy] at hof
    calc
      (∫⁻ t, ‖g k t‖ₑ ∂volume) = ∫⁻ t, ENNReal.ofReal (g k t) ∂volume := by
        apply lintegral_congr
        intro t
        have ht0 : 0 ≤ g k t := by
          by_cases ht : t ∈ Set.Ioc x y
          · simp [g, ht, hnonneg k t ⟨ht.1.le, ht.2⟩]
          · simp [g, ht]
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg ht0]
      _ = ENNReal.ofReal (∫ t in x..y, f k t) := hof.symm
  have hlinTop : ∑' k, ∫⁻ t, ‖g k t‖ₑ ∂volume ≠ ∞ := by
    rw [show (∑' k, ∫⁻ t, ‖g k t‖ₑ ∂volume) =
        ∑' k, ENNReal.ofReal (∫ t in x..y, f k t) by
      congr 1
      funext k
      exact hlin k]
    rw [← ENNReal.ofReal_tsum_of_nonneg hint0 hsum]
    exact ENNReal.ofReal_ne_top
  have htonelli := MeasureTheory.integral_tsum hgmeas hlinTop
  rw [intervalIntegral.integral_of_le hxy]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  calc
    (∫ t, (Set.Ioc x y).indicator (fun t => ∑' k, f k t) t ∂volume) =
        ∫ t, ∑' k, g k t ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Set.Ioc x y
      · simp [g, ht]
      · simp [g, ht]
    _ = ∑' k, ∫ t, g k t ∂volume := htonelli
    _ = ∑' k, ∫ t in x..y, f k t := by
      congr 1
      funext k
      rw [show g k = (Set.Ioc x y).indicator (f k) by rfl,
        MeasureTheory.integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hxy]

/-- The even source series is the integral primitive of the shifted odd series.
This is the infinite-layer form of the finite `(9.2)` recurrence. -/
theorem suzukiProposition118SourceTMinus_weighted_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    y * suzukiProposition118SourceTMinus y -
        x * suzukiProposition118SourceTMinus x =
      -(∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) := by
  have hy : 2 ≤ y := hx.trans hxy
  have hxsum := summable_suzukiProposition118SourceTMinus_of_sourceContract hH hx
  have hysum := summable_suzukiProposition118SourceTMinus_of_sourceContract hH hy
  let f : ℕ → ℝ → ℝ := fun k t => suzukiLayer 1 2 (2 * k + 1) (t - 1)
  have hterm : ∀ k,
      y * suzukiLayer 1 2 (2 * (k + 1)) y -
          x * suzukiLayer 1 2 (2 * (k + 1)) x =
        -(∫ t in x..y, f k t) := by
    intro k
    have h :=
      weighted_suzukiLayer_sub (β := (2 : ℝ)) (n := 2 * (k + 1))
        (by norm_num) (by omega) (by norm_num; exact hx) hxy
    change y * suzukiLayer 1 2 (2 * (k + 1)) y -
        x * suzukiLayer 1 2 (2 * (k + 1)) x =
      -(∫ t in x..y, suzukiLayer 1 2 (2 * k + 1) (t - 1))
    have hk : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    simpa only [hk] using h
  have hint : ∀ k, IntervalIntegrable (f k) volume x y := by
    intro k
    apply ContinuousOn.intervalIntegrable
    have hm : ContinuousOn
        (fun t => KappaOneModel.layer 2 (2 * k + 1) (t - 1)) (Set.uIcc x y) := by
      apply (KappaOneModel.regular (by norm_num) (2 * k + 1)).continuous.comp
        (continuous_id.sub continuous_const).continuousOn
      intro t ht
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici]
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> norm_num at * <;> linarith
    exact hm.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer 2 (2 * k + 1) (t - 1)).symm
  have hnonneg : ∀ k, ∀ t ∈ Set.Icc x y, 0 ≤ f k t := by
    intro k t ht
    rw [show f k t = KappaOneModel.layer 2 (2 * k + 1) (t - 1) by
      exact (KappaOneModel.layer_eq_suzukiLayer 2 (2 * k + 1) (t - 1)).symm]
    apply (KappaOneModel.regular (by norm_num) (2 * k + 1)).nonneg
    unfold KappaOneModel.closedDomain KappaOneModel.eps
    simp only [Set.mem_Ici]
    norm_num
    linarith [ht.1]
  have hsumInt : Summable (fun k => ∫ t in x..y, f k t) := by
    have hd := (Summable.mul_left y hysum).sub (Summable.mul_left x hxsum)
    have hn := hd.neg
    exact hn.congr fun k => by rw [hterm k]; simp
  have hswap := intervalIntegral_tsum_of_nonneg hxy hint hnonneg hsumInt
  calc
    y * suzukiProposition118SourceTMinus y -
        x * suzukiProposition118SourceTMinus x =
        ∑' k, (y * suzukiLayer 1 2 (2 * (k + 1)) y -
          x * suzukiLayer 1 2 (2 * (k + 1)) x) := by
      rw [suzukiProposition118SourceTMinus, suzukiProposition118SourceTMinus,
        ← tsum_mul_left, ← tsum_mul_left,
        ← (Summable.mul_left y hysum).tsum_sub (Summable.mul_left x hxsum)]
    _ = ∑' k, -(∫ t in x..y, f k t) := tsum_congr hterm
    _ = -(∑' k, ∫ t in x..y, f k t) := tsum_neg
    _ = -(∫ t in x..y, ∑' k, f k t) := by rw [hswap]
    _ = -(∫ t in x..y, suzukiProposition118SourceTPlus (t - 1)) := by
      simp [f, suzukiProposition118SourceTPlus]

/-- Above the first odd threshold, the odd source series is the integral
primitive of the shifted even source series. -/
theorem suzukiProposition118SourceTPlus_weighted_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    y * suzukiProposition118SourceTPlus y -
        x * suzukiProposition118SourceTPlus x =
      -(∫ t in x..y, suzukiProposition118SourceTMinus (t - 1)) := by
  have hy : 3 ≤ y := hx.trans hxy
  have hxsum := summable_suzukiProposition118SourceTPlus_of_sourceContract hH
    (by linarith : 1 < x)
  have hysum := summable_suzukiProposition118SourceTPlus_of_sourceContract hH
    (by linarith : 1 < y)
  have htailx : Summable (fun k => suzukiLayer 1 2 (2 * (k + 1) + 1) x) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hxsum.comp_injective (i := fun k : ℕ => k + 1)
        (by intro a b hab; exact Nat.add_right_cancel hab)
  have htaily : Summable (fun k => suzukiLayer 1 2 (2 * (k + 1) + 1) y) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hysum.comp_injective (i := fun k : ℕ => k + 1)
        (by intro a b hab; exact Nat.add_right_cancel hab)
  let f : ℕ → ℝ → ℝ := fun k t => suzukiLayer 1 2 (2 * (k + 1)) (t - 1)
  have hterm : ∀ k,
      y * suzukiLayer 1 2 (2 * k + 3) y -
          x * suzukiLayer 1 2 (2 * k + 3) x =
        -(∫ t in x..y, f k t) := by
    intro k
    have h :=
      weighted_suzukiLayer_sub (β := (2 : ℝ)) (n := 2 * k + 3)
        (by norm_num) (by omega) (by
          have heps : sourceEpsilon (2 * k + 3) = 1 := by
            unfold sourceEpsilon
            omega
          rw [heps]
          norm_num
          exact hx) hxy
    change y * suzukiLayer 1 2 (2 * k + 3) y -
        x * suzukiLayer 1 2 (2 * k + 3) x =
      -(∫ t in x..y, suzukiLayer 1 2 (2 * (k + 1)) (t - 1))
    have hk : 2 * k + 3 - 1 = 2 * (k + 1) := by omega
    simpa only [hk] using h
  have hint : ∀ k, IntervalIntegrable (f k) volume x y := by
    intro k
    apply ContinuousOn.intervalIntegrable
    have hm : ContinuousOn
        (fun t => KappaOneModel.layer 2 (2 * (k + 1)) (t - 1)) (Set.uIcc x y) := by
      apply (KappaOneModel.regular (by norm_num) (2 * (k + 1))).continuous.comp
        (continuous_id.sub continuous_const).continuousOn
      intro t ht
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici]
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> norm_num at * <;> linarith
    exact hm.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer 2 (2 * (k + 1)) (t - 1)).symm
  have hnonneg : ∀ k, ∀ t ∈ Set.Icc x y, 0 ≤ f k t := by
    intro k t ht
    rw [show f k t = KappaOneModel.layer 2 (2 * (k + 1)) (t - 1) by
      exact (KappaOneModel.layer_eq_suzukiLayer 2 (2 * (k + 1)) (t - 1)).symm]
    apply (KappaOneModel.regular (by norm_num) (2 * (k + 1))).nonneg
    unfold KappaOneModel.closedDomain KappaOneModel.eps
    simp only [Set.mem_Ici]
    norm_num
    linarith [ht.1]
  have hsumInt : Summable (fun k => ∫ t in x..y, f k t) := by
    have hd := (Summable.mul_left y htaily).sub (Summable.mul_left x htailx)
    have hn := hd.neg
    exact hn.congr fun k => by
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, hterm k]
      simp
  have hswap := intervalIntegral_tsum_of_nonneg hxy hint hnonneg hsumInt
  have hxbase : suzukiLayer 1 2 1 x = 0 :=
    suzukiLayer_eq_zero_of_le 1 2 1 (by norm_num; exact hx)
  have hybase : suzukiLayer 1 2 1 y = 0 :=
    suzukiLayer_eq_zero_of_le 1 2 1 (by norm_num; exact hy)
  have hxtail :
      (∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) x) =
        ∑' k : ℕ, suzukiLayer 1 2 (2 * (k + 1) + 1) x := by
    have h := hxsum.sum_add_tsum_nat_add 1
    simpa [hxbase, Nat.add_comm] using h.symm
  have hytail :
      (∑' k : ℕ, suzukiLayer 1 2 (2 * k + 1) y) =
        ∑' k : ℕ, suzukiLayer 1 2 (2 * (k + 1) + 1) y := by
    have h := hysum.sum_add_tsum_nat_add 1
    simpa [hybase, Nat.add_comm] using h.symm
  calc
    y * suzukiProposition118SourceTPlus y -
        x * suzukiProposition118SourceTPlus x =
        ∑' k, (y * suzukiLayer 1 2 (2 * (k + 1) + 1) y -
          x * suzukiLayer 1 2 (2 * (k + 1) + 1) x) := by
      rw [suzukiProposition118SourceTPlus, suzukiProposition118SourceTPlus]
      rw [hytail, hxtail]
      rw [← tsum_mul_left, ← tsum_mul_left,
        ← (Summable.mul_left y htaily).tsum_sub (Summable.mul_left x htailx)]
    _ = ∑' k, -(∫ t in x..y, f k t) := by
      apply tsum_congr
      intro k
      simpa only [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] using hterm k
    _ = -(∑' k, ∫ t in x..y, f k t) := tsum_neg
    _ = -(∫ t in x..y, ∑' k, f k t) := by rw [hswap]
    _ = -(∫ t in x..y, suzukiProposition118SourceTMinus (t - 1)) := by
      simp [f, suzukiProposition118SourceTMinus]

/-- On the first source strip, the initial history and the odd amplitude
identity combine with the even recurrence to give the full source equation. -/
private theorem suzukiProposition118SourceQ_weighted_sub_of_le_three
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    y * suzukiProposition118SourceQ y - x * suzukiProposition118SourceQ x =
      -(∫ t in x..y, suzukiProposition118SourceQ (t - 1)) := by
  let A : ℝ := SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude
  let g : ℝ → ℝ := fun t => A / (t - 1)
  have hplusx := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
    (s := x) (by linarith : 1 < x) (hxy.trans hy)
  have hplusy := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
    (s := y) (by linarith : 1 < y) hy
  have hminus := suzukiProposition118SourceTMinus_weighted_sub hH hx hxy
  have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (μ := volume) (2 : ℝ))
  have hne3 : ∀ᵐ t : ℝ ∂volume, t ≠ 3 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (μ := volume) (3 : ℝ))
  have hQae : ∀ᵐ t : ℝ ∂volume, t ∈ Ι x y →
      suzukiProposition118SourceQ (t - 1) = g t := by
    filter_upwards [hne2, hne3] with t ht2 ht3
    intro ht
    rw [uIoc_of_le hxy] at ht
    have hu1 : 1 < t - 1 := by
      have hxt : x < t := ht.1
      exact lt_of_le_of_ne (by linarith : 1 ≤ t - 1)
        (fun heq => ht2 (by linarith))
    have hu2 : t - 1 < 2 := by
      have hty : t ≤ y := ht.2
      exact lt_of_le_of_ne (by linarith : t - 1 ≤ 2)
        (fun heq => ht3 (by linarith))
    rw [suzukiProposition118SourceQ, if_pos hu2]
  have hPlusAe : ∀ᵐ t : ℝ ∂volume, t ∈ Ι x y →
      suzukiProposition118SourceTPlus (t - 1) = g t - 1 := by
    filter_upwards [hne2, hne3] with t ht2 ht3
    intro ht
    rw [uIoc_of_le hxy] at ht
    have hu1 : 1 < t - 1 := by
      exact lt_of_le_of_ne (by linarith [ht.1] : 1 ≤ t - 1)
        (fun heq => ht2 (by linarith))
    have hu2 : t - 1 < 2 := by
      exact lt_of_le_of_ne (by linarith [ht.2] : t - 1 ≤ 2)
        (fun heq => ht3 (by linarith))
    have hp := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH
      (s := t - 1) hu1 (by linarith : t - 1 ≤ 3)
    dsimp [g, A]
    field_simp [ne_of_gt (by linarith : 0 < t - 1)]
    linarith
  have hgcont : ContinuousOn g (Set.uIcc x y) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    have htx : x ≤ t := ht.1
    change t - 1 ≠ 0
    exact ne_of_gt (by linarith)
  have hgint : IntervalIntegrable g volume x y := hgcont.intervalIntegrable
  have hgsubint : IntervalIntegrable (fun t => g t - 1) volume x y :=
    hgint.sub intervalIntegrable_const
  have hPlusInt : IntervalIntegrable
      (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y := by
    apply hgsubint.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    exact hPlusAe.mono fun t ht hmem => (ht hmem).symm
  have hQIntegral :
      (∫ t in x..y, suzukiProposition118SourceQ (t - 1)) =
        (y - x) + ∫ t in x..y, suzukiProposition118SourceTPlus (t - 1) := by
    rw [intervalIntegral.integral_congr_ae hQae]
    have hadd := intervalIntegral.integral_add
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => suzukiProposition118SourceTPlus (t - 1))
      intervalIntegrable_const hPlusInt
    have hsum :
        (∫ t in x..y, (1 : ℝ) + suzukiProposition118SourceTPlus (t - 1)) =
          ∫ t in x..y, g t := by
      apply intervalIntegral.integral_congr_ae
      exact hPlusAe.mono fun t ht hmem => by rw [ht hmem]; ring
    rw [hsum] at hadd
    simpa using hadd
  have hQx : suzukiProposition118SourceQ x =
      suzukiProposition118SourceTPlus x + suzukiProposition118SourceTMinus x := by
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr hx)]
  have hQy : suzukiProposition118SourceQ y =
      suzukiProposition118SourceTPlus y + suzukiProposition118SourceTMinus y := by
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr (hx.trans hxy))]
  rw [hQx, hQy, hQIntegral]
  linarith

/-- The genuine source is interval-integrable on every compact subinterval of
its series range.  Measurability comes directly from the two layer `tsum`s;
the production hat comparison supplies a continuous compact majorant. -/
theorem suzukiProposition118SourceQ_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable suzukiProposition118SourceQ volume x y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy]
  obtain ⟨C, hC, hQ⟩ := suzukiProposition118SourceQ_nonneg_and_le_hat hH
  let G : ℝ → ℝ := fun s => C * s * (H.T .plus s + H.T .minus s)
  have hpos : Icc x y ⊆ Ioi (0 : ℝ) := by
    intro s hs
    simp only [Set.mem_Icc, Set.mem_Ioi] at hs ⊢
    linarith [hs.1]
  have hGcont : ContinuousOn G (Icc x y) := by
    dsimp [G]
    have hp := (hH.toSection13HatContract.continuous .plus).mono hpos
    have hm := (hH.toSection13HatContract.continuous .minus).mono hpos
    fun_prop
  have hlayer : ∀ n : ℕ, AEStronglyMeasurable (suzukiLayer 1 2 n)
      (volume.restrict (Icc x y)) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
    have hreg := (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) n).continuous
    have hsub : Icc x y ⊆ KappaOneModel.closedDomain 2 n := by
      intro s hs
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici, Set.mem_Icc] at hs ⊢
      have heps : KappaOneModel.eps n ≤ 1 := by
        unfold KappaOneModel.eps
        omega
      have : (2 : ℝ) - KappaOneModel.eps n ≤ 2 :=
        sub_le_self 2 (Nat.cast_nonneg _)
      linarith [hs.1]
    exact (hreg.mono hsub).congr fun s _ =>
      (KappaOneModel.layer_eq_suzukiLayer 2 n s).symm
  have hmeasSeries : AEStronglyMeasurable
      (fun s => suzukiProposition118SourceTPlus s +
        suzukiProposition118SourceTMinus s)
      (volume.restrict (Icc x y)) := by
    apply AEStronglyMeasurable.add
    · exact AEStronglyMeasurable.tsum (fun k => hlayer (2 * k + 1))
    · exact AEStronglyMeasurable.tsum (fun k => hlayer (2 * (k + 1)))
  have hmeasQ : AEStronglyMeasurable suzukiProposition118SourceQ
      (volume.restrict (Icc x y)) := by
    apply hmeasSeries.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr (hx.trans hs.1))]
  apply Integrable.mono' hGcont.integrableOn_Icc hmeasQ
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rcases hQ s (hx.trans hs.1) with ⟨hQ0, hQle⟩
  rw [Real.norm_eq_abs, abs_of_nonneg hQ0]
  exact hQle

/-- Above the first odd threshold, adding the two parity recurrences gives the
full source integral delay equation. -/
private theorem suzukiProposition118SourceQ_weighted_sub_of_three_le
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    y * suzukiProposition118SourceQ y - x * suzukiProposition118SourceQ x =
      -(∫ t in x..y, suzukiProposition118SourceQ (t - 1)) := by
  have hm := suzukiProposition118SourceTMinus_weighted_sub hH (by linarith : 2 ≤ x) hxy
  have hp := suzukiProposition118SourceTPlus_weighted_sub hH hx hxy
  have hmi := suzukiProposition118SourceQ_intervalIntegrable hH
    (x := x - 1) (y := y - 1) (by linarith) (by linarith)
  have hQi : IntervalIntegrable (fun t => suzukiProposition118SourceQ (t - 1)) volume x y := by
    convert hmi.comp_sub_right 1 using 1 <;> ring
  have hlayer : ∀ n : ℕ, AEStronglyMeasurable
      (fun t => suzukiLayer 1 2 n (t - 1)) (volume.restrict (Set.uIoc x y)) := by
    intro n
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    have hreg := (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) n).continuous
    have hshiftcont : Continuous (fun t : ℝ => t - 1) :=
      continuous_id.sub continuous_const
    have hmodel : ContinuousOn
        (fun t => KappaOneModel.layer 2 n (t - 1)) (Set.uIoc x y) := by
      apply hreg.comp hshiftcont.continuousOn
      intro t ht
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [Set.mem_Ici]
      rw [Set.mem_uIoc] at ht
      rcases ht with ht | ht <;> linarith
    exact hmodel.congr fun t _ =>
      (KappaOneModel.layer_eq_suzukiLayer 2 n (t - 1)).symm
  have hpmeas : AEStronglyMeasurable
      (fun t => suzukiProposition118SourceTPlus (t - 1))
      (volume.restrict (Set.uIoc x y)) := by
    exact AEStronglyMeasurable.tsum (fun k => hlayer (2 * k + 1))
  have hpint : IntervalIntegrable
      (fun t => suzukiProposition118SourceTPlus (t - 1)) volume x y := by
    apply hQi.mono_fun hpmeas
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    have hp0 : 0 ≤ suzukiProposition118SourceTPlus (t - 1) := by
      rw [suzukiProposition118SourceTPlus]
      exact tsum_nonneg (suzukiLayer_one_two_odd_nonneg (by linarith : 1 < t - 1))
    have hm0 : 0 ≤ suzukiProposition118SourceTMinus (t - 1) := by
      rw [suzukiProposition118SourceTMinus]
      exact tsum_nonneg (fun k => suzukiLayer_one_two_even_nonneg ht2 k)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0]
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2), abs_of_nonneg (add_nonneg hp0 hm0)]
    linarith
  have hmint : IntervalIntegrable
      (fun t => suzukiProposition118SourceTMinus (t - 1)) volume x y := by
    apply (hQi.sub hpint).congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.mem_uIoc] at ht
    have ht2 : 2 ≤ t - 1 := by rcases ht with ht | ht <;> linarith
    change suzukiProposition118SourceQ (t - 1) -
      suzukiProposition118SourceTPlus (t - 1) = suzukiProposition118SourceTMinus (t - 1)
    rw [suzukiProposition118SourceQ, if_neg (not_lt.mpr ht2), add_sub_cancel_left]
  have hQeq : ∀ t ∈ Set.uIcc x y,
      suzukiProposition118SourceQ (t - 1) =
        suzukiProposition118SourceTPlus (t - 1) +
          suzukiProposition118SourceTMinus (t - 1) := by
    intro t ht
    rw [suzukiProposition118SourceQ, if_neg]
    rw [Set.mem_uIcc] at ht
    rcases ht with ht | ht <;> linarith
  rw [show suzukiProposition118SourceQ x =
      suzukiProposition118SourceTPlus x + suzukiProposition118SourceTMinus x by
        rw [suzukiProposition118SourceQ, if_neg (by linarith)],
    show suzukiProposition118SourceQ y =
      suzukiProposition118SourceTPlus y + suzukiProposition118SourceTMinus y by
        rw [suzukiProposition118SourceQ, if_neg (by linarith)],
    intervalIntegral.integral_congr hQeq,
    intervalIntegral.integral_add hpint hmint]
  linarith

/-- On the first strip the shifted source is the continuous initial-history
kernel almost everywhere, hence is interval-integrable. -/
private theorem suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 3) :
    IntervalIntegrable (fun t => suzukiProposition118SourceQ (t - 1)) volume x y := by
  let A : ℝ := SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude
  let g : ℝ → ℝ := fun t => A / (t - 1)
  have hgcont : ContinuousOn g (Set.uIcc x y) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    rw [uIcc_of_le hxy] at ht
    change t - 1 ≠ 0
    exact ne_of_gt (by linarith [ht.1])
  apply hgcont.intervalIntegrable.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hne2 : ∀ᵐ t : ℝ ∂volume, t ≠ 2 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (μ := volume) (2 : ℝ))
  have hne3 : ∀ᵐ t : ℝ ∂volume, t ≠ 3 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton (μ := volume) (3 : ℝ))
  filter_upwards [hne2, hne3] with t ht2 ht3
  intro ht
  rw [uIoc_of_le hxy] at ht
  have hu1 : 1 < t - 1 :=
    lt_of_le_of_ne (by linarith [ht.1] : 1 ≤ t - 1) (fun heq => ht2 (by linarith))
  have hu2 : t - 1 < 2 :=
    lt_of_le_of_ne (by linarith [ht.2] : t - 1 ≤ 2) (fun heq => ht3 (by linarith))
  rw [suzukiProposition118SourceQ, if_pos hu2]

/-- The direct finite-layer argument gives the source integral DDE on every
interval `2 ≤ x ≤ y`, including intervals crossing the kink at `3`. -/
theorem suzukiProposition118SourceQ_weighted_sub
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    y * suzukiProposition118SourceQ y - x * suzukiProposition118SourceQ x =
      -(∫ t in x..y, suzukiProposition118SourceQ (t - 1)) := by
  by_cases hy : y ≤ 3
  · exact suzukiProposition118SourceQ_weighted_sub_of_le_three hH hx hxy hy
  by_cases hx3 : 3 ≤ x
  · exact suzukiProposition118SourceQ_weighted_sub_of_three_le hH hx3 hxy
  have hxle3 : x ≤ 3 := le_of_not_ge hx3
  have h3y : 3 ≤ y := le_of_not_ge hy
  have hlo := suzukiProposition118SourceQ_weighted_sub_of_le_three hH hx hxle3 le_rfl
  have hhi := suzukiProposition118SourceQ_weighted_sub_of_three_le hH le_rfl h3y
  have hlowInt := suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three
    hx hxle3 le_rfl
  have hhighBase := suzukiProposition118SourceQ_intervalIntegrable hH
    (x := (2 : ℝ)) (y := y - 1) (by norm_num) (by linarith)
  have hhighInt : IntervalIntegrable
      (fun t => suzukiProposition118SourceQ (t - 1)) volume 3 y := by
    convert hhighBase.comp_sub_right 1 using 1 <;> ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals hlowInt hhighInt
  linarith

/-- The shifted source occurring in the DDE is interval-integrable on every
compact interval contained in `[2,∞)`. -/
theorem suzukiProposition118SourceQ_shift_intervalIntegrable
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiProposition118SourceQ (t - 1)) volume x y := by
  by_cases hy : y ≤ 3
  · exact suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three hx hxy hy
  by_cases hx3 : 3 ≤ x
  · have hbase := suzukiProposition118SourceQ_intervalIntegrable hH
      (x := x - 1) (y := y - 1) (by linarith) (by linarith)
    convert hbase.comp_sub_right 1 using 1 <;> ring
  · have hxle3 : x ≤ 3 := le_of_not_ge hx3
    have h3y : 3 ≤ y := le_of_not_ge hy
    exact (suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three
      hx hxle3 le_rfl).trans
      (by
        have hbase := suzukiProposition118SourceQ_intervalIntegrable hH
          (x := (2 : ℝ)) (y := y - 1) (by norm_num) (by linarith)
        convert hbase.comp_sub_right 1 using 1 <;> ring)

/-- The weighted source `s ↦ sQ(s)` is continuous on every compact interval
of the series range, directly from its integral DDE. -/
theorem continuousOn_weighted_suzukiProposition118SourceQ
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {M : ℝ} (hM : 2 ≤ M) :
    ContinuousOn (fun s => s * suzukiProposition118SourceQ s) (Icc 2 M) := by
  let f : ℝ → ℝ := fun t => suzukiProposition118SourceQ (t - 1)
  have hf := suzukiProposition118SourceQ_shift_intervalIntegrable hH
    (x := (2 : ℝ)) (y := M) (by norm_num) hM
  have hfOn : IntegrableOn f (Icc 2 M) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hM).1 hf
  have hprim := intervalIntegral.continuousOn_primitive hfOn
  have hcont : ContinuousOn
      (fun s => 2 * suzukiProposition118SourceQ 2 - ∫ t in Ioc 2 s, f t)
      (Icc 2 M) := continuousOn_const.sub hprim
  apply hcont.congr
  intro s hs
  have h2s : 2 ≤ s := hs.1
  have hdde := suzukiProposition118SourceQ_weighted_sub hH
    (x := (2 : ℝ)) (y := s) (by norm_num) h2s
  rw [intervalIntegral.integral_of_le h2s] at hdde
  dsimp [f]
  linarith

/-- Consequently the genuine source is continuous at every point strictly
above the lower boundary (on the series side of the possible boundary jump). -/
theorem continuousAt_suzukiProposition118SourceQ_of_two_lt
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 < s) : ContinuousAt suzukiProposition118SourceQ s := by
  have hW := continuousOn_weighted_suzukiProposition118SourceQ hH
    (M := s + 1) (by linarith)
  have hWAt := hW.continuousAt (Icc_mem_nhds hs (by linarith : s < s + 1))
  have hdiv := hWAt.div (continuousAt_id) (ne_of_gt (by linarith : 0 < s))
  apply hdiv.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (ne_of_gt (by linarith : 0 < s))] with u hu
  change suzukiProposition118SourceQ u =
    (u * suzukiProposition118SourceQ u) / u
  field_simp

/-- On the prescribed initial history, the source is continuous away from its
endpoints. -/
theorem continuousAt_suzukiProposition118SourceQ_of_one_lt_of_lt_two
    {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    ContinuousAt suzukiProposition118SourceQ s := by
  have hrat : ContinuousAt
      (fun u : ℝ => SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude / u) s :=
    continuousAt_const.div continuousAt_id (ne_of_gt (by linarith : 0 < s))
  apply hrat.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hs2] with u hu
  have hu' : u < 2 := hu
  rw [suzukiProposition118SourceQ, if_pos hu']

/-- The source itself is interval-integrable on compact intervals contained in
`(1,∞)`; the single switch point at `2` is harmless. -/
theorem suzukiProposition118SourceQ_intervalIntegrable_of_one_lt
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    IntervalIntegrable suzukiProposition118SourceQ volume x y := by
  by_cases hy : y ≤ 2
  · have hs := suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three
      (x := x + 1) (y := y + 1) (by linarith) (by linarith) (by linarith)
    convert hs.comp_add_right 1 using 1 <;> ring
  by_cases hx2 : 2 ≤ x
  · exact suzukiProposition118SourceQ_intervalIntegrable hH hx2 hxy
  · have hxle2 : x ≤ 2 := le_of_not_ge hx2
    have h2y : 2 ≤ y := le_of_not_ge hy
    have hloShift := suzukiProposition118SourceQ_shift_intervalIntegrable_of_le_three
      (x := x + 1) (y := (3 : ℝ)) (by linarith) (by linarith) le_rfl
    have hlo : IntervalIntegrable suzukiProposition118SourceQ volume x 2 := by
      convert hloShift.comp_add_right 1 using 1 <;> ring
    exact hlo.trans (suzukiProposition118SourceQ_intervalIntegrable hH le_rfl h2y)

/-- Away from the unique possible kink `s=3`, the integral DDE differentiates
to the weighted source equation `(sQ(s))'=-Q(s-1)`. -/
theorem hasDerivAt_weighted_suzukiProposition118SourceQ
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 2 < s) (hs3 : s ≠ 3) :
    HasDerivAt (fun u => u * suzukiProposition118SourceQ u)
      (-suzukiProposition118SourceQ (s - 1)) s := by
  let f : ℝ → ℝ := fun t => suzukiProposition118SourceQ (t - 1)
  have hf := suzukiProposition118SourceQ_shift_intervalIntegrable hH
    (x := (2 : ℝ)) (y := s) (by norm_num) hs.le
  have hfcont : ContinuousAt f s := by
    dsimp [f]
    by_cases hlt : s < 3
    · exact (continuousAt_suzukiProposition118SourceQ_of_one_lt_of_lt_two
        (by linarith) (by linarith)).comp
          ((hasDerivAt_id s).sub_const 1).continuousAt
    · exact (continuousAt_suzukiProposition118SourceQ_of_two_lt hH
      (by linarith [lt_of_le_of_ne (not_lt.mp hlt) hs3.symm])).comp
        ((hasDerivAt_id s).sub_const 1).continuousAt
  have hfmeas : StronglyMeasurableAtFilter f (𝓝 s) volume := by
    by_cases hlt : s < 3
    · apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (s := Ioo (2 : ℝ) 3) _ s ⟨hs, hlt⟩
      intro u hu
      dsimp [f]
      exact (continuousAt_suzukiProposition118SourceQ_of_one_lt_of_lt_two
        (by linarith [hu.1]) (by linarith [hu.2])).comp
          ((hasDerivAt_id u).sub_const 1).continuousAt
    · have h3s : 3 < s := lt_of_le_of_ne (not_lt.mp hlt) hs3.symm
      apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (s := Ioi (3 : ℝ)) _ s h3s
      intro u hu
      change 3 < u at hu
      dsimp [f]
      exact (continuousAt_suzukiProposition118SourceQ_of_two_lt hH
        (by linarith [hu])).comp ((hasDerivAt_id u).sub_const 1).continuousAt
  have hprim := intervalIntegral.integral_hasDerivAt_right hf hfmeas hfcont
  have hbase := hprim.neg.const_add ((2 : ℝ) * suzukiProposition118SourceQ 2)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have hdde := suzukiProposition118SourceQ_weighted_sub hH
    (x := (2 : ℝ)) (y := u) (by norm_num) hu.le
  dsimp [f]
  linarith

end MathlibNt.SieveTheory
