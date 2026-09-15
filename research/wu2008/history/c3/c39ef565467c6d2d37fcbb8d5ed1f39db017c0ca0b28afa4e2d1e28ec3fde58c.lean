import MathlibNt.Wu2008DoubleSieve.Gamma16MassCoordinates
import MathlibNt.Wu2008DoubleSieve.Gamma16IntegralIntegrability

/-! # Physical triple-plus-outer prime quadrature for the fourth row -/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Topology Interval

noncomputable def gamma16PrimeKernelSum (R φ : ℝ) : ℝ :=
  ∑ p ∈ gamma16MassPrimes R,
    gamma16Kernel φ (log p.2.1 / log R) (log p.2.2.1 / log R)
      (log p.2.2.2 / log R) (log p.1 / log R) /
      ((p.2.1 : ℝ) * p.2.2.1 * p.2.2.2 * p.1)

noncomputable def gamma16NestedPrimeSum (R φ : ℝ) : ℝ :=
  ∑ p4 ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta),
    primeOrderedTripleSum R gamma16Alpha (log p4 / log R)
      (gamma16ClippedKernel φ (log p4 / log R)) / p4

theorem gamma16_prime_sum_eq_nested {R : ℝ} (hR : 1 < R) (φ : ℝ) :
    gamma16PrimeKernelSum R φ = gamma16NestedPrimeSum R φ := by
  unfold gamma16PrimeKernelSum gamma16MassPrimes gamma16NestedPrimeSum
  rw [sum_sigma]
  apply sum_congr rfl
  intro p4 hp4
  have h4 := (mem_primesIcc (rpow_nonneg (by linarith) _)).mp hp4
  rw [sum_sigma, primeOrderedTripleSum, primeOrdered_coordinate_rpow hR h4.1,
    Finset.sum_div]
  apply sum_congr rfl
  intro p1 hp1
  rw [sum_sigma, Finset.sum_div]
  apply sum_congr rfl
  intro p2 hp2
  rw [Finset.sum_div]
  apply sum_congr rfl
  intro p3 hp3
  have hp : (⟨p4, p1, p2, p3⟩ : Gamma16MassTuple) ∈ gamma16MassPrimes R :=
    mem_sigma.mpr ⟨hp4, mem_sigma.mpr ⟨hp1, mem_sigma.mpr ⟨hp2, hp3⟩⟩⟩
  obtain ⟨ht, hu, hv, hw⟩ := gamma16_mass_coordinate_bounds hR hp
  dsimp only at ht hu hv hw ⊢
  rw [gamma16ClippedKernel, gamma16_clip_eq ht, gamma16_clip_eq hu,
    gamma16_clip_eq hv, gamma16_clip_eq hw]
  ring

theorem gamma16_prime_mass_eventually :
    ∀ᶠ R : ℝ in atTop,
      ∑ p ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p : ℝ) ≤ 5 := by
  filter_upwards [eventually_gt_atTop 1,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with R hR hs hD
  have h := (le_abs_self _).trans (primeOrdered_reciprocal_Icc_uniform_bound hR hs
    gamma16_constants.1 gamma16_constants.2.1 gamma16_constants.2.2.1)
  have hi := (primeOrdered_exponent_density_bounds
    gamma16_constants.1 gamma16_constants.2.1 gamma16_constants.2.2.1).2
  linarith

theorem gamma16_fourfold_prime_quadrature (P ε : ℝ) (hP : 2 ≤ P) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ φ : ℝ, 2 ≤ φ → φ ≤ P →
      |gamma16PrimeKernelSum R φ - gamma16FourthIntegral φ| < ε := by
  let η := ε / 12
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [eventually_gt_atTop 1, gamma16_prime_mass_eventually,
    primeOrdered_triple_uniform 10 (1000 * P + 200) η (by norm_num) (by linarith) hη,
    primeOrdered_weighted_uniform 640 (64 * (1000 * P + 200) + 4800)
      (ε / 2) (by norm_num) (by linarith) (half_pos hε)]
    with R hR hmass htriple houter
  intro φ hφ hφP
  obtain ⟨hbound, hlip⟩ := gamma16_outer_regular hφ hφP
  have ho := houter (gamma16OuterWeight φ) gamma16Alpha gamma16Beta
    (primeOrdered_continuous_of_lipschitz hlip) hbound hlip
    gamma16_constants.1 gamma16_constants.2.1 gamma16_constants.2.2.1
  rw [← gamma16_fourth_integral_eq_outer] at ho
  have hr :
      |gamma16NestedPrimeSum R φ -
        primeOrderedClosedSum R gamma16Alpha gamma16Beta (gamma16OuterWeight φ)| ≤ 5 * η := by
    unfold gamma16NestedPrimeSum primeOrderedClosedSum
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p4 ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), η / p4 := by
        apply sum_le_sum
        intro p4 hp4
        have h4 := (mem_primesIcc (rpow_nonneg (by linarith) _)).mp hp4
        have hw := gamma16_log_coordinate_mem hR h4.1 h4.2.1 h4.2.2
        have ht := htriple _ (gamma16_clipped_weight hφ hφP (log p4 / log R))
          gamma16Alpha (log p4 / log R) gamma16_constants.1 hw.1
          (hw.2.trans gamma16_constants.2.2.1)
        rw [← primeOrderedTripleIntegral_eq] at ht
        rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p4 : (0 : ℝ) ≤ p4)]
        exact div_le_div_of_nonneg_right ht.le (Nat.cast_nonneg p4)
      _ = η * ∑ p4 ∈ primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta), 1 / (p4 : ℝ) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring
      _ ≤ 5 * η := by nlinarith [mul_le_mul_of_nonneg_left hmass hη.le]
  have htri := abs_sub_le (gamma16NestedPrimeSum R φ)
    (primeOrderedClosedSum R gamma16Alpha gamma16Beta (gamma16OuterWeight φ))
    (gamma16FourthIntegral φ)
  rw [gamma16_prime_sum_eq_nested hR]
  dsimp only [η] at hr
  linarith

end Wu2008DoubleSieve
