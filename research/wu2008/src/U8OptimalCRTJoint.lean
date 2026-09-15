import U8TwoLinearRemainder
import U8TwoDimensionalConvolution

/-! The actual CRT quadratic joined to the constructed truncated optimizer.
The original cube-root sieve carrier is not changed. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct
open TwoDimensional

 theorem nuN_cast_eq_rootCount (N m : ℕ) : (nuN N m : ℝ) = rootCount N m := by
  classical
  unfold nuN rootCount roots
  rw [Nat.cast_prod]
  apply prod_congr rfl
  intro p _
  split_ifs <;> norm_num

theorem nuN_div_eq_density (N : ℕ) {m : ℕ} (hm : Squarefree m) :
    (nuN N m : ℝ) / m = density N m := by
  rw [nuN_cast_eq_rootCount, density_eq N hm]

theorem nuN_lcm_eq_density (N : ℕ) {Z : ℝ} {d f : ℕ}
    (hd : d ∣ (sievePrimes Z).prod id) (hf : f ∣ (sievePrimes Z).prod id) :
    (nuN N (Nat.lcm d f) : ℝ) / Nat.lcm d f = density N (Nat.lcm d f) :=
  nuN_div_eq_density N (sieve_lcm_squarefree hd hf)

theorem carrier_dvd {Z R : ℝ} {d : ℕ} (hd : d ∈ carrier Z R) :
    d ∣ (sievePrimes Z).prod id := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1

theorem carrier_bound {Z R : ℝ} {d : ℕ} (hd : d ∈ carrier Z R) : (d : ℝ) ≤ R :=
  (mem_filter.mp hd).2

theorem carrier_one {Z R : ℝ} (hR : 1 ≤ R) : 1 ∈ carrier Z R :=
  mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _,sievePrimes_prod_ne_zero Z⟩,
    by simpa using hR⟩

theorem carrier_small_support {N : ℕ} {Z R : ℝ} (hR : R < (N : ℝ)^originalAlpha)
    {d : ℕ} (hd : d ∈ carrier Z R) {p : ℕ} (hp : p ∈ d.primeFactors) :
    (p : ℝ) < (N : ℝ)^originalAlpha := by
  have hd0 := ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) (carrier_dvd hd)
  have hp_le : (p : ℝ) ≤ d := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) (Nat.dvd_of_mem_primeFactors hp)
  exact hp_le.trans_lt ((carrier_bound hd).trans_lt hR)

/-- There are no supplied local-density, CRT or optimal-main hypotheses. -/
theorem quadratic_optimal_exact {N : ℕ} (hN : Even N) {e Z R : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hR1 : 1 ≤ R) (hRa : R < (N : ℝ)^originalAlpha) :
    quadratic N e t (carrier Z R) (optimalWeight N hN Z R) =
      ((interval N e t).card : ℝ) / denominator N Z R +
      quadraticRemainder N e t (carrier Z R) (optimalWeight N hN Z R) := by
  rw [quadratic_eq_nuN_of_small_support ht _ _ (fun _ hd => carrier_dvd hd)
    (fun _ hd _ hp => carrier_small_support hRa hd hp)]
  simp_rw [nuN_cast_eq_rootCount]
  change (interval N e t).card * mainMatrix N Z R (optimalWeight N hN Z R) + _ = _
  rw [mainMatrix_optimal N hN Z hR1]
  ring

/-- Real free levels are handled by their natural floor, then enlarged monotonically. -/
theorem optimal_remainder_bound (N : ℕ) (hN : Even N) (e Z R : ℝ) (t : ℕ × ℕ)
    (hR1 : 1 ≤ R) :
    |quadraticRemainder N e t (carrier Z R) (optimalWeight N hN Z R)| ≤
      2*(R+1)^2*R^4 := by
  have h0 : 0 ≤ R := zero_le_one.trans hR1
  have hf0 : (0 : ℝ) ≤ ⌊R⌋₊ := Nat.cast_nonneg _
  have hf : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le h0
  apply (quadraticRemainder_abs_le_polynomial N ⌊R⌋₊ e t _ _
    (fun _ hd => ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) (carrier_dvd hd))
    (fun _ hd => Nat.le_floor (carrier_bound hd))
    (fun d _ => optimalWeight_abs_le N hN Z hR1 d)).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2)
    (by norm_num)) (pow_le_pow_left₀ hf0 hf 4) (by positivity) (by positivity)

/-- The optimizer, its support, normalization, height and true main matrix are
all discharged internally. The remaining pair count is deliberately visible here. -/
theorem smallPrefix_optimal_card_bound (N : ℕ) (hNe : Even N) (e R : ℝ)
    (hN : 4 ≤ N) (he : e ≤ 1/2) (hR1 : 1 ≤ R)
    (hRa : R < (N : ℝ)^originalAlpha) :
    ((smallPrefix N e).card : ℝ) ≤
      (∑ t ∈ pairs N e, ((interval N e t).card : ℝ)) /
        denominator N ((N : ℝ)^(1/3 : ℝ)) R +
      (pairs N e).card * (2*(R+1)^2*R^4) := by
  let Z := (N : ℝ)^(1/3 : ℝ)
  have hb := smallPrefix_card_le_cubeRootQuadratic N e hN he (carrier Z R)
    (optimalWeight N hNe Z R) (carrier_one hR1) (fun _ hd => carrier_dvd hd)
    (optimalWeight_one N hNe Z hR1)
  calc
    _ ≤ ∑ t ∈ pairs N e, quadratic N e t (carrier Z R) (optimalWeight N hNe Z R) := hb
    _ = (∑ t ∈ pairs N e, ((interval N e t).card : ℝ)) / denominator N Z R +
        ∑ t ∈ pairs N e, quadraticRemainder N e t (carrier Z R) (optimalWeight N hNe Z R) := by
      rw [sum_div, ← sum_add_distrib]
      exact sum_congr rfl (fun _ ht => quadratic_optimal_exact hNe ht hR1 hRa)
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ ∑ t ∈ pairs N e, |quadraticRemainder N e t (carrier Z R) (optimalWeight N hNe Z R)| :=
          sum_le_sum fun _ _ => le_abs_self _
        _ ≤ ∑ _t ∈ pairs N e, 2*(R+1)^2*R^4 :=
          sum_le_sum fun t _ => optimal_remainder_bound N hNe e Z R t hR1
        _ = _ := by simp

end U8Literal.SmallProduct
