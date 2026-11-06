import U8SquarefreeHarmonicLower
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorAsymptotic

/-! Uniform two-log growth of the actual two-dimensional denominator. The
parameter used in the one-dimensional arithmetic cutoff is not a distribution
parameter. It is reparametrized solely to select exponent beta/2. -/
noncomputable section
open Finset Filter
open scoped BigOperators Topology
namespace U8Literal.SmallProduct.TwoDimensional
open scoped Classical
open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiuWeight

theorem liuFactor_eq_arithmetic {N d : ℕ} (hd : Squarefree d) :
    liuFactor N d = liuSelbergArithmetic N d := by
  rw [liuFactor, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero]
  by_cases hc : Nat.Coprime d N
  · rw [liuSelbergArithmetic_eq_prod hd.ne_zero hd hc]
    apply prod_congr rfl
    intro p hp
    have hnot : ¬ p ∣ N := (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd.mp
      (hc.of_dvd_left (Nat.dvd_of_mem_primeFactors hp))
    simp [hnot]
  · rw [liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime (by tauto)]
    obtain ⟨p,hp,hpg⟩ := Nat.exists_prime_and_dvd
      (show Nat.gcd d N ≠ 1 from fun h => hc (Nat.coprime_iff_gcd_eq_one.mpr h))
    have hpd := hpg.trans (Nat.gcd_dvd_left d N)
    have hpN := hpg.trans (Nat.gcd_dvd_right d N)
    apply prod_eq_zero_iff.mpr
    exact ⟨p, Nat.mem_primeFactors_of_ne_zero hd.ne_zero |>.mpr ⟨hp,hpd⟩, by simp [hpN]⟩

theorem liuDenominator_eq_prefix {N : ℕ} (hN : Even N) {ε : ℝ}
    (hT : 1 ≤ paperQSourceCutoff N ε) :
    liuSelbergDenominator N ε =
      ∑ d ∈ squarefreePrefix (paperQSourceCutoff N ε), liuFactor N d := by
  rw [liuSelbergDenominator_eq_sum_Icc hN hT, squarefreePrefix, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : Squarefree d
  · rw [if_pos hd, liuFactor_eq_arithmetic hd]
  · rw [if_neg hd, liuSelbergArithmetic_eq_zero_of_not_squarefree_or_not_coprime (by tauto)]

theorem floor_half_power_square_le (N : ℕ) (β : ℝ) :
    ((⌊(N : ℝ)^(β/2)⌋₊ : ℕ) : ℝ)^2 ≤ (N : ℝ)^β := by
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (β/2))
  calc
    _ ≤ ((N : ℝ)^(β/2))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2
    _ = (N : ℝ)^β := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1
      ring

/-- The exponent is fixed before a single threshold, uniform over even N and
all legal sieve-prime cutoffs Z. -/
theorem eventually_denominator_two_log {β : ℝ} (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ Z : ℝ, (N : ℝ)^β < Z →
      (β^2/64) * (Real.log N)^2 / SingularSeries.liuSingularSeries N ≤
        denominator N Z ((N : ℝ)^β) := by
  let ε : ℝ := 1/2-β
  have hexp : 1/4-ε/2 = β/2 := by dsimp [ε]; ring
  have hhalf : 0 < β/2 := by positivity
  have hlim := tendsto_liuSelbergDenominator_normalized_even ε (by rw [hexp]; exact hhalf)
  have hlow := hlim.eventually (Ioi_mem_nhds (show β/8 < (1/4-ε/2)/2 by rw [hexp]; linarith))
  rw [eventually_inf_principal] at hlow
  have hlog := (tendsto_log_floor_rpow_div_log (β/2) hhalf).eventually
    (Ioi_mem_nhds (show β/4 < β/2 by linarith))
  filter_upwards [hlow, hlog, eventually_ge_atTop (2 : ℕ)] with N hL hH hN
  intro heven Z hZ
  let T := ⌊(N : ℝ)^(β/2)⌋₊
  let S := SingularSeries.liuSingularSeries N
  let L := Real.log (N : ℝ)
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hN)
  have hSpos : 0 < S := SingularSeries.liuSingularSeries_pos N
  have hT : 1 ≤ T := by
    apply Nat.le_floor
    simpa using Real.one_le_rpow (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)) hhalf.le
  have hcut : paperQSourceCutoff N ε = T := by simp only [paperQSourceCutoff, hexp, T]
  have hfirst : (β/8)*L/S ≤ ∑ d ∈ squarefreePrefix T, liuFactor N d := by
    have hh := le_of_lt (hL heven)
    change β/8 ≤ liuSelbergDenominator N ε * S / L at hh
    have hm := (le_div_iff₀ hLpos).mp hh
    apply (div_le_iff₀ hSpos).mpr
    rw [← hcut, ← liuDenominator_eq_prefix heven (by rwa [hcut])]
    exact hm
  have hsecond : (β/8)*L ≤ ∑ e ∈ squarefreePrefix T, harmonicFactor e := by
    have hh : β/4 ≤ Real.log T / L := le_of_lt hH
    have hm := (le_div_iff₀ hLpos).mp hh
    have ht := log_le_twice_harmonicFactor_sum T
    linarith
  have hfirst0 : 0 ≤ (β/8)*L/S := by positivity
  have hmul := mul_le_mul hfirst hsecond (by positivity : 0 ≤ (β/8)*L) (hfirst0.trans hfirst)
  have hrect := denominator_ge_prefix_product heven hZ (floor_half_power_square_le N β)
  have hid : ((β/8)*L/S)*((β/8)*L) = (β^2/64)*L^2/S := by ring
  rw [hid] at hmul
  exact hmul.trans hrect

/-- The existing optimizer consumes the genuine denominator bound. -/
theorem optimal_main_le_two_log {N : ℕ} (hN : Even N) {β Z : ℝ}
    (hβ : 0 < β) (hNtwo : 1 < N)
    (hden : (β^2/64) * (Real.log N)^2 / SingularSeries.liuSingularSeries N ≤
      denominator N Z ((N : ℝ)^β)) :
    mainMatrix N Z ((N : ℝ)^β) (optimalWeight N hN Z ((N : ℝ)^β)) ≤
      (64/β^2) * SingularSeries.liuSingularSeries N / (Real.log N)^2 := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNtwo)
  have hS : 0 < SingularSeries.liuSingularSeries N := SingularSeries.liuSingularSeries_pos N
  have hc : 0 < (β^2/64) * (Real.log N)^2 / SingularSeries.liuSingularSeries N := by positivity
  rw [mainMatrix_optimal N hN Z (Real.one_le_rpow
    (show (1 : ℝ) ≤ N by exact_mod_cast hNtwo.le) hβ.le)]
  calc
    _ ≤ 1 / ((β^2/64) * (Real.log N)^2 / SingularSeries.liuSingularSeries N) :=
      one_div_le_one_div_of_le hc hden
    _ = _ := by field_simp



end U8Literal.SmallProduct.TwoDimensional
