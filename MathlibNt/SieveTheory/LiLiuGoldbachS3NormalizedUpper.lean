import MathlibNt.SieveTheory.LiLiuGoldbachS3PaidUpper
import MathlibNt.SieveTheory.LiLiuGoldbachS3RosserMainUpper
import MathlibNt.SieveTheory.LiLiuGoldbachS3RatioGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachS3PrimeKernel
import MathlibNt.SieveTheory.LiLiuGoldbachS3LiEulerUpper
import MathlibNt.SieveTheory.LiLiuGoldbachUpperDensitySix

open scoped BigOperators
open Filter
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.SwitchingPrinciple
open AnalyticNumberTheory.Sieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

theorem goldbachS3_primeKernelIntegral_nonneg
    {β : ℝ} (hβ : (4 / 53 : ℝ) ≤ β) (hβu : β ≤ (1 / 3 : ℝ)) :
    0 ≤ goldbachS3_primeKernelIntegral β := by
  unfold goldbachS3_primeKernelIntegral
  apply intervalIntegral.integral_nonneg hβ
  intro u hu
  have hs : 1 < ((1 / 2 : ℝ) - u) / (4 / 53 : ℝ) := by
    linarith [hu.2.trans hβu]
  exact div_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
    (goldbach_one_le_suzukiUpperFactor hs)) (by linarith [hu.1])

private theorem S3NormalizedUpper_li_nonneg
    {N : ℕ} {ε : ℝ} (hN : 4 ≤ N) (hεu : ε < (2 : ℝ) / 15) :
    0 ≤ trueLogarithmicIntegral (goldbachS1Endpoint N ε) := by
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 3 ≤ (1 - ε) * (N : ℝ) := by nlinarith
  have hc : 3 ≤ Nat.ceil ((1 - ε) * (N : ℝ)) := by
    exact_mod_cast hx.trans (Nat.le_ceil ((1 - ε) * (N : ℝ)))
  have hm : 2 ≤ goldbachS1Endpoint N ε := by
    unfold goldbachS1Endpoint
    omega
  exact LiuWeight.liuLogarithmicIntegral_nonneg (2 / Real.log 2)
    (div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
    (by exact_mod_cast hm)

private theorem S3NormalizedUpper_product_nonneg
    (N : ℕ) (hEven : Even N) (ε z : ℝ) :
    0 ≤ sieveProductPrimeFactors (goldbachS1BoundingSieve N hEven ε z) := by
  let S := goldbachS1BoundingSieve N hEven ε z
  change 0 ≤ sieveProductPrimeFactors S
  unfold sieveProductPrimeFactors
  apply Finset.prod_nonneg
  intro p hp
  have hpDvd : p ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
  exact sub_nonneg.mpr
    (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpDvd).le

private theorem S3NormalizedUpper_rosser_kernel
    (B β ε t : ℝ) (hB : 0 ≤ B) (hβ : (4 / 53 : ℝ) < β)
    (hβu : β ≤ (1 / 3 : ℝ)) (ht : 0 < t) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β),
        (1 / (Nat.totient p : ℝ)) *
          (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).divisors,
            LinearSieve.upperRosserWeight
              (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)))
              (LiuWeight.panModulusCutoff N B / p + 1) d / (Nat.totient d : ℝ))) ≤
        sieveProductPrimeFactors
          (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ))) *
            (goldbachS3_primeKernelIntegral β + t) := by
  let L : ℝ := Real.log (β / (4 / 53 : ℝ)) + 1
  have hL : 0 < L := by
    have hr : 1 < β / (4 / 53 : ℝ) := (one_lt_div (by norm_num)).2 hβ
    dsimp [L]
    linarith [Real.log_pos hr]
  let ρ : ℝ := t / (2 * L)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρL : ρ * L = t / 2 := by dsimp [ρ]; field_simp
  obtain ⟨z₀, _hz₀, hdensity⟩ := goldbachS3RosserMain_upper_six ρ hρ
  obtain ⟨Nr, _hNr, hratio⟩ := goldbachS3_ratio_range B hB
  obtain ⟨Nk, _hNk, hkernel⟩ :=
    goldbachS3_primeKernel_upper B β (t / 2) hB hβ hβu (by positivity)
  obtain ⟨Nu, _hNu, hunit⟩ := goldbachS3_unitKernel_upper β 1 hβ zero_lt_one
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (4 / 53 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨Nz, hNz⟩ := eventually_atTop.mp (hpow.eventually (eventually_ge_atTop z₀))
  refine ⟨max 4 (max Nr (max Nk (max Nu Nz))), le_max_left _ _, ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNrN : Nr ≤ N := le_trans (by omega) hN
  have hNkN : Nk ≤ N := le_trans (by omega) hN
  have hNuN : Nu ≤ N := le_trans (by omega) hN
  have hNzN : Nz ≤ N := le_trans (by omega) hN
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let ps := goldbachClosedPrimes N z ((N : ℝ) ^ β)
  let V : ℝ := sieveProductPrimeFactors (goldbachS1BoundingSieve N hEven ε z)
  have hV : 0 ≤ V := S3NormalizedUpper_product_nonneg N hEven ε z
  have hpoint : ∀ p ∈ ps,
      (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
        LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
          (LiuWeight.panModulusCutoff N B / p + 1) d / (Nat.totient d : ℝ)) ≤
        (suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) + ρ) * V := by
    intro p hp
    rcases mem_goldbachClosedPrimes_iff.mp hp with ⟨hpp, _, hpl, hpu⟩
    have hu : (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := hpu.trans
      (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) hβu)
    obtain ⟨hΔ, hslo, hshi⟩ := hratio N hNrN p hpp.one_le hpl hu
    -- Delta is the cast of the natural quotient, not the real quotient.
    have hd := hdensity N hEven ε z
      ((LiuWeight.panModulusCutoff N B / p : ℕ) : ℝ)
      (goldbachS3_sieveRatio N B p) (hNz N hNzN) hΔ rfl hslo hshi
    simpa only [Nat.floor_natCast] using hd
  have hsum :
      (∑ p ∈ ps,
        (1 / (Nat.totient p : ℝ)) *
          (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
            LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
              (LiuWeight.panModulusCutoff N B / p + 1) d /
                (Nat.totient d : ℝ))) ≤
        V * (∑ p ∈ ps,
          (suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) + ρ) /
            (Nat.totient p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    calc
      _ ≤ (1 / (Nat.totient p : ℝ)) *
          ((suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) + ρ) * V) :=
        mul_le_mul_of_nonneg_left (hpoint p hp)
          (div_nonneg zero_le_one (Nat.cast_nonneg _))
      _ = _ := by ring
  have hsplit :
      (∑ p ∈ ps,
        (suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) + ρ) /
          (Nat.totient p : ℝ)) =
        (∑ p ∈ ps,
          suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) /
            (Nat.totient p : ℝ)) +
          ρ * ∑ p ∈ ps, (1 : ℝ) / (Nat.totient p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hk := hkernel N hNkN
  have hu := mul_le_mul_of_nonneg_left (hunit N hNuN) hρ.le
  change ρ * (∑ p ∈ ps, (1 : ℝ) / (Nat.totient p : ℝ)) ≤ ρ * L at hu
  rw [hρL] at hu
  have hkern :
      (∑ p ∈ ps,
        (suzukiContinuousUpperFactor (goldbachS3_sieveRatio N B p) + ρ) /
          (Nat.totient p : ℝ)) ≤ goldbachS3_primeKernelIntegral β + t := by
    rw [hsplit]
    change (∑ p ∈ ps, _) ≤ _ at hk
    linarith
  exact hsum.trans (mul_le_mul_of_nonneg_left hkern hV)

private theorem S3NormalizedUpper_bv_absorb
    (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        δ * (SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ 2) := by
  let U : ℝ := SingularSeries.liuUniversalProduct
  have hU : 0 < U := SingularSeries.liuUniversalProduct_pos
  have hδU : 0 < δ * U := mul_pos hδ hU
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (C / (δ * U)))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlog
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hbudget : C ≤ δ * U * Real.log (N : ℝ) := by
    have hh := (div_le_iff₀ hδU).mp (hM N ((le_max_right _ _).trans hN))
    simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using hh
  have hdiv : C / Real.log (N : ℝ) ≤ δ * U :=
    (div_le_iff₀ hlogN).mpr hbudget
  have hratio : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := by positivity
  have hseries : δ * U ≤ δ * SingularSeries.liuSingularSeries N :=
    mul_le_mul_of_nonneg_left
      (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le
  calc
    C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) =
        (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      norm_num
      ring
    _ ≤ (δ * U) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hdiv hratio
    _ ≤ (δ * SingularSeries.liuSingularSeries N) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hseries hratio
    _ = _ := by ring

/-- Fully paid normalization of the actual closed S3, for each fixed beta.
The strict mother carrier and the genuine source-factor integral are retained. -/
theorem goldbachS3_normalized_upper (β δ ε : ℝ)
    (hβ : (4 / 53 : ℝ) < β) (hβu : β ≤ (1 / 3 : ℝ))
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β) : ℝ) ≤
        ((1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
            goldbachS3_primeKernelIntegral β + δ) *
          (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  let A : ℝ := (1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)
  let I : ℝ := goldbachS3_primeKernelIntegral β
  have hA : 0 < A := by
    have ha : 0 < 1 - ε := by linarith
    dsimp [A]
    positivity
  have hI : 0 ≤ I := goldbachS3_primeKernelIntegral_nonneg hβ.le hβu
  let t : ℝ := min 1 (δ / (2 * (A + I + 1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htbudget : t * (A + I + 1) ≤ δ / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * (A + I + 1) by positivity)).mp
      (show t ≤ δ / (2 * (A + I + 1)) from min_le_right _ _)
    nlinarith
  have hcoef : (A + t) * (I + t) ≤ A * I + δ / 2 := by
    have hsq : t ^ 2 ≤ t := by nlinarith
    nlinarith
  obtain ⟨B, hB, C, _hC, hpaidε⟩ := goldbachS3Closed_upperRosser_paid 3 (by norm_num)
  obtain ⟨Np, _hNp, hpaid⟩ := hpaidε ε hε hεu
  obtain ⟨Nk, _hNk, hkernel⟩ := S3NormalizedUpper_rosser_kernel B β ε t hB hβ hβu ht
  obtain ⟨Nv, _hNv, hmass⟩ := goldbachS3_li_mul_eulerProduct_upper t ε ht hε hεu
  obtain ⟨Ne, _hNe, herr⟩ := S3NormalizedUpper_bv_absorb C (δ / 2) (by positivity)
  refine ⟨max 4 (max Np (max Nk (max Nv Ne))), le_max_left _ _, ?_⟩
  intro N hN hEven
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNpN : Np ≤ N := le_trans (by omega) hN
  have hNkN : Nk ≤ N := le_trans (by omega) hN
  have hNvN : Nv ≤ N := le_trans (by omega) hN
  have hNeN : Ne ≤ N := le_trans (by omega) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let X : ℝ := trueLogarithmicIntegral (goldbachS1Endpoint N ε)
  let V : ℝ := sieveProductPrimeFactors
    (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ (4 / 53 : ℝ)))
  let scale : ℝ := SingularSeries.liuSingularSeries N * (N : ℝ) /
    Real.log (N : ℝ) ^ 2
  have hX : 0 ≤ X := S3NormalizedUpper_li_nonneg hN4 hεu
  have hscale : 0 ≤ scale :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (Nat.cast_nonneg N)) (sq_nonneg _)
  have hp := hpaid N hNpN hEven ((N : ℝ) ^ β)
    (Real.rpow_le_rpow_of_exponent_le hN1 hβ.le)
    (Real.rpow_le_rpow_of_exponent_le hN1 hβu)
  have hk := mul_le_mul_of_nonneg_left (hkernel N hNkN hEven) hX
  have hm : X * V ≤ (A + t) * scale := by
    convert hmass N hNvN hEven using 1
    dsimp [X, V, A, scale]
    ring
  have hmain : (X * V) * (I + t) ≤ (A * I + δ / 2) * scale := by
    calc
      (X * V) * (I + t) ≤ ((A + t) * scale) * (I + t) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = ((A + t) * (I + t)) * scale := by ring
      _ ≤ (A * I + δ / 2) * scale :=
        mul_le_mul_of_nonneg_right hcoef hscale
  have he : C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤ (δ / 2) * scale :=
    herr N hNeN
  calc
    (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ β) : ℝ) ≤
        X * (V * (I + t)) + C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) :=
      hp.trans (add_le_add hk le_rfl)
    _ = (X * V) * (I + t) + C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) := by ring
    _ ≤ (A * I + δ / 2) * scale + (δ / 2) * scale := add_le_add hmain he
    _ = _ := by dsimp [A, I, scale]; ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig