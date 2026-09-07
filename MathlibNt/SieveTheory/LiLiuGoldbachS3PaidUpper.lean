import MathlibNt.SieveTheory.LiLiuGoldbachS3LevelGeometry
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional

open scoped BigOperators
open Finset Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open BombieriVinogradov

private theorem S3Paid_mul_injective
    {N p q d e : ℕ} {z y : ℝ}
    (hp : p ∈ goldbachClosedPrimes N z y)
    (hq : q ∈ goldbachClosedPrimes N z y)
    (_hd : d ∣ goldbachS1ProdPrimes N z)
    (he : e ∣ goldbachS1ProdPrimes N z)
    (heq : p * d = q * e) : p = q ∧ d = e := by
  have hpp := (mem_goldbachClosedPrimes_iff.mp hp).1
  have hqq := (mem_goldbachClosedPrimes_iff.mp hq).1
  have hpe : ¬ p ∣ e :=
    hpp.coprime_iff_not_dvd.mp (goldbachS3_coprime_of_dvd_prodPrimes hp he)
  have hpqe : p ∣ q * e := heq ▸ dvd_mul_right p d
  have hpq : p ∣ q := (hpp.dvd_mul.mp hpqe).resolve_right hpe
  have hpqEq : p = q := ((Nat.dvd_prime hqq).mp hpq).resolve_left hpp.ne_one
  subst q
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hpp.pos heq⟩

private theorem S3Paid_prefix_doubleSum_le
    (N Q : ℕ) (z y : ℝ) :
    (∑ p ∈ goldbachClosedPrimes N z y,
      ∑ d ∈ (goldbachS1ProdPrimes N z).divisors.filter (fun d => d < Q / p + 1),
        standardPrimeAPPrefixMaxError N (p * d)) ≤
      ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
  classical
  let ps := goldbachClosedPrimes N z y
  let ds := fun p => (goldbachS1ProdPrimes N z).divisors.filter (fun d => d < Q / p + 1)
  let T := ps.sigma ds
  let f := fun a : (p : ℕ) × ℕ => a.1 * a.2
  have hinj : Set.InjOn f T := by
    rintro ⟨p, d⟩ hpd ⟨q, e⟩ hqe heq
    rcases Finset.mem_sigma.mp hpd with ⟨hp, hd⟩
    rcases Finset.mem_sigma.mp hqe with ⟨hq, he⟩
    have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hevd := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
    obtain ⟨rfl, rfl⟩ := S3Paid_mul_injective hp hq hdvd hevd heq
    rfl
  have hsub : T.image f ⊆ Icc 1 Q := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨⟨p, d⟩, hpd, rfl⟩
    rcases Finset.mem_sigma.mp hpd with ⟨hp, hd⟩
    rcases Finset.mem_filter.mp hd with ⟨hdv, hdl⟩
    change d < Q / p + 1 at hdl
    have hpp := (mem_goldbachClosedPrimes_iff.mp hp).1
    have hd0 := Nat.pos_of_mem_divisors hdv
    have hdle : d ≤ Q / p := by omega
    have hmul : p * d ≤ Q := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hpp.pos).mp hdle
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_pos hpp.pos hd0), hmul⟩
  calc
    (∑ p ∈ ps, ∑ d ∈ ds p, standardPrimeAPPrefixMaxError N (p * d)) =
        ∑ k ∈ T.image f, standardPrimeAPPrefixMaxError N k := by
      rw [Finset.sum_sigma', Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => standardPrimeAPPrefixMaxError_nonneg N k)

/-- The actual conditional Rosser errors inject into the unweighted full
modulus sum. In particular the divisor `1` is not removed. -/
theorem goldbachS3_upperErrSum_le_prefixSum
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} (Q : ℕ)
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε) :
    (∑ p ∈ goldbachClosedPrimes N z y,
      LinearSieve.upperErrSum (goldbachS3BoundingSieve N hEven ε z p) (Q / p + 1)
        (LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z) (Q / p + 1))) ≤
      ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
  classical
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (S3Paid_prefix_doubleSum_le N Q z y)
  change (∑ d ∈ (goldbachS1ProdPrimes N z).divisors.filter (fun d => d < Q / p + 1),
      |LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z) (Q / p + 1) d| *
        |(goldbachS3BoundingSieve N hEven ε z p).rem d|) ≤ _
  apply Finset.sum_le_sum
  intro d hd
  have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  calc
    |LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z) (Q / p + 1) d| *
        |(goldbachS3BoundingSieve N hEven ε z p).rem d| ≤
        1 * |(goldbachS3BoundingSieve N hEven ε z p).rem d| :=
      mul_le_mul_of_nonneg_right (LinearSieve.abs_upperRosserWeight_le_one _ _ _)
        (abs_nonneg _)
    _ ≤ standardPrimeAPPrefixMaxError N (p * d) := by
      simpa only [one_mul] using
        goldbachS3BoundingSieve_abs_rem_le_prefix hEven hε hm hp hdvd

private theorem S3Paid_finite
    {N : ℕ} (hEven : Even N) {ε z y : ℝ} (Q : ℕ)
    (hε : 0 ≤ ε) (hm : 2 ≤ goldbachS1Endpoint N ε)
    (hlevel : ∀ p ∈ goldbachClosedPrimes N z y, 1 < Q / p + 1 ∧
      ∀ ℓ ∈ (goldbachS1ProdPrimes N z).primeFactors, ℓ < Q / p + 1) :
    (goldbachS3Closed (goldbachDifferenceCarrier N ε) N z y : ℝ) ≤
      trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
        (∑ p ∈ goldbachClosedPrimes N z y, (1 / (Nat.totient p : ℝ)) *
          (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
            LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
              (Q / p + 1) d / (Nat.totient d : ℝ))) +
        ∑ k ∈ Icc 1 Q, standardPrimeAPPrefixMaxError N k := by
  classical
  have hpoint : ∀ p ∈ goldbachClosedPrimes N z y,
      (literalH (goldbachDifferenceCarrier N ε) N p z : ℝ) ≤
        (trueLogarithmicIntegral (goldbachS1Endpoint N ε) / Nat.totient p) *
          (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
            LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
              (Q / p + 1) d / Nat.totient d) +
        LinearSieve.upperErrSum (goldbachS3BoundingSieve N hEven ε z p) (Q / p + 1)
          (LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z) (Q / p + 1)) := by
    intro p hp
    have hcert := LinearSieve.upperRosserWeight_certificate
      (goldbachS1ProdPrimes_squarefree N z) (goldbachS1ProdPrimes_ne_zero N z)
      (hlevel p hp).1 (hlevel p hp).2
    have hf := LinearSieve.siftedSum_le_mainSum_add_upperErrSum_upperRosser
      (S := goldbachS3BoundingSieve N hEven ε z p) (Q / p + 1) hcert
    rw [goldbachS3BoundingSieve_siftedSum_eq,
      goldbachS3BoundingSieve_mainSum_eq_totientSum] at hf
    exact hf
  have hsum := Finset.sum_le_sum hpoint
  have herr := goldbachS3_upperErrSum_le_prefixSum (z := z) (y := y) hEven Q hε hm
  have hmain :
      (∑ p ∈ goldbachClosedPrimes N z y,
        (trueLogarithmicIntegral (goldbachS1Endpoint N ε) / Nat.totient p) *
          (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
            LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
              (Q / p + 1) d / Nat.totient d)) =
        trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
          (∑ p ∈ goldbachClosedPrimes N z y, (1 / (Nat.totient p : ℝ)) *
            (∑ d ∈ (goldbachS1ProdPrimes N z).divisors,
              LinearSieve.upperRosserWeight (goldbachS1ProdPrimes N z)
                (Q / p + 1) d / Nat.totient d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [Finset.sum_add_distrib, hmain] at hsum
  have hlit : (goldbachS3Closed (goldbachDifferenceCarrier N ε) N z y : ℝ) =
      ∑ p ∈ goldbachClosedPrimes N z y,
        (literalH (goldbachDifferenceCarrier N ε) N p z : ℝ) := by
    simp only [goldbachS3Closed, Int.cast_sum]
  rw [hlit]
  exact hsum.trans (add_le_add le_rfl herr)

private theorem S3Paid_endpoint_two_le {N : ℕ} {ε : ℝ}
    (hN : 4 ≤ N) (hε : ε < 2 / 15) : 2 ≤ goldbachS1Endpoint N ε := by
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hx3 : 3 ≤ (1 - ε) * (N : ℝ) := by nlinarith
  have hceil : 3 ≤ Nat.ceil ((1 - ε) * (N : ℝ)) := by
    exact_mod_cast hx3.trans (Nat.le_ceil ((1 - ε) * (N : ℝ)))
  unfold goldbachS1Endpoint
  omega

/-- Actual closed S3 with the BV remainder paid, retaining the exact finite
upper Rosser main sum and the strict-endpoint genuine logarithmic integral.
Both constants precede epsilon, and the threshold is uniform in `y`. -/
theorem goldbachS3Closed_upperRosser_paid (U : ℝ) (hU : 0 < U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε < 2 / 15 →
        ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ y : ℝ, (N : ℝ) ^ (4 / 53 : ℝ) ≤ y →
            y ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
            (goldbachS3Closed (goldbachDifferenceCarrier N ε) N
              ((N : ℝ) ^ (4 / 53 : ℝ)) y : ℝ) ≤
              trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
                (∑ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) y,
                  (1 / (Nat.totient p : ℝ)) *
                    (∑ d ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).divisors,
                      LinearSieve.upperRosserWeight
                        (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)))
                        (LiuWeight.panModulusCutoff N B / p + 1) d /
                          (Nat.totient d : ℝ))) +
                C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨B, hB, C, hC, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov U hU
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hBV.and (goldbachS3_level_eventually B))
  refine ⟨B, hB, C, hC, ?_⟩
  intro ε hε hεu
  refine ⟨max 4 K, le_max_left _ _, ?_⟩
  intro N hN hEven y _hzy hy
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hdata := hK N ((le_max_right _ _).trans hN)
  have hm := S3Paid_endpoint_two_le hN4 hεu
  have hlevel : ∀ p ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) y,
      1 < LiuWeight.panModulusCutoff N B / p + 1 ∧
      ∀ ℓ ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).primeFactors,
        ℓ < LiuWeight.panModulusCutoff N B / p + 1 := by
    intro p hp
    have hpd := mem_goldbachClosedPrimes_iff.mp hp
    exact hdata.2.2 p hpd.1.pos (hpd.2.2.2.trans hy)
  exact (S3Paid_finite hEven (LiuWeight.panModulusCutoff N B) hε.le hm hlevel).trans
    (add_le_add le_rfl (hdata.1 (by omega)))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig