

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.GroupWithZero
import MathlibNt.SieveTheory.Arithmetic.SingularSeries

/-!
 # MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

Liu's source singular series omits the prime `2`.  This file first separates
its exact finite truncation from the legacy sieve-normalized proxy.

Source: Liu, `main.tex`, lines 98--102.
-/

namespace MathlibNt.SieveTheory.SingularSeries

open Nat Real Finset

/-- Liu's local factor at an odd prime. -/
noncomputable def liuLocalFactor (p N : ℕ) : ℝ :=
  if p ∣ N then
    (p : ℝ) / (p - 1)
  else
    (p : ℝ) * (p - 2) / ((p - 1) ^ 2)

/-- The divisor factor is the source product of the correction and base factors. -/
theorem liuLocalFactor_of_dvd {p N : ℕ} (hp2 : 2 < p) (hpdvd : p ∣ N) :
    liuLocalFactor p N =
      ((p : ℝ) - 1) / ((p : ℝ) - 2) *
        (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [liuLocalFactor, if_pos hpdvd]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp1' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hp2' : (p : ℝ) - 2 ≠ 0 := by
    have hp2'' : (2 : ℝ) < p := by exact_mod_cast hp2
    linarith
  field_simp [hp1, hp2']
  ring

/-- A nondivisor contributes exactly Liu's universal base factor. -/
theorem liuLocalFactor_of_not_dvd {p N : ℕ} (hp2 : 2 < p) (hpn : ¬p ∣ N) :
    liuLocalFactor p N = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  rw [liuLocalFactor, if_neg hpn]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp1' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  field_simp [hp1]
  ring

/-- Away from `2`, Liu's local factor is the legacy local factor. -/
theorem liuLocalFactor_eq_localFactor {p N : ℕ} (hp2 : 2 < p) :
    liuLocalFactor p N = localFactor p N := by
  by_cases hpdvd : p ∣ N
  · simp [liuLocalFactor, localFactor, hpdvd, ne_of_gt hp2]
  · simp [liuLocalFactor, localFactor, hpdvd, ne_of_gt hp2]

/-- Liu's source-normalized finite truncation: only odd primes `p ≤ z`. -/
noncomputable def liuSingularSeriesTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)).prod
    (fun p => liuLocalFactor p N)

theorem liuSingularSeriesTruncated_pos (N z : ℕ) :
    0 < liuSingularSeriesTruncated N z := by
  unfold liuSingularSeriesTruncated
  apply Finset.prod_pos
  intro p hp
  rw [mem_filter] at hp
  rw [liuLocalFactor_eq_localFactor hp.2.2]
  exact localFactor_pos hp.2.1

/-- For even `N`, the legacy truncation differs from Liu's finite truncation
by exactly the local factor `2`. -/
theorem singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
    (N z : ℕ) (hN : Even N) (hz : 2 ≤ z) :
    singularSeriesTruncated N z = 2 * liuSingularSeriesTruncated N z := by
  classical
  unfold singularSeriesTruncated liuSingularSeriesTruncated
  let P := (range (z + 1)).filter Nat.Prime
  have h2P : 2 ∈ P := by
    simp [P, hz, Nat.prime_two]
  rw [show (range (z + 1)).filter Nat.Prime = P by rfl]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem h2P, localFactor_two hN]
  congr 1
  have hfilter :
      P \ {2} = (range (z + 1)).filter (fun p => p.Prime ∧ 2 < p) := by
    ext p
    constructor
    · intro hp
      rw [mem_sdiff, mem_filter] at hp
      rw [mem_filter]
      refine ⟨hp.1.1, hp.1.2, ?_⟩
      rcases hp.1.2.eq_two_or_odd' with h | h
      · exact (hp.2 (by simp [h])).elim
      · obtain ⟨k, hk⟩ := h
        have hpge := hp.1.2.two_le
        omega
    · intro hp
      rw [mem_filter] at hp
      rw [mem_sdiff, mem_filter]
      exact ⟨⟨hp.1, hp.2.1⟩, by simp [ne_of_gt hp.2.2]⟩
  rw [hfilter]
  apply Finset.prod_congr rfl
  intro p hp
  rw [mem_filter] at hp
  exact (liuLocalFactor_eq_localFactor hp.2.2).symm

/-- At the legacy cutoff `N`, the proxy is exactly twice Liu's finite
source-normalized truncation. -/
theorem singularSeries_eq_two_mul_liuSingularSeriesTruncatedAtN
    (N : ℕ) (hN : Even N) (hN2 : 2 ≤ N) :
    singularSeries N = 2 * liuSingularSeriesTruncated N N := by
  exact singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated N N hN hN2

/-- The deviation from `1` in Liu's universal odd-prime product. -/
noncomputable def liuBaseDeviation (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then -1 / ((p : ℝ) - 1) ^ 2 else 0

theorem summable_liuBaseDeviation_bound :
    Summable (fun p : ℕ => 1 / ((p : ℝ) - 1) ^ 2) := by
  apply (summable_nat_add_iff 2).mp
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs1 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs
  have heq : (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) - 1) ^ 2) =
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    funext n
    congr 2
    push_cast
    ring
  rw [heq]
  exact hs1

theorem summable_norm_liuBaseDeviation :
    Summable (fun p : ℕ => ‖liuBaseDeviation p‖) := by
  apply Summable.of_nonneg_of_le
    (fun p => norm_nonneg (liuBaseDeviation p)) _ summable_liuBaseDeviation_bound
  intro p
  unfold liuBaseDeviation
  split_ifs
  · rw [norm_div, norm_neg, norm_one, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ((p : ℝ) - 1))]
  · simp
    positivity

theorem one_add_liuBaseDeviation_pos (p : ℕ) :
    0 < 1 + liuBaseDeviation p := by
  rw [liuBaseDeviation]
  split_ifs with h
  · have hp2 : (2 : ℝ) < p := by exact_mod_cast h.2
    have hpden : 1 < ((p : ℝ) - 1) ^ 2 := by
      nlinarith [sq_nonneg ((p : ℝ) - 1)]
    rw [neg_div, ← sub_eq_add_neg, sub_pos]
    exact (div_lt_one (by positivity)).mpr hpden
  · norm_num

theorem one_add_liuBaseDeviation_le_one (p : ℕ) :
    1 + liuBaseDeviation p ≤ 1 := by
  rw [liuBaseDeviation]
  split_ifs
  · apply add_le_of_nonpos_right
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)
  · simp

theorem multipliable_one_add_liuBaseDeviation :
    Multipliable (fun p : ℕ => 1 + liuBaseDeviation p) :=
  multipliable_one_add_of_summable summable_norm_liuBaseDeviation

/-- The convergent universal product
`∏_{p > 2 prime} (1 - 1 / (p - 1)^2)` in Liu's source. -/
noncomputable def liuUniversalProduct : ℝ :=
  ∏' p : ℕ, (1 + liuBaseDeviation p)

theorem liuUniversalProduct_ne_zero : liuUniversalProduct ≠ 0 := by
  exact tprod_one_add_ne_zero_of_summable
    (fun p => ne_of_gt (one_add_liuBaseDeviation_pos p))
    summable_norm_liuBaseDeviation

theorem liuUniversalProduct_nonneg : 0 ≤ liuUniversalProduct := by
  unfold liuUniversalProduct
  apply ge_of_tendsto multipliable_one_add_liuBaseDeviation.tendsto_prod_tprod_nat
  filter_upwards [] with n
  exact Finset.prod_nonneg (fun p _ => (one_add_liuBaseDeviation_pos p).le)

theorem liuUniversalProduct_pos : 0 < liuUniversalProduct :=
  lt_of_le_of_ne liuUniversalProduct_nonneg liuUniversalProduct_ne_zero.symm

/-- Finite truncation of Liu's universal product through `z`.  Non-prime and
even indices contribute `1`. -/
noncomputable def liuUniversalProductTruncated (z : ℕ) : ℝ :=
  ∏ p ∈ range (z + 1), (1 + liuBaseDeviation p)

theorem liuUniversalProductTruncated_pos (z : ℕ) :
    0 < liuUniversalProductTruncated z := by
  unfold liuUniversalProductTruncated
  exact Finset.prod_pos fun p _ => one_add_liuBaseDeviation_pos p

theorem tendsto_liuUniversalProductTruncated :
    Filter.Tendsto liuUniversalProductTruncated Filter.atTop
      (nhds liuUniversalProduct) := by
  exact multipliable_one_add_liuBaseDeviation.tendsto_prod_tprod_nat.comp
    (Filter.tendsto_add_atTop_nat 1)

/-- Every finite universal product dominates the full product.  This is the
monotone Euler-tail inequality; unlike pointwise convergence, it is uniform in
the source integer. -/
theorem liuUniversalProduct_le_truncated (z : ℕ) :
    liuUniversalProduct ≤ liuUniversalProductTruncated z := by
  have hmono : Antitone liuUniversalProductTruncated := by
    intro m n hmn
    unfold liuUniversalProductTruncated
    apply Finset.prod_le_prod_of_subset_of_le_one
    · intro p hp
      simp only [mem_range] at hp ⊢
      omega
    · intro p hp
      exact (one_add_liuBaseDeviation_pos p).le
    · intro p hp hpm
      exact one_add_liuBaseDeviation_le_one p
  apply le_of_tendsto tendsto_liuUniversalProductTruncated
  filter_upwards [Filter.eventually_ge_atTop z] with n hn
  exact hmono hn

/-- The finite correction attached to an odd prime divisor of `N`. -/
noncomputable def liuCorrectionFactor (p : ℕ) : ℝ :=
  ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem liuCorrectionFactor_pos {p : ℕ} (hp2 : 2 < p) :
    0 < liuCorrectionFactor p := by
  unfold liuCorrectionFactor
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  exact div_pos (by linarith) (by linarith)

theorem one_le_liuCorrectionFactor {p : ℕ} (hp2 : 2 < p) :
    1 ≤ liuCorrectionFactor p := by
  unfold liuCorrectionFactor
  have hp2' : (2 : ℝ) < p := by exact_mod_cast hp2
  rw [one_le_div₀ (by linarith)]
  linarith

/-- The finite product of Liu's correction factors over odd prime divisors. -/
noncomputable def liuCorrection (N : ℕ) : ℝ :=
  (N.primeFactors.filter (fun p => 2 < p)).prod liuCorrectionFactor

theorem liuCorrection_pos (N : ℕ) : 0 < liuCorrection N := by
  unfold liuCorrection
  apply Finset.prod_pos
  intro p hp
  rw [mem_filter] at hp
  exact liuCorrectionFactor_pos hp.2

theorem one_le_liuCorrection (N : ℕ) : 1 ≤ liuCorrection N := by
  unfold liuCorrection
  exact Finset.one_le_prod fun p hp => one_le_liuCorrectionFactor (mem_filter.mp hp).2

/-- The correction product through `z`, written on the same index set as the
finite universal product. -/
noncomputable def liuCorrectionTruncated (N z : ℕ) : ℝ :=
  ((range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)).prod
    (fun p => if p ∣ N then liuCorrectionFactor p else 1)

theorem liuCorrectionTruncated_pos (N z : ℕ) :
    0 < liuCorrectionTruncated N z := by
  unfold liuCorrectionTruncated
  apply Finset.prod_pos
  intro p hp
  rw [mem_filter] at hp
  split_ifs
  · exact liuCorrectionFactor_pos hp.2.2
  · norm_num

theorem one_add_liuBaseDeviation_eq_baseFactor {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    1 + liuBaseDeviation p = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  simp only [liuBaseDeviation, hp, hp2, and_self, if_true]
  rw [neg_div]
  ring

theorem liuLocalFactor_eq_correction_mul_base {p N : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    liuLocalFactor p N =
      (if p ∣ N then liuCorrectionFactor p else 1) *
        (1 + liuBaseDeviation p) := by
  by_cases hpdvd : p ∣ N
  · rw [if_pos hpdvd, liuLocalFactor_of_dvd hp2 hpdvd,
      one_add_liuBaseDeviation_eq_baseFactor hp hp2]
    rfl
  · rw [if_neg hpdvd, one_mul, liuLocalFactor_of_not_dvd hp2 hpdvd,
      one_add_liuBaseDeviation_eq_baseFactor hp hp2]

theorem liuUniversalProductTruncated_eq_oddPrimeProd (z : ℕ) :
    liuUniversalProductTruncated z =
      ((range (z + 1)).filter (fun p => p.Prime ∧ 2 < p)).prod
        (fun p => 1 + liuBaseDeviation p) := by
  classical
  unfold liuUniversalProductTruncated
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : p.Prime ∧ 2 < p
  · simp [h]
  · simp [h, liuBaseDeviation]

theorem liuSingularSeriesTruncated_factorization (N z : ℕ) :
    liuSingularSeriesTruncated N z =
      liuCorrectionTruncated N z * liuUniversalProductTruncated z := by
  classical
  rw [liuUniversalProductTruncated_eq_oddPrimeProd]
  unfold liuSingularSeriesTruncated liuCorrectionTruncated
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [mem_filter] at hp
  exact liuLocalFactor_eq_correction_mul_base hp.2.1 hp.2.2

theorem liuCorrectionTruncated_eq_liuCorrection
    {N z : ℕ} (hN : 0 < N) (hz : N ≤ z) :
    liuCorrectionTruncated N z = liuCorrection N := by
  classical
  unfold liuCorrectionTruncated liuCorrection
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_range, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hpz, hp, hp2⟩, hpdvd⟩
    exact ⟨⟨hp, hpdvd, hN.ne'⟩, hp2⟩
  · rintro ⟨⟨hp, hpdvd, _⟩, hp2⟩
    have hpN : p ≤ N := Nat.le_of_dvd hN hpdvd
    exact ⟨⟨by omega, hp, hp2⟩, hpdvd⟩

/-- Truncating the divisor correction can only decrease it.  Unlike the exact
identity above, this comparison applies at cutoffs below `N`. -/
theorem liuCorrectionTruncated_le_liuCorrection
    (N z : ℕ) (hN : 0 < N) :
    liuCorrectionTruncated N z ≤ liuCorrection N := by
  classical
  unfold liuCorrectionTruncated liuCorrection
  rw [← Finset.prod_filter]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpbase, hpdvd⟩
    rcases Finset.mem_filter.mp hpbase with ⟨_, hpprime, hp2⟩
    exact Finset.mem_filter.mpr
     ⟨Nat.mem_primeFactors.mpr ⟨hpprime, hpdvd, hN.ne'⟩, hp2⟩
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpbase, _⟩
    exact (liuCorrectionFactor_pos (Finset.mem_filter.mp hpbase).2.2).le
  · intro p hp _
    exact one_le_liuCorrectionFactor (Finset.mem_filter.mp hp).2

/-- Liu's genuine source singular series: its finite divisor correction times
the convergent universal odd-prime product. -/
noncomputable def liuSingularSeries (N : ℕ) : ℝ :=
  liuCorrection N * liuUniversalProduct

theorem liuSingularSeries_source_formula (N : ℕ) :
    liuSingularSeries N =
      (N.primeFactors.filter (fun p => 2 < p)).prod
          (fun p => ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        ∏' p : ℕ, (1 + liuBaseDeviation p) := by
  rfl

theorem liuSingularSeries_pos (N : ℕ) : 0 < liuSingularSeries N := by
  exact mul_pos (liuCorrection_pos N) liuUniversalProduct_pos

/-- Liu's singular series is uniformly bounded below by its positive universal
Euler product; every divisor correction factor is at least one. -/
theorem liuUniversalProduct_le_liuSingularSeries (N : ℕ) :
    liuUniversalProduct ≤ liuSingularSeries N := by
  rw [liuSingularSeries]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (one_le_liuCorrection N) liuUniversalProduct_nonneg

theorem tendsto_liuSingularSeriesTruncated (N : ℕ) (hN : 0 < N) :
    Filter.Tendsto (liuSingularSeriesTruncated N) Filter.atTop
      (nhds (liuSingularSeries N)) := by
  rw [liuSingularSeries]
  apply Filter.Tendsto.congr' ?_
    (show Filter.Tendsto
      (fun z => liuCorrection N * liuUniversalProductTruncated z)
      Filter.atTop (nhds (liuCorrection N * liuUniversalProduct)) from
        tendsto_const_nhds.mul tendsto_liuUniversalProductTruncated)
  filter_upwards [Filter.eventually_ge_atTop N] with z hz
  symm
  rw [liuSingularSeriesTruncated_factorization,
    liuCorrectionTruncated_eq_liuCorrection hN hz]

/-- The universal Euler truncations approach the full product from above,
uniformly enough for the varying source integer used in Chen's sieve. -/
theorem eventually_liuUniversalProductTruncated_le
   (η : ℝ) (hη : 0 < η) :
   ∀ᶠ z : ℕ in Filter.atTop,
     liuUniversalProductTruncated z ≤ (1 + η) * liuUniversalProduct := by
  have hU : 0 < liuUniversalProduct := liuUniversalProduct_pos
  have h := tendsto_liuUniversalProductTruncated.eventually
   (Metric.ball_mem_nhds liuUniversalProduct (mul_pos hη hU))
  filter_upwards [h] with z hz
  rw [Real.dist_eq] at hz
  have hz' := (abs_lt.mp hz).2
  nlinarith

/-- Uniform upper comparison of every source truncation with Liu's genuine
singular series.  Missing divisor factors only decrease the correction, while
the universal Euler tail is independent of `N`. -/
theorem eventually_liuSingularSeriesTruncated_le
   (η : ℝ) (hη : 0 < η) :
   ∀ᶠ z : ℕ in Filter.atTop, ∀ N : ℕ, 0 < N →
     liuSingularSeriesTruncated N z ≤
       (1 + η) * liuSingularSeries N := by
  filter_upwards [eventually_liuUniversalProductTruncated_le η hη] with z hz N hN
  rw [liuSingularSeriesTruncated_factorization, liuSingularSeries]
  calc
   liuCorrectionTruncated N z * liuUniversalProductTruncated z ≤
       liuCorrection N * liuUniversalProductTruncated z :=
     mul_le_mul_of_nonneg_right
       (liuCorrectionTruncated_le_liuCorrection N z hN)
       (liuUniversalProductTruncated_pos z).le
   _ ≤ liuCorrection N * ((1 + η) * liuUniversalProduct) :=
     mul_le_mul_of_nonneg_left hz (liuCorrection_pos N).le
   _ = (1 + η) * (liuCorrection N * liuUniversalProduct) := by ring

/-- The positive tail quotient omitted by the universal truncation through `z`. -/
noncomputable def liuSingularSeriesTail (z : ℕ) : ℝ :=
  liuUniversalProduct / liuUniversalProductTruncated z

theorem liuSingularSeriesTail_pos (z : ℕ) :
    0 < liuSingularSeriesTail z := by
  exact div_pos liuUniversalProduct_pos (liuUniversalProductTruncated_pos z)

theorem liuSingularSeriesTail_le_one (z : ℕ) :
    liuSingularSeriesTail z ≤ 1 := by
  rw [liuSingularSeriesTail]
  exact (div_le_one (liuUniversalProductTruncated_pos z)).2
    (liuUniversalProduct_le_truncated z)

theorem tendsto_liuSingularSeriesTail_one :
    Filter.Tendsto liuSingularSeriesTail Filter.atTop (nhds 1) := by
  have hc : Filter.Tendsto (fun _ : ℕ => liuUniversalProduct) Filter.atTop
      (nhds liuUniversalProduct) := tendsto_const_nhds
  have h := hc.div tendsto_liuUniversalProductTruncated liuUniversalProduct_ne_zero
  change Filter.Tendsto
    ((fun _ : ℕ => liuUniversalProduct) / liuUniversalProductTruncated)
      Filter.atTop (nhds 1)
  simpa only [div_self liuUniversalProduct_ne_zero] using h

theorem liuSingularSeriesTruncatedAtN_eq_div_tail
    (N : ℕ) (hN : 0 < N) :
    liuSingularSeriesTruncated N N =
      liuSingularSeries N / liuSingularSeriesTail N := by
  rw [liuSingularSeriesTruncated_factorization,
    liuCorrectionTruncated_eq_liuCorrection hN le_rfl]
  unfold liuSingularSeries liuSingularSeriesTail
  field_simp [liuUniversalProduct_ne_zero,
    ne_of_gt (liuUniversalProductTruncated_pos N)]

/-- For even source integers, the legacy sieve proxy is exactly twice the
true Liu series divided by its positive finite-cutoff tail.  Since that tail
tends to `1`, the proxy has the wrong asymptotic normalization by a factor `2`. -/
theorem singularSeries_eq_two_mul_liuSingularSeries_div_tail
    (N : ℕ) (hNeven : Even N) (hN : 2 ≤ N) :
    singularSeries N =
      2 * (liuSingularSeries N / liuSingularSeriesTail N) := by
  rw [singularSeries_eq_two_mul_liuSingularSeriesTruncatedAtN N hNeven hN,
    liuSingularSeriesTruncatedAtN_eq_div_tail N (by omega)]

/-- The finite sieve-normalized proxy dominates twice Liu's genuine series.
The proof uses only the sign of the universal Euler tail, not fixed-`N`
convergence. -/
theorem two_mul_liuSingularSeries_le_singularSeries
    (N : ℕ) (hNeven : Even N) (hN : 2 ≤ N) :
    2 * liuSingularSeries N ≤ singularSeries N := by
  rw [singularSeries_eq_two_mul_liuSingularSeries_div_tail N hNeven hN]
  gcongr
  rw [le_div_iff₀ (liuSingularSeriesTail_pos N)]
  exact mul_le_of_le_one_right (liuSingularSeries_pos N).le
    (liuSingularSeriesTail_le_one N)

end MathlibNt.SieveTheory.SingularSeries
