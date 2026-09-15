import MathlibNt.Wu2008DoubleSieve.FourthRowGamma5LinkFinite
import MathlibNt.Wu2008DoubleSieve.Gamma6BaseFinite

/-! # Exact finite Gamma6 mother-to-label transport

The original source count, modulus, cutoff and convolution coefficient are
unchanged. Actual zero fibres justify range restriction. A prime in the
first half-open window forces its nonnegative real base to exceed one,
so no source-box premise is needed to recover the order of the two primes.
-/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

/-- The three original upper/lower endpoints have exactly the Base exponents. -/
theorem fourthRowGamma6Link_cutoffs (N d : ℕ) (δ : ℝ) :
    wuLocalCutoff N δ d (89 / 25) =
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ∧
    wuLocalCutoff N δ d (291 / 100) =
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseC ∧
    wuLocalCutoff N δ d (5 / 2) =
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseF := by
  norm_num [wuLocalCutoff, gamma6BaseB, gamma6BaseC, gamma6BaseF]

/-- A prime in the first window forces R>1, even for arbitrary delta and d. -/
theorem fourthRowGamma6Link_prime_order (N d p q : ℕ) (δ : ℝ)
    (hp : p.Prime)
    (hpb : (p : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB)
    (hqc : ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseC ≤ (q : ℝ)) :
    p < q := by
  have hR0 : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / d := by positivity
  have hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d := by
    by_contra h
    have hpow := Real.rpow_le_one hR0 (le_of_not_gt h)
      (show 0 ≤ gamma6BaseB by norm_num [gamma6BaseB])
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  exact_mod_cast gamma6Base_prime_order hR hpb hqc

/-- Exact rectangular reindexing; discarded labels have zero actual source fibre. -/
theorem fourthRowGamma6Link_pair_sum {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (d : ℕ) (δ : ℝ) :
    fourthRowMotherPair N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (89 / 25)) (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2)) =
    ∑ pq ∈ (range (N + 1) ×ˢ range (N + 1)).filter (fun pq =>
      pq.1.Prime ∧ pq.2.Prime ∧ pq.1.Coprime N ∧ pq.2.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (pq.1 : ℝ) ∧
      (pq.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ∧
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseC ≤ (pq.2 : ℝ) ∧
      (pq.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseF),
      (sourceSieveCount N (d * pq.1 * pq.2) (d * N)
        (wuLocalCutoff N δ d gamma5ClassicalS) : ℝ) := by
  let X := (primeWindow N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (89 / 25))) ×ˢ
    (primeWindow N (wuLocalCutoff N δ d (291 / 100))
      (wuLocalCutoff N δ d (5 / 2)))
  let Y := X.filter (fun pq => pq.1 ≤ N ∧ pq.2 ≤ N)
  have hX (p q : ℕ) : (p, q) ∈ X ↔
      p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (p : ℝ) ∧
      (p : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ∧
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseC ≤ (q : ℝ) ∧
      (q : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseF := by
    simp only [X, mem_product, mem_primeWindow,
      (fourthRowGamma6Link_cutoffs N d δ).1,
      (fourthRowGamma6Link_cutoffs N d δ).2.1,
      (fourthRowGamma6Link_cutoffs N d δ).2.2, gamma5ClassicalS]
    tauto
  have hY : Y = (range (N + 1) ×ˢ range (N + 1)).filter (fun pq =>
      pq.1.Prime ∧ pq.2.Prime ∧ pq.1.Coprime N ∧ pq.2.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (pq.1 : ℝ) ∧
      (pq.1 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseB ∧
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseC ≤ (pq.2 : ℝ) ∧
      (pq.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma6BaseF) := by
    ext pq
    rcases pq with ⟨p, q⟩
    simp only [Y, mem_filter, hX, mem_product, mem_range, Nat.lt_succ_iff]
    tauto
  rw [← hY]
  have hsum : (∑ pq ∈ Y, (sourceSieveCount N (d * pq.1 * pq.2) (d * N)
      (wuLocalCutoff N δ d gamma5ClassicalS) : ℝ)) =
      ∑ pq ∈ X, (sourceSieveCount N (d * pq.1 * pq.2) (d * N)
      (wuLocalCutoff N δ d gamma5ClassicalS) : ℝ) := by
    apply sum_subset (filter_subset _ _)
    intro pq hpq hn
    have hz : sourceSieveCount N (d * pq.1 * pq.2) (d * N)
        (wuLocalCutoff N δ d gamma5ClassicalS) = 0 := by
      by_contra hz
      have hp := fourthRowGamma5Link_factor_bound hN he
        ((dvd_mul_left pq.1 d).trans (dvd_mul_right (d * pq.1) pq.2)) hz
      have hq := fourthRowGamma5Link_factor_bound hN he
        (dvd_mul_left pq.2 (d * pq.1)) hz
      exact hn (mem_filter.mpr ⟨hpq, hp, hq⟩)
    simp [hz]
  rw [hsum]
  have horder : ∀ pq ∈ X, pq.1 < pq.2 := by
    intro pq hpq
    obtain ⟨hp, _, _, _, _, hpb, hqc, _⟩ := (hX pq.1 pq.2).mp hpq
    exact fourthRowGamma6Link_prime_order N d pq.1 pq.2 δ hp hpb hqc
  calc
    _ = ∑ pq ∈ X, if pq.1 < pq.2 then
        (sourceSieveCount N (d * pq.1 * pq.2) (d * N)
          (wuLocalCutoff N δ d gamma5ClassicalS) : ℝ) else 0 := by
      simp only [X, sum_product, gamma5ClassicalS]
      unfold fourthRowMotherPair
      rw [sum_comm]
    _ = _ := sum_congr rfl (fun pq hpq => if_pos (horder pq hpq))

/-- The actual finite mother count equals the existing count on actual Base labels.
All real delta and every original convolution window are allowed. -/
theorem fourthRowGamma6Link_count_eq {i N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowMotherGamma6 N δ W =
      gamma5ClassicalCount N δ W (gamma6BaseLabels N δ W) := by
  unfold fourthRowMotherGamma6 gamma5ClassicalCount gamma6BaseLabels
  simp only [sum_filter, sum_product]
  apply sum_congr rfl
  intro d _
  rw [fourthRowGamma6Link_pair_sum hN he]
  simp only [sum_filter, sum_product, mul_sum, mul_ite, mul_zero, gamma5ClassicalProduct]

end Wu2008DoubleSieve
