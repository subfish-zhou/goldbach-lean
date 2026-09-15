import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSource
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackMain

/-! # Exact finite wiring of the fourth-row Gamma5 count

The range truncation uses actual source fibres, never a bound on the real
cutoff. The full product and all convolution multiplicities are retained.
-/
namespace Wu2008DoubleSieve
open Finset
open scoped Classical

/-- The original upper cutoff is exactly the classical exponent. -/
theorem fourthRowGamma5Link_cutoff (N d : ℕ) (δ : ℝ) :
    wuLocalCutoff N δ d (291 / 100) =
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma5ClassicalB := by
  norm_num [wuLocalCutoff, gamma5ClassicalB]

/-- Every selected factor of a nonempty source fibre is at most N. -/
theorem fourthRowGamma5Link_factor_bound {N m M r : ℕ} {z : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hr : r ∣ m)
    (hs : sourceSieveCount N m M z ≠ 0) : r ≤ N := by
  have hc : (sourceSieveCarrier N m M z).Nonempty := by
    apply card_pos.mp
    have hh : (sourceSieveCarrier N m M z).card ≠ 0 := by
      intro hh
      exact hs (by simp [sourceSieveCount, hh])
    omega
  obtain ⟨ell, hell⟩ := hc
  obtain ⟨hell, hp, hd, _⟩ := mem_filter.mp hell
  have hellN : ell ≤ N := by simpa using mem_range.mp hell
  have hne : ell ≠ N := by
    intro hh
    subst ell
    have htwo : 2 ∣ N := even_iff_two_dvd.mp he
    obtain hh | hh := (Nat.dvd_prime hp).mp htwo <;> omega
  exact (Nat.le_of_dvd (by omega : 0 < N - ell) (hr.trans hd)).trans (Nat.sub_le _ _)

/-- The bounded literal label set for a single old product. -/
noncomputable def fourthRowGamma5LinkPairs (N d : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  ((primeWindow N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (291 / 100))) ×ˢ
    (primeWindow N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (291 / 100)))).filter (fun pq => pq.1 < pq.2)

/-- Membership retains both coprimalities and the half-open window. -/
theorem fourthRowGamma5Link_pairs_iff (N d p q : ℕ) (δ : ℝ) :
    (p, q) ∈ fourthRowGamma5LinkPairs N d δ ↔
      p.Prime ∧ q.Prime ∧ p.Coprime N ∧ q.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (p : ℝ) ∧ p < q ∧
      (q : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma5ClassicalB := by
  simp only [fourthRowGamma5LinkPairs, mem_filter, mem_product, mem_primeWindow,
    fourthRowGamma5Link_cutoff, gamma5ClassicalS]
  constructor
  · rintro ⟨⟨⟨hp, hpN, hpa, _⟩, ⟨hq, hqN, _, hqc⟩⟩, hpq⟩
    exact ⟨hp, hq, hpN, hqN, hpa, hpq, hqc⟩
  · rintro ⟨hp, hq, hpN, hqN, hpa, hpq, hqc⟩
    have hpq' : (p : ℝ) < q := by exact_mod_cast hpq
    exact ⟨⟨⟨hp, hpN, hpa, hpq'.trans hqc⟩,
      ⟨hq, hqN, hpa.trans hpq'.le, hqc⟩⟩, hpq⟩

/-- A per-product finite sum reindexing, including zero fibres outside N+1. -/
theorem fourthRowGamma5Link_pair_sum {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (d : ℕ) (δ : ℝ) :
    fourthRowMotherPair N d N (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (291 / 100)) (wuLocalCutoff N δ d (103 / 25))
      (wuLocalCutoff N δ d (291 / 100)) =
    ∑ pq ∈ (range (N + 1) ×ˢ range (N + 1)).filter (fun pq =>
      pq.1.Prime ∧ pq.2.Prime ∧ pq.1.Coprime N ∧ pq.2.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (pq.1 : ℝ) ∧ pq.1 < pq.2 ∧
      (pq.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma5ClassicalB),
      (sourceSieveCount N (d * pq.1 * pq.2) (d * N)
        (wuLocalCutoff N δ d gamma5ClassicalS) : ℝ) := by
  let X := fourthRowGamma5LinkPairs N d δ
  let Y := X.filter (fun pq => pq.1 ≤ N ∧ pq.2 ≤ N)
  have hY : Y = (range (N + 1) ×ˢ range (N + 1)).filter (fun pq =>
      pq.1.Prime ∧ pq.2.Prime ∧ pq.1.Coprime N ∧ pq.2.Coprime N ∧
      wuLocalCutoff N δ d gamma5ClassicalS ≤ (pq.1 : ℝ) ∧ pq.1 < pq.2 ∧
      (pq.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / d) ^ gamma5ClassicalB) := by
    ext pq
    rcases pq with ⟨p, q⟩
    simp only [Y, X, mem_filter, fourthRowGamma5Link_pairs_iff, mem_product, mem_range,
      Nat.lt_succ_iff]
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
      have hq := fourthRowGamma5Link_factor_bound hN he (dvd_mul_left pq.2 (d * pq.1)) hz
      exact hn (mem_filter.mpr ⟨hpq, hp, hq⟩)
    simp [hz]
  rw [hsum]
  simp only [X, fourthRowGamma5LinkPairs, sum_filter, sum_product, gamma5ClassicalS]
  unfold fourthRowMotherPair
  rw [sum_comm]

/-- Exact physical identification, valid for arbitrary real delta and all windows. -/
theorem fourthRowGamma5Link_count_eq {i N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (δ : ℝ) (W : Fin i → Finset ℕ) :
    fourthRowMotherGamma5 N δ W =
      gamma5ClassicalCount N δ W (gamma5ClassicalLabels N δ W) := by
  unfold fourthRowMotherGamma5 gamma5ClassicalCount gamma5ClassicalLabels
  simp only [sum_filter, sum_product]
  apply sum_congr rfl
  intro d _
  rw [fourthRowGamma5Link_pair_sum hN he]
  simp only [sum_filter, sum_product, mul_sum, mul_ite, mul_zero, gamma5ClassicalProduct]

end Wu2008DoubleSieve
