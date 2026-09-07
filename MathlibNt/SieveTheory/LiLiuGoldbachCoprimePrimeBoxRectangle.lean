import MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBox

/-! Actual coprime half-open boxes and finite signed weighted limits, retaining the diagonal. -/
namespace MathlibNt.SieveTheory.LiuWeight
open Filter Finset
open scoped Topology BigOperators
open PrimeReciprocalLogScale PrimeReciprocalLogRectangle

noncomputable def coprimePrimeLogRectanglePairs
    (N : ℕ) (a b c d : ℝ) : Finset (ℕ × ℕ) :=
  (primeLogRectanglePairs N a b c d).filter fun p => Nat.Coprime (p.1 * p.2) N

theorem coprimePrimeLogRectanglePairs_eq_product (N : ℕ) (a b c d : ℝ) :
    coprimePrimeLogRectanglePairs N a b c d =
      coprimePrimeLogIntervalPrimes N a b ×ˢ coprimePrimeLogIntervalPrimes N c d := by
  classical
  ext p
  change (p ∈ (primeLogIntervalPrimes N a b ×ˢ primeLogIntervalPrimes N c d).filter
    (fun p => Nat.Coprime (p.1 * p.2) N)) ↔ _
  simp only [mem_filter, mem_product, coprimePrimeLogIntervalPrimes]
  constructor
  · rintro ⟨⟨hr, hs⟩, hcop⟩
    have hc := Nat.coprime_mul_iff_left.mp hcop
    exact ⟨⟨hr, (mem_primeLogIntervalPrimes.mp hr).1.coprime_iff_not_dvd.mp hc.1⟩,
      ⟨hs, (mem_primeLogIntervalPrimes.mp hs).1.coprime_iff_not_dvd.mp hc.2⟩⟩
  · rintro ⟨⟨hr, hrd⟩, ⟨hs, hsd⟩⟩
    exact ⟨⟨hr, hs⟩, Nat.coprime_mul_iff_left.mpr
      ⟨(mem_primeLogIntervalPrimes.mp hr).1.coprime_iff_not_dvd.mpr hrd,
        (mem_primeLogIntervalPrimes.mp hs).1.coprime_iff_not_dvd.mpr hsd⟩⟩

noncomputable def coprimePrimeReciprocalLogRectangle (N : ℕ) (a b c d : ℝ) : ℝ :=
  ∑ p ∈ coprimePrimeLogRectanglePairs N a b c d, 1 / ((p.1 : ℝ) * p.2)

theorem coprimePrimeReciprocalLogRectangle_eq_mul (N : ℕ) (a b c d : ℝ) :
    coprimePrimeReciprocalLogRectangle N a b c d =
      coprimePrimeReciprocalLogInterval N a b * coprimePrimeReciprocalLogInterval N c d := by
  unfold coprimePrimeReciprocalLogRectangle
  rw [coprimePrimeLogRectanglePairs_eq_product, sum_product]
  unfold coprimePrimeReciprocalLogInterval
  rw [sum_mul]
  apply sum_congr rfl
  intro r _
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  simp only [one_div, mul_inv]

theorem tendsto_coprimePrimeReciprocalLogRectangle {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun N : ℕ => coprimePrimeReciprocalLogRectangle N a b c d) atTop
      (nhds (logarithmicRectangleMass a b c d)) := by
  simpa only [coprimePrimeReciprocalLogRectangle_eq_mul, logarithmicRectangleMass] using
    (tendsto_coprimePrimeReciprocalLogInterval ha hab).mul
      (tendsto_coprimePrimeReciprocalLogInterval hc hcd)

/-- The literal filtered original carrier, without a carrier-identification premise. -/
theorem tendsto_sum_filter_coprime_primeLogRectanglePairs {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ (primeLogRectanglePairs N a b c d).filter
        (fun p => Nat.Coprime (p.1 * p.2) N), 1 / ((p.1 : ℝ) * p.2)) atTop
      (nhds (logarithmicRectangleMass a b c d)) :=
  tendsto_coprimePrimeReciprocalLogRectangle ha hab hc hcd

variable {ι : Type*}

/-- Fixed finite signed weights: an exact sum limit, not multiplication of inequalities. -/
theorem tendsto_weighted_sum_coprimePrimeReciprocalLogRectangle
    (s : Finset ι) (w a b c d : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i)
    (hc : ∀ i ∈ s, 0 < c i) (hcd : ∀ i ∈ s, c i < d i) :
    Tendsto (fun N : ℕ => ∑ i ∈ s, w i *
      coprimePrimeReciprocalLogRectangle N (a i) (b i) (c i) (d i)) atTop
      (nhds (∑ i ∈ s, w i * logarithmicRectangleMass (a i) (b i) (c i) (d i))) := by
  refine tendsto_finsetSum s ?_
  intro i hi
  exact (tendsto_coprimePrimeReciprocalLogRectangle
    (ha i hi) (hab i hi) (hc i hi) (hcd i hi)).const_mul (w i)

/-- The finite box family and weights precede a common threshold above Nmin. -/
theorem exists_abs_weighted_sum_coprimePrimeReciprocalLogRectangle_sub_lt
    (s : Finset ι) (w a b c d : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hab : ∀ i ∈ s, a i < b i)
    (hc : ∀ i ∈ s, 0 < c i) (hcd : ∀ i ∈ s, c i < d i)
    (Nmin : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, Nmin ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      |(∑ i ∈ s, w i * coprimePrimeReciprocalLogRectangle N (a i) (b i) (c i) (d i)) -
        ∑ i ∈ s, w i * logarithmicRectangleMass (a i) (b i) (c i) (d i)| < ε := by
  have h := tendsto_weighted_sum_coprimePrimeReciprocalLogRectangle s w a b c d ha hab hc hcd
  have he : ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ s, w i * coprimePrimeReciprocalLogRectangle N (a i) (b i) (c i) (d i)) -
        ∑ i ∈ s, w i * logarithmicRectangleMass (a i) (b i) (c i) (d i)| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp h ε hε)
  obtain ⟨M, hM⟩ := eventually_atTop.mp he
  exact ⟨max Nmin M, le_max_left _ _, fun N hN => hM N ((le_max_right _ _).trans hN)⟩

end MathlibNt.SieveTheory.LiuWeight
