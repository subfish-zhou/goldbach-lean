import MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBoxRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachLogDarboux

open Finset Set
open scoped BigOperators Interval NNReal
namespace MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle
open LiLiuGoldbachLogDarboux

noncomputable def pairLogCoordinate (N : ℕ) (p : ℕ × ℕ) : ℝ × ℝ :=
  (primeLogExponent N p.1, primeLogExponent N p.2)

theorem mem_coprimePrimeLogRectanglePairs_iff_coordinate {N : ℕ} (hN : 1 < N)
    {p : ℕ × ℕ} {a b c d : ℝ} :
    p ∈ coprimePrimeLogRectanglePairs N a b c d ↔
      p.1.Prime ∧ p.2.Prime ∧ Nat.Coprime (p.1*p.2) N ∧
        pairLogCoordinate N p ∈ Ioc a b ×ˢ Ioc c d := by
  classical
  change p ∈ (primeLogIntervalPrimes N a b ×ˢ primeLogIntervalPrimes N c d).filter
    (fun p => Nat.Coprime (p.1*p.2) N) ↔ _
  simp only [mem_filter, mem_product, mem_primeLogIntervalPrimes]
  constructor
  · rintro ⟨⟨⟨hp,hpab⟩,⟨hq,hqcd⟩⟩,hcop⟩
    exact ⟨hp,hq,hcop,(primeLogExponent_mem_interval_iff hN hp.pos a b).mpr hpab,
      (primeLogExponent_mem_interval_iff hN hq.pos c d).mpr hqcd⟩
  · rintro ⟨hp,hq,hcop,hxy⟩
    exact ⟨⟨⟨hp,(primeLogExponent_mem_interval_iff hN hp.pos a b).mp hxy.1⟩,
      ⟨hq,(primeLogExponent_mem_interval_iff hN hq.pos c d).mp hxy.2⟩⟩,hcop⟩

noncomputable def coprimePrimeKernelRectangle (N : ℕ) (a b c d : ℝ)
    (K : ℝ × ℝ → ℝ) : ℝ :=
  ∑ p ∈ coprimePrimeLogRectanglePairs N a b c d,
    K (pairLogCoordinate N p) / ((p.1 : ℝ)*p.2)

/-- A lower grid is transported using disjoint boxes, not a cover with free overlap. -/
theorem weighted_coprime_grid_le_kernel {N n : ℕ} (hN : 1 < N) (hn : 0 < n)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (K : ℝ × ℝ → ℝ) (coeff : Fin n × Fin n → ℝ)
    (hpos : ∀ x ∈ Ioc a b ×ˢ Ioc c d, 0 ≤ K x)
    (hcoeff : ∀ q x, x ∈ cell a b c d n q → coeff q ≤ K x) :
    (∑ q : Fin n × Fin n, coeff q * coprimePrimeReciprocalLogRectangle N
      (grid a b n q.1) (grid a b n (q.1.val+1))
      (grid c d n q.2) (grid c d n (q.2.val+1))) ≤
      coprimePrimeKernelRectangle N a b c d K := by
  classical
  let boxes (q : Fin n × Fin n) := coprimePrimeLogRectanglePairs N
    (grid a b n q.1) (grid a b n (q.1.val+1))
    (grid c d n q.2) (grid c d n (q.2.val+1))
  have hc : ∀ q p, p ∈ boxes q → pairLogCoordinate N p ∈ cell a b c d n q := by
    intro q p hp
    exact ((mem_coprimePrimeLogRectanglePairs_iff_coordinate hN).mp hp).2.2.2
  have hs : ∀ q, boxes q ⊆ coprimePrimeLogRectanglePairs N a b c d := by
    intro q p hp
    obtain ⟨hp1,hp2,hcop,hxy⟩ := (mem_coprimePrimeLogRectanglePairs_iff_coordinate hN).mp hp
    exact (mem_coprimePrimeLogRectanglePairs_iff_coordinate hN).mpr
      ⟨hp1,hp2,hcop,cell_subset hab hcd hn q hxy⟩
  have hd : (↑(Finset.univ : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)).PairwiseDisjoint boxes := by
    intro q _ r _ hqr
    change Disjoint (boxes q) (boxes r)
    rw [Finset.disjoint_left]
    intro p hp hpr
    exact Set.disjoint_left.mp
      (cell_disjoint hab hcd n (Set.mem_univ q) (Set.mem_univ r) hqr) (hc q p hp) (hc r p hpr)
  calc
    _ = ∑ q : Fin n × Fin n, ∑ p ∈ boxes q,
        coeff q / ((p.1 : ℝ)*p.2) := by
      simp only [coprimePrimeReciprocalLogRectangle, Finset.mul_sum, mul_one_div, boxes]
    _ ≤ ∑ q : Fin n × Fin n, ∑ p ∈ boxes q,
        K (pairLogCoordinate N p) / ((p.1 : ℝ)*p.2) := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right (hcoeff q _ (hc q p hp)) (by positivity)
    _ = ∑ p ∈ Finset.univ.biUnion boxes,
        K (pairLogCoordinate N p) / ((p.1 : ℝ)*p.2) := by
      rw [Finset.sum_biUnion hd]
    _ ≤ coprimePrimeKernelRectangle N a b c d K := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨q,_,hq⟩ := Finset.mem_biUnion.mp hp
        exact hs q hq
      · intro p hp _
        exact div_nonneg (hpos _ ((mem_coprimePrimeLogRectanglePairs_iff_coordinate hN).mp hp).2.2.2)
          (by positivity)

/-- Fixed positive rectangles: actual copN prime sums dominate the kernel integral asymptotically.
The finite grid is chosen before the common prime-count threshold. -/
theorem exists_coprimePrimeKernelRectangle_lower {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    {K : ℝ × ℝ → ℝ} {L : ℝ≥0} (hK : LipschitzWith L K)
    (hpos : ∀ x ∈ Ioc a b ×ˢ Ioc c d, 0 ≤ K x)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∫ u in a..b, ∫ v in c..d, K (u,v)/(u*v)) - η ≤
        coprimePrimeKernelRectangle N a b c d K := by
  obtain ⟨n,hn,w,_,hw,hi⟩ := exists_darboux ha hab hc hcd hK hpos (half_pos hη)
  obtain ⟨N₀,hN₀,hlim⟩ := exists_abs_weighted_sum_coprimePrimeReciprocalLogRectangle_sub_lt
    (Finset.univ : Finset (Fin n × Fin n)) w
    (fun q => grid a b n q.1) (fun q => grid a b n (q.1.val+1))
    (fun q => grid c d n q.2) (fun q => grid c d n (q.2.val+1))
    (fun q _ => ha.trans_le (grid_bounds hab.le hn (Nat.le_of_lt q.1.isLt)).1)
    (fun q _ => grid_strict hab hn q.1.val)
    (fun q _ => hc.trans_le (grid_bounds hcd.le hn (Nat.le_of_lt q.2.isLt)).1)
    (fun q _ => grid_strict hcd hn q.2.val) 2 (half_pos hη)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  have he := (abs_lt.mp (hlim N hN)).1
  have hf := weighted_coprime_grid_le_kernel (show 1 < N by omega) hn hab.le hcd.le K w hpos hw
  unfold cellMass at hi
  linarith

end MathlibNt.SieveTheory.LiuWeight
