import MathlibNt.SieveTheory.LiLiuGoldbachPrimeDarbouxLower
import MathlibNt.SieveTheory.LiLiuGoldbachSymmetricPairs

open Finset Set
open scoped BigOperators Interval NNReal
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight

noncomputable def goldbachPairKernelSum (N : ℕ) (K : ℝ × ℝ → ℝ)
    (T : Finset (ℕ × ℕ)) : ℝ :=
  ∑ p ∈ T, K (pairLogCoordinate N p) / ((p.1 : ℝ)*p.2)

theorem coprimePrimeLogRectanglePairs_subset_closed (N : ℕ) (a b c d : ℝ) :
    coprimePrimeLogRectanglePairs N a b c d ⊆
      (goldbachClosedPrimes N ((N : ℝ)^a) ((N : ℝ)^b)) ×ˢ
      (goldbachClosedPrimes N ((N : ℝ)^c) ((N : ℝ)^d)) := by
  rw [coprimePrimeLogRectanglePairs_eq_product]
  intro p hp
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hp
  obtain ⟨hp,hnp⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq,hnq⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpp,hlp,hup⟩ := mem_primeLogIntervalPrimes.mp hp
  obtain ⟨hqp,hlq,huq⟩ := mem_primeLogIntervalPrimes.mp hq
  exact Finset.mem_product.mpr ⟨mem_goldbachClosedPrimes_iff.mpr ⟨hpp,hnp,hlp.le,hup⟩,
    mem_goldbachClosedPrimes_iff.mpr ⟨hqp,hnq,hlq.le,huq⟩⟩

theorem coprimePrimeKernelRectangle_le_closed (N : ℕ) (a b c d : ℝ)
    (K : ℝ × ℝ → ℝ) (hK : ∀ x, 0 ≤ K x) :
    coprimePrimeKernelRectangle N a b c d K ≤
      goldbachPairKernelSum N K
        ((goldbachClosedPrimes N ((N : ℝ)^a) ((N : ℝ)^b)) ×ˢ
          (goldbachClosedPrimes N ((N : ℝ)^c) ((N : ℝ)^d))) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (coprimePrimeLogRectanglePairs_subset_closed N a b c d)
  intro p _ _
  exact div_nonneg (hK _) (by positivity)

/-- The closed square retains its diagonal and all original copN labels. -/
theorem goldbachG6_coprime_square_kernel_le (N : ℕ) (a b : ℝ)
    (K : ℝ × ℝ → ℝ) (hK : ∀ x, 0 ≤ K x)
    (hsym : ∀ u v, K (u,v) = K (v,u)) :
    (1/2 : ℝ)*coprimePrimeKernelRectangle N a b a b K ≤
      goldbachPairKernelSum N K (goldbachG6Pairs N ((N : ℝ)^a) ((N : ℝ)^b)) := by
  have h := coprimePrimeKernelRectangle_le_closed N a b a b K hK
  have ht := goldbachG6Pairs_half_square_le N ((N : ℝ)^a) ((N : ℝ)^b)
    (fun r s => K (pairLogCoordinate N (r,s))/((r : ℝ)*s))
    (fun r s => by simp only [pairLogCoordinate]; rw [hsym, mul_comm (r : ℝ) (s : ℝ)] )
    (fun r _ => div_nonneg (hK _) (by positivity))
  unfold goldbachPairKernelSum at h ⊢
  rw [Finset.sum_product] at h
  linarith

/-- General symmetric nonnegative Lipschitz kernels on the original G6 labels. -/
theorem exists_goldbachG6_kernel_integral_lower {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {K : ℝ × ℝ → ℝ} {L : ℝ≥0} (hK : LipschitzWith L K) (hpos : ∀ x, 0 ≤ K x)
    (hsym : ∀ u v, K (u,v) = K (v,u)) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (1/2 : ℝ)*(∫ u in a..b, ∫ v in a..b, K (u,v)/(u*v))-η ≤
        goldbachPairKernelSum N K (goldbachG6Pairs N ((N : ℝ)^a) ((N : ℝ)^b)) := by
  obtain ⟨N₀,hN₀,hN⟩ := exists_coprimePrimeKernelRectangle_lower ha hab ha hab hK
    (fun x _ => hpos x) (mul_pos (by norm_num : (0 : ℝ)<2) hη)
  refine ⟨N₀,hN₀,?_⟩
  intro N hn
  have h := hN N hn
  have hfinite := goldbachG6_coprime_square_kernel_le N a b K hpos hsym
  linarith

/-- The G7 shared closed boundary is retained; the lower rectangle is only a subset. -/
theorem exists_goldbachG7_kernel_integral_lower {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {K : ℝ × ℝ → ℝ} {L : ℝ≥0} (hK : LipschitzWith L K) (hpos : ∀ x, 0 ≤ K x)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∫ u in a..b, ∫ v in b..c, K (u,v)/(u*v))-η ≤
        goldbachPairKernelSum N K
          (goldbachG7Pairs N ((N : ℝ)^a) ((N : ℝ)^b) ((N : ℝ)^c)) := by
  obtain ⟨N₀,hN₀,hN⟩ := exists_coprimePrimeKernelRectangle_lower ha hab (ha.trans hab) hbc hK
    (fun x _ => hpos x) hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hn
  exact (hN N hn).trans (coprimePrimeKernelRectangle_le_closed N a b b c K hpos)

/-- A common threshold and an explicitly split error budget for both original families. -/
theorem exists_goldbachG67_kernel_integral_lower {a b c : ℝ}
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    {K : ℝ × ℝ → ℝ} {L : ℝ≥0} (hK : LipschitzWith L K) (hpos : ∀ x, 0 ≤ K x)
    (hsym : ∀ u v, K (u,v) = K (v,u)) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (1/2 : ℝ)*(∫ u in a..b, ∫ v in a..b, K (u,v)/(u*v)) +
      (∫ u in a..b, ∫ v in b..c, K (u,v)/(u*v)) - η ≤
        goldbachPairKernelSum N K (goldbachG6Pairs N ((N : ℝ)^a) ((N : ℝ)^b)) +
        goldbachPairKernelSum N K
          (goldbachG7Pairs N ((N : ℝ)^a) ((N : ℝ)^b) ((N : ℝ)^c)) := by
  obtain ⟨N6,hN6,h6⟩ := exists_goldbachG6_kernel_integral_lower ha hab hK hpos hsym (half_pos hη)
  obtain ⟨N7,_,h7⟩ := exists_goldbachG7_kernel_integral_lower ha hab hbc hK hpos (half_pos hη)
  refine ⟨max N6 N7,by omega,?_⟩
  intro N hN
  have h6' := h6 N (by omega)
  have h7' := h7 N (by omega)
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
