import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassRiemann

/-!
# Simultaneous actual packing for a finite coarse rectangle family

Both the coarse label and the two microgrid labels are retained by
nested pairing. Separation is tested on the actual prime windows.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem truncatedSixthMass_grid_window_subset {N j : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hj : j < truncatedSixthMassGridSize N a b) :
    primeWindow N
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1) / truncatedSixthMassDelta N)
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1)) ⊆
      primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b) := by
  intro p hp
  obtain ⟨hp0, hpc, hlo, hhi⟩ := mem_primeWindow.mp hp
  have hg := truncatedSixthMass_grid_point_bounds hN hab hj
  rw [truncatedSixthMass_grid_lower_endpoint hN] at hlo
  refine mem_primeWindow.mpr ⟨hp0, hpc, ?_, ?_⟩
  · exact (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hg.1).trans hlo
  · exact hhi.trans_le (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) hg.2)

theorem truncatedSixthMass_packing_box_subset {N : ℕ} {a b c d : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hcd : c ≤ d) {j : ℕ × ℕ}
    (hj : j ∈ truncatedSixthMassPacking N a b c d) :
    truncatedSixthMassPackingBox N a c j ⊆
      primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ×ˢ
        primeWindow N ((N : ℝ) ^ c) ((N : ℝ) ^ d) := by
  obtain ⟨hj1, hj2⟩ := mem_product.mp hj
  intro p hp
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  exact mem_product.mpr
    ⟨truncatedSixthMass_grid_window_subset hN hab (mem_range.mp hj1) hp1,
      truncatedSixthMass_grid_window_subset hN hcd (mem_range.mp hj2) hp2⟩

theorem truncatedSixthMass_rectangle_disjoint {N : ℕ} {a b c d a' b' c' d' : ℝ}
    (hN : 1 < N) (hsep : b ≤ a' ∨ b' ≤ a ∨ d ≤ c' ∨ d' ≤ c) :
    Disjoint
      (primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ×ˢ
        primeWindow N ((N : ℝ) ^ c) ((N : ℝ) ^ d))
      (primeWindow N ((N : ℝ) ^ a') ((N : ℝ) ^ b') ×ˢ
        primeWindow N ((N : ℝ) ^ c') ((N : ℝ) ^ d')) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hp1, hp2⟩ := mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := mem_product.mp hq
  have hcontra {u v : ℝ} {p : ℕ} (huv : u ≤ v)
      (hu : (p : ℝ) < (N : ℝ) ^ u) (hv : (N : ℝ) ^ v ≤ p) : False :=
    (not_lt_of_ge (hv.trans' (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le) huv))) hu
  rcases hsep with h | h | h | h
  · exact hcontra h (mem_primeWindow.mp hp1).2.2.2 (mem_primeWindow.mp hq1).2.2.1
  · exact hcontra h (mem_primeWindow.mp hq1).2.2.2 (mem_primeWindow.mp hp1).2.2.1
  · exact hcontra h (mem_primeWindow.mp hp2).2.2.2 (mem_primeWindow.mp hq2).2.2.1
  · exact hcontra h (mem_primeWindow.mp hq2).2.2.2 (mem_primeWindow.mp hp2).2.2.1

theorem truncatedSixthMass_family_actual {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (K : Finset ℕ) (a b c d s : ℕ → ℝ)
    (hg : ∀ k ∈ K, a k ≤ b k ∧ c k ≤ d k ∧
      truncatedSixthLowerAlpha ≤ a k ∧ truncatedSixthLowerBeta ≤ c k ∧
      truncatedSixthLowerAdmissibleRegion δ (b k) (d k))
    (hs : ∀ k ∈ K, 2 ≤ s k ∧ s k ≤ 5 ∧ s k ≤ truncatedSixthLowerS δ (b k) (d k))
    (hsep : ∀ k ∈ K, ∀ l ∈ K, k ≠ l →
      b k ≤ a l ∨ b l ≤ a k ∨ d k ≤ c l ∨ d l ≤ c k) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerWedgePairs N δ) +
        (∑ k ∈ K, (wuLowerCoefficient (s k) + wuImprovementLimit false δ (s k) - η) *
          truncatedSixthMassPackingTheta N δ (a k) (b k) (c k) (d k)) -
        ε * truncatedSixthMassScale N ≤
        (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
          ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
          ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, h⟩ := truncatedSixthLower_finite_packing_actual hδ hδhi hη hηhi hε
    (K.image s) (by
      intro t ht
      obtain ⟨k, hk, rfl⟩ := mem_image.mp ht
      exact ⟨(hs k hk).1, (hs k hk).2.1⟩)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have hN1 : 1 < N := by omega
  let J := fun k => truncatedSixthMassPacking N (a k) (b k) (c k) (d k)
  let encode := fun (k : ℕ) (j : ℕ × ℕ) => Nat.pair k (Nat.pair j.1 j.2)
  let I := K.biUnion (fun k => (J k).image (encode k))
  let key := fun n => (Nat.unpair n).1
  let micro := fun n => Nat.unpair (Nat.unpair n).2
  let x := fun n => truncatedSixthMassGridPoint N (a (key n)) ((micro n).1 + 1)
  let y := fun n => truncatedSixthMassGridPoint N (c (key n)) ((micro n).2 + 1)
  have hdecode (n : ℕ) (hn : n ∈ I) : key n ∈ K ∧ micro n ∈ J (key n) := by
    obtain ⟨k, hk, himage⟩ := mem_biUnion.mp hn
    obtain ⟨j, hji, rfl⟩ := mem_image.mp himage
    simpa only [key, micro, encode, Nat.unpair_pair] using And.intro hk hji
  have hgeom (n : ℕ) (hn : n ∈ I) :
      truncatedSixthLowerAdmissibleRegion δ (x n) (y n) ∧
      (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (N : ℝ) ^ x n / truncatedSixthMassDelta N ∧
      (N : ℝ) ^ truncatedSixthLowerBeta ≤ (N : ℝ) ^ y n / truncatedSixthMassDelta N := by
    have hk := hg (key n) (hdecode n hn).1
    exact truncatedSixthMass_packing_admissible hN1 hk.1 hk.2.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
      (hdecode n hn).2
  have hdisj : Set.PairwiseDisjoint (I : Set ℕ)
      (fun n => truncatedSixthLowerBoxPairs N (truncatedSixthMassDelta N) (x n) (y n)) := by
    intro n hn m hm hnm
    have hnk := (hdecode n hn).1
    have hmk := (hdecode m hm).1
    change Disjoint (truncatedSixthMassPackingBox N (a (key n)) (c (key n)) (micro n))
      (truncatedSixthMassPackingBox N (a (key m)) (c (key m)) (micro m))
    by_cases hk : key n = key m
    · rw [← hk]
      apply truncatedSixthMass_packing_disjoint hN1
      intro hj
      apply hnm
      have hcode := congrArg₂ encode hk hj
      simpa only [encode, key, micro, Nat.pair_unpair] using hcode
    · exact (truncatedSixthMass_rectangle_disjoint hN1 (hsep _ hnk _ hmk hk)).mono
        (truncatedSixthMass_packing_box_subset hN1 (hg _ hnk).1 (hg _ hnk).2.1 (hdecode n hn).2)
        (truncatedSixthMass_packing_box_subset hN1 (hg _ hmk).1 (hg _ hmk).2.1 (hdecode m hm).2)
  have hcount := h N hN he (truncatedSixthMassDelta N)
    (truncatedSixthMass_delta_legal hN1).2.1 (truncatedSixthMass_delta_legal hN1).2.2
    I x y (fun n => s (key n))
    (fun n hn => (hgeom n hn).1) (fun n hn => (hgeom n hn).2.1) (fun n hn => (hgeom n hn).2.2)
    (fun n hn => ⟨mem_image_of_mem s (hdecode n hn).1,
      truncatedSixthMass_packing_grid_parameter hN1 (hg _ (hdecode n hn).1).1
        (hg _ (hdecode n hn).1).2.1 (hs _ (hdecode n hn).1).2.2 (hdecode n hn).2⟩) hdisj
  have hsum :
      (∑ n ∈ I, (wuLowerCoefficient (s (key n)) + wuImprovementLimit false δ (s (key n)) - η) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
          (convolutionWuWindows N (truncatedSixthMassDelta N)
            ![(N : ℝ) ^ y n, (N : ℝ) ^ x n])) =
      ∑ k ∈ K, (wuLowerCoefficient (s k) + wuImprovementLimit false δ (s k) - η) *
        truncatedSixthMassPackingTheta N δ (a k) (b k) (c k) (d k) := by
    dsimp only [I]
    rw [sum_biUnion]
    · apply sum_congr rfl
      intro k _
      rw [sum_image]
      · simp only [key, micro, encode, x, y, Nat.unpair_pair]
        rw [truncatedSixthMassPackingTheta, mul_sum]
        rfl
      · intro u _ v _ huv
        have heq := congrArg (fun n => Nat.unpair (Nat.unpair n).2) huv
        simpa only [encode, Nat.unpair_pair] using heq
    · intro k _ l _ hkl
      apply Finset.disjoint_left.mpr
      intro n hn hm
      obtain ⟨j, _, hj⟩ := mem_image.mp hn
      obtain ⟨i, _, hi⟩ := mem_image.mp hm
      apply hkl
      have heq := congrArg (fun n => (Nat.unpair n).1) (hj.trans hi.symm)
      simpa only [encode, Nat.unpair_pair] using heq
  rw [hsum] at hcount
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hcount

end Wu2008DoubleSieve
