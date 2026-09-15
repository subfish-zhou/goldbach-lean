import HighConsumerBox

namespace HighConsumer
open Finset Real Wu2008DoubleSieve HighTheta HighBoxRecovery
open scoped Classical
noncomputable section

/-- The physical box inclusion uses only the retained polygon, not a square ceiling. -/
theorem retained_box_subset {N : ℕ} {δ Δ x y : ℝ}
    (hN : 1 < N) (hr : truncatedSixthLowerRegion δ x y)
    (hp : (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^x/Δ)
    (hq : (N : ℝ)^truncatedSixthLowerBeta ≤ (N : ℝ)^y/Δ) :
    truncatedSixthLowerBoxPairs N Δ x y ⊆ truncatedSixthLowerPairs N δ := by
  intro b hb
  obtain ⟨hp',hq'⟩ := mem_product.mp hb
  have hpv := mem_primeWindow.mp hp'
  have hqv := mem_primeWindow.mp hq'
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hN0 : (0 : ℝ) < N := by linarith
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨?_,?_⟩,?_⟩
  · exact mem_primeWindow.mpr ⟨hpv.1,hpv.2.1,hp.trans hpv.2.2.1,
      hpv.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hr.2.1)⟩
  · exact mem_primeWindow.mpr ⟨hqv.1,hqv.2.1,hq.trans hqv.2.2.1,
      hqv.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hr.2.2.2.1)⟩
  · calc
      (b.1 : ℝ)*b.2 ≤ (N : ℝ)^x*(N : ℝ)^y :=
        mul_le_mul hpv.2.2.2.le hqv.2.2.2.le (Nat.cast_nonneg _) (rpow_nonneg hN0.le _)
      _ = (N : ℝ)^(x+y) := (rpow_add hN0 x y).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hNR hr.2.2.2.2

/-- Low boxes and genuinely high boxes have disjoint physical prime pairs. -/
theorem low_high_disjoint {N : ℕ} {δ Δ x y X Y : ℝ}
    (hN : 1 < N) (hδ : 0 ≤ δ)
    (hl : truncatedSixthLowerAdmissibleRegion δ x y)
    (hh : (N : ℝ)^(1/4 : ℝ) ≤ (N : ℝ)^Y/Δ) :
    Disjoint (truncatedSixthLowerBoxPairs N Δ x y)
      (truncatedSixthLowerBoxPairs N Δ X Y) := by
  apply disjoint_left.mpr
  intro b hb hc
  have hlow := (mem_primeWindow.mp (mem_product.mp hb).2).2.2.2
  have hhigh := hh.trans (mem_primeWindow.mp (mem_product.mp hc).2).2.2.1
  have hy : y ≤ (1:ℝ)/4 := by
    have := hl.2
    unfold truncatedSixthLowerC at this
    linarith
  have hpow := rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le : (1 : ℝ) ≤ N) hy
  exact (not_lt_of_ge hhigh) (hlow.trans_le hpow)

/-- Actual finite mixed packing. The classical complement excludes every
selected box BEFORE any lower bounds are added. The old low producer and its
full a+h coefficient are retained, while the new high boxes use paid closed Phi.
Only geometric packing data, never a total-count lower bound, are inputs. -/
theorem mixed_packing_actual {δ η ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 50*highEta) (hd : δ < 1/100) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε)
    (G : Finset ℝ) (hG : ∀ s ∈ G, 2 ≤ s ∧ s ≤ 5) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ (I J : Finset ℕ) (x y s X Y t : ℕ → ℝ),
      (∀ i ∈ I, truncatedSixthLowerAdmissibleRegion δ (x i) (y i)) →
      (∀ i ∈ I, (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^(x i)/Δ) →
      (∀ i ∈ I, (N : ℝ)^truncatedSixthLowerBeta ≤ (N : ℝ)^(y i)/Δ) →
      (∀ i ∈ I, s i ∈ G ∧ s i ≤ truncatedSixthLowerS δ (x i) (y i)) →
      (Set.PairwiseDisjoint (I : Set ℕ) (fun i => truncatedSixthLowerBoxPairs N Δ (x i) (y i))) →
      (∀ j ∈ J, truncatedSixthLowerRegion δ (X j) (Y j) ∧ 1/4 < Y j) →
      (∀ j ∈ J, (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^(X j)/Δ) →
      (∀ j ∈ J, (N : ℝ)^(1/4 : ℝ) ≤ (N : ℝ)^(Y j)/Δ) →
      (∀ j ∈ J, 2 ≤ t j ∧ t j ≤ 29/10 ∧ t j ≤ truncatedSixthLowerS δ (X j) (Y j)) →
      (Set.PairwiseDisjoint (J : Set ℕ) (fun j => truncatedSixthLowerBoxPairs N Δ (X j) (Y j))) →
      let L := I.biUnion (fun i => truncatedSixthLowerBoxPairs N Δ (x i) (y i))
      let H := J.biUnion (fun j => truncatedSixthLowerBoxPairs N Δ (X j) (Y j))
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerPairs N δ \ (L ∪ H)) +
        (∑ i ∈ I, (wuLowerCoefficient (s i)+wuImprovementLimit false δ (s i)-η)*
          boxTheta N ((N : ℝ)^(1/2-δ))
            (convolutionWuWindows N Δ ![(N : ℝ)^(y i),(N : ℝ)^(x i)])) +
        (∑ j ∈ J, (log (t j-1)+(1/10000)*log (2/(t j-1))-η)*
          boxTheta N ((N : ℝ)^(1/2-δ))
            (convolutionWuWindows N Δ ![(N : ℝ)^(X j),(N : ℝ)^(Y j)])) -
        ε*wuSingularSeries N*N/log N^(2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ)^truncatedSixthLowerAlpha)
        ((N : ℝ)^truncatedSixthLowerBeta) ((N : ℝ)^truncatedSixthLowerSigma)
        ((N : ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨Tc,_,hc⟩ := truncatedSixthLower_normalized_masked_relative hδ hη hηhi hε
  obtain ⟨Tl,_,hl⟩ := truncatedSixthLower_finite_grid_gain hδ hd hη G hG
  obtain ⟨Th,_,hh⟩ := high_box_count hδ hδhi hη
  refine ⟨max 512 (max Tc (max Tl Th)),le_max_left _ _,?_⟩
  intro N hN he Δ hlo hhi I J x y s X Y t hlow hp hq hs hld hhigh hP hQ ht hhd L H
  have hN1 : 1 < N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1.le
  let F := fun b : ℕ × ℕ => (sieveCount N (b.1*b.2) N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)
  have hQb : ∀ j ∈ J, (N : ℝ)^truncatedSixthLowerBeta ≤ (N : ℝ)^(Y j)/Δ := by
    intro j hj
    exact (rpow_le_rpow_of_exponent_le hNR (by norm_num [truncatedSixthLowerBeta])).trans (hQ j hj)
  have hLa : L ⊆ truncatedSixthLowerPairs N δ := by
    intro b hb
    obtain ⟨i,hi,hb⟩ := mem_biUnion.mp hb
    exact retained_box_subset hN1 (hlow i hi).1 (hp i hi) (hq i hi) hb
  have hHa : H ⊆ truncatedSixthLowerPairs N δ := by
    intro b hb
    obtain ⟨j,hj,hb⟩ := mem_biUnion.mp hb
    exact retained_box_subset hN1 (hhigh j hj).1 (hP j hj) (hQb j hj) hb
  have hLH : Disjoint L H := by
    apply disjoint_left.mpr
    intro b hb hb'
    obtain ⟨i,hi,hb⟩ := mem_biUnion.mp hb
    obtain ⟨j,hj,hb'⟩ := mem_biUnion.mp hb'
    exact disjoint_left.mp (low_high_disjoint hN1 hδ.le (hlow i hi) (hQ j hj)) hb hb'
  have hcl := hc N (by omega) he (truncatedSixthLowerPairs N δ \ (L ∪ H)) sdiff_subset
  have hls : (∑ i ∈ I, (wuLowerCoefficient (s i)+wuImprovementLimit false δ (s i)-η)*
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ ![(N : ℝ)^(y i),(N : ℝ)^(x i)])) ≤ ∑ b ∈ L, F b := by
    dsimp [L]
    rw [sum_biUnion hld]
    apply sum_le_sum
    intro i hi
    have hqa := (rpow_le_rpow_of_exponent_le hNR truncatedSixthLower_parameters.2.1.le).trans (hq i hi)
    have hv := hl N (by omega) he Δ (x i) (y i) hlo hhi (hlow i hi) (hp i hi) hqa (s i) (hs i hi).1 (hs i hi).2
    have heq : (∑ b ∈ truncatedSixthLowerBoxPairs N Δ (x i) (y i), F b) =
        ∑ b ∈ primeWindow N ((N : ℝ)^(y i)/Δ) ((N : ℝ)^(y i)) ×ˢ
          primeWindow N ((N : ℝ)^(x i)/Δ) ((N : ℝ)^(x i)),
          (sieveCount N (b.1*b.2) N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
      dsimp [truncatedSixthLowerBoxPairs,F]
      rw [sum_product,sum_product,sum_comm]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro q _
      rw [mul_comm p q]
    rw [heq]
    exact hv
  have hhs : (∑ j ∈ J, (log (t j-1)+(1/10000)*log (2/(t j-1))-η)*
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ ![(N : ℝ)^(X j),(N : ℝ)^(Y j)])) ≤ ∑ b ∈ H, F b := by
    dsimp [H]
    rw [sum_biUnion hhd]
    apply sum_le_sum
    intro j hj
    have hqa := (rpow_le_rpow_of_exponent_le hNR truncatedSixthLower_parameters.2.1.le).trans (hQb j hj)
    exact hh N (by omega) he Δ (X j) (Y j) hlo hhi (hhigh j hj).1 (hhigh j hj).2
      (hP j hj) hqa (t j) (ht j hj).1 (ht j hj).2.1 (ht j hj).2.2
  have htotal := truncatedSixthLower_mask_mass_le hN1 hδ (truncatedSixthLowerPairs N δ) Subset.rfl
  have heq : (∑ b ∈ truncatedSixthLowerPairs N δ, F b) =
      (∑ b ∈ truncatedSixthLowerPairs N δ \ (L ∪ H), F b) +
      (∑ b ∈ L, F b) + (∑ b ∈ H, F b) := by
    rw [add_assoc, ← sum_union hLH, ← sum_union sdiff_disjoint,
      sdiff_union_of_subset (union_subset hLa hHa)]
  change (∑ b ∈ truncatedSixthLowerPairs N δ, F b) ≤ _ at htotal
  rw [heq] at htotal
  change _ ≤ ∑ b ∈ truncatedSixthLowerPairs N δ \ (L ∪ H), F b at hcl
  linarith only [hcl,hls,hhs,htotal]

end
end HighConsumer
