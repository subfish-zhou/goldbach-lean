import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryKBlockPhase
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPartialSummation
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open _root_.LiLiuPrereqFouvry
theorem wAnalyticGridWeight_variation_bound_kscale
    {Cscale M T x Z y : ℝ} (hCscale : 1 ≤ Cscale) (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale*x)
    {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ} {K : WExtractedKey}
    {j : Fin 5 → ℕ} {positive : Bool} {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive) :
    Rectangle.variation (wAnalyticBoxLo j) (wAnalyticBoxHi j)
      (wAnalyticGridWeight K j positive a (M * y)) ≤ wAnalyticVariationConstant (Cscale*Z) := by
  exact Rectangle.variation_normalizedWeight_div_le_all _ _ _
    (wAnalyticDyadicBlock_parameter_budget_kscale hCscale hM hT hZ hx hy hN hQ ha ht)
    (wAnalyticBoxLo j) (wAnalyticBoxHi j) (fun i => (2 : ℝ) ^ j i)
    (fun _ => by positivity)
    (fun i => by simp [wAnalyticBoxLo])
    (fun i => by simp [wAnalyticBoxHi])

theorem wAnalyticDyadicWeightedBlock_norm_le_prefix_kscale
    {Cscale M T x Z y : ℝ} (hCscale : 1 ≤ Cscale) (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale*x)
    (β c₁ γ ζ : ℕ → ℝ) (P : WOriginalTuple → Prop) (R S ξ : ℝ)
    (b : ℕ) (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool) :
    let U := wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K
    ‖wAnalyticDyadicWeightedBlock U K j positive β c₁ γ ζ a (M * y)‖ ≤
      wBlockAmplitude K j * wAnalyticVariationConstant (Cscale*Z) *
        wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive) j β c₁ γ ζ a := by
  dsimp only
  have hNp : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (lt_of_lt_of_le hT (hN n hn))
  have hA : 0 ≤ wBlockAmplitude K j := by unfold wBlockAmplitude; positivity
  have hC := wAnalyticVariationConstant_nonneg (mul_nonneg (by linarith : 0 ≤ Cscale) hZ)
  have hP := wAnalyticBlockPrefixMax_nonneg
    (wAnalyticDyadicBlock (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K)
      j positive) j β c₁ γ ζ a
  by_cases hn : (wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive).Nonempty
  · obtain ⟨t, ht⟩ := hn
    have hv := wAnalyticGridWeight_variation_bound_kscale hCscale hM hT hZ hx hy hN hQ ha ht
    exact (wAnalyticDyadicWeightedBlock_norm_le_variation hNp hQ
      (wFloorCutoff M Z) β c₁ γ ζ a P R S ξ b K j positive (M * y)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hA) hP)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [wAnalyticDyadicWeightedBlock, he, sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg hA hC)
      (wAnalyticBlockPrefixMax_nonneg ∅ j β c₁ γ ζ a)

theorem wExtractedFloorKeyExponential_norm_le_prefixes_kscale
    {Cscale M T x Z y : ℝ} (hCscale : 1 ≤ Cscale) (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hy : y ∈ Set.Icc (1 / 2 : ℝ) 3)
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, T ≤ (n : ℝ))
    (hQ : ∀ q ∈ Q, 0 < q) {a : ℤ} (ha : |(a : ℝ)| ≤ Cscale*x)
    (β c₁ γ ζ : ℕ → ℝ) (P : WOriginalTuple → Prop) (R S ξ : ℝ)
    (b : ℕ) (K : WExtractedKey) :
    ‖wExtractedKeyExponential (wFloorCutoff M Z) N Q β c₁ γ ζ a P R S ξ b K
      (M * y)‖ ≤
      wAnalyticVariationConstant (Cscale*Z) *
        wAnalyticKeyPrefixMajorant
          (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K)
          K β c₁ γ ζ a := by
  have hNp : ∀ n ∈ N, 0 < n := fun n hn =>
    Nat.cast_pos.mp (lt_of_lt_of_le hT (hN n hn))
  rw [wExtractedKeyExponential_eq_dyadicWeightedBlocks hNp hQ]
  unfold wAnalyticKeyPrefixMajorant
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j _
  apply (norm_add_le _ _).trans
  have hp := wAnalyticDyadicWeightedBlock_norm_le_prefix_kscale hCscale hM hT hZ hx hy hN hQ ha
    β c₁ γ ζ P R S ξ b K j true
  have hn := wAnalyticDyadicWeightedBlock_norm_le_prefix_kscale hCscale hM hT hZ hx hy hN hQ ha
    β c₁ γ ζ P R S ξ b K j false
  exact (add_le_add hp hn).trans (by ring_nf; rfl)


/-- A fixed enlargement of the residue only adds a fixed fifth-power variation cost. -/
theorem wAnalyticVariationConstant_kscale {Cscale Z : ℝ}
    (hC : 1 ≤ Cscale) (hZ : 0 ≤ Z) :
    wAnalyticVariationConstant (Cscale*Z) ≤ Cscale^5*wAnalyticVariationConstant Z := by
  unfold wAnalyticVariationConstant
  have hb : 1+112*(Cscale*Z) ≤ Cscale*(1+112*Z) := by nlinarith
  calc
    _ ≤ 2048*(6+2*Real.pi)^5*(Cscale*(1+112*Z))^5 := by gcongr
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
