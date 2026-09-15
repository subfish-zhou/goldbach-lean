import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticBox
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryRectangleCoordinates

/-!
# Actual arithmetic prefixes after five-variable partial summation

The original finite fiber remains inside every prefix, including its coupled
frequency cutoff and arithmetic masks. Only the concrete smooth factor is
differenced; no assertion that a prefix is an arithmetic progression is made.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open _root_.LiLiuPrereqFouvry

def wAnalyticBoxLo (j : Fin 5 → ℕ) : Fin 5 → ℕ := fun i => 2 ^ j i
def wAnalyticBoxHi (j : Fin 5 → ℕ) : Fin 5 → ℕ := fun i => 2 * 2 ^ j i

def wAnalyticGridWeight (K : WExtractedKey) (j : Fin 5 → ℕ)
    (positive : Bool) (a : ℤ) (u : ℝ) (v : Fin 5 → ℕ) : ℂ :=
  SlowFactor.normalizedWeight (wBlockPhaseA K j positive u)
    (wBlockPhaseB K j positive a) (fun i => (v i : ℝ) / (2 : ℝ) ^ j i)

def wAnalyticBlockPrefixMax (B : Finset (WExtractedTuple × ℤ)) (j : Fin 5 → ℕ)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  Rectangle.coordinatePrefixMax (wAnalyticBoxLo j) (wAnalyticBoxHi j) B
    wAnalyticCoordinates
    (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1)

theorem wAnalyticBlockPrefixMax_nonneg (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    0 ≤ wAnalyticBlockPrefixMax B j β c₁ γ ζ a :=
  Rectangle.coordinatePrefixMax_nonneg _ _ _ _ _

theorem wAnalyticPrefixSum_eq_coordinatePrefix
    (B : Finset (WExtractedTuple × ℤ)) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (cap : Fin 5 → ℕ) :
    wAnalyticPrefixSum B β c₁ γ ζ a cap =
      Rectangle.coordinatePrefix B wAnalyticCoordinates
        (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
          wExtractedArithmeticPhase a t.2 t.1) cap := by
  unfold wAnalyticPrefixSum wAnalyticPrefix Rectangle.coordinatePrefix
  apply sum_congr
  · ext t
    simp only [mem_filter]
  · intro t _
    rfl

theorem wAnalyticPrefixSum_norm_le_max (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (cap : Fin 5 → ℕ)
    (hcap : cap ∈ Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j)) :
    ‖wAnalyticPrefixSum B β c₁ γ ζ a cap‖ ≤
      wAnalyticBlockPrefixMax B j β c₁ γ ζ a := by
  rw [wAnalyticPrefixSum_eq_coordinatePrefix]
  exact Rectangle.coordinatePrefix_norm_le_max (wAnalyticBoxLo j) (wAnalyticBoxHi j)
    B wAnalyticCoordinates
    (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1) cap hcap

/-- The finite maximum is attained by an actual arithmetic rectangular
prefix, even when the underlying block is empty. -/
theorem wAnalyticBlockPrefixMax_attained (B : Finset (WExtractedTuple × ℤ))
    (j : Fin 5 → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    ∃ cap ∈ Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j),
      wAnalyticBlockPrefixMax B j β c₁ γ ζ a =
        ‖wAnalyticPrefixSum B β c₁ γ ζ a cap‖ := by
  let f := fun cap => ‖Rectangle.coordinatePrefix B wAnalyticCoordinates
    (fun t => (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1) cap‖₊
  have hn : (Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j)).Nonempty := by
    refine ⟨wAnalyticBoxLo j, (Rectangle.mem_box _ _ _).mpr (fun i => ⟨le_rfl, ?_⟩)⟩
    dsimp [wAnalyticBoxLo, wAnalyticBoxHi]
    omega
  obtain ⟨cap, hcap, hmax⟩ := exists_max_image
    (Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j)) f hn
  have he : (Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j)).sup f = f cap :=
    le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := f) hcap)
  refine ⟨cap, hcap, ?_⟩
  rw [wAnalyticPrefixSum_eq_coordinatePrefix]
  change (((Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j)).sup f : NNReal) : ℝ) =
    (f cap : ℝ)
  exact congrArg (fun z : NNReal => (z : ℝ)) he

def wAnalyticDyadicWeightedBlock (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (j : Fin 5 → ℕ) (positive : Bool)
    (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (u : ℝ) : ℂ :=
  ∑ t ∈ wAnalyticDyadicBlock U j positive,
    let v := wGCDTuple (wExtractedOriginal t.1)
    (wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
      wExtractedArithmeticPhase a t.2 t.1 *
      wAnalyticWeight K.D K.D' a u t.2 v.k₁ v.n₁ t.1.1.2.1 t.1.1.2.2

theorem wAnalyticDyadicWeightedBlock_eq_normalized
    (U : Finset (WExtractedTuple × ℤ)) (K : WExtractedKey)
    (j : Fin 5 → ℕ) (positive : Bool) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) (u : ℝ) :
    wAnalyticDyadicWeightedBlock U K j positive β c₁ γ ζ a u =
      (wBlockAmplitude K j : ℂ) *
        ∑ t ∈ wAnalyticDyadicBlock U j positive,
          wAnalyticGridWeight K j positive a u (wAnalyticCoordinates t) *
            ((wExtractedCoefficient β c₁ γ ζ t.1 : ℂ) *
              wExtractedArithmeticPhase a t.2 t.1) := by
  unfold wAnalyticDyadicWeightedBlock
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [wAnalyticWeight_eq_normalized_block ht]
  change _ = (wBlockAmplitude K j : ℂ) *
    (SlowFactor.normalizedWeight _ _ (wAnalyticUnitCoordinates j t) * _)
  ring

theorem wExtractedKeyExponential_eq_dyadicWeightedBlocks
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (H : ℕ → ℕ → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey) (u : ℝ) :
    let U := wExtractedKeyFiber H N Q a P R S ξ b K
    wExtractedKeyExponential H N Q β c₁ γ ζ a P R S ξ b K u =
      ∑ j ∈ U.image wAnalyticDyadicKey,
        (wAnalyticDyadicWeightedBlock U K j true β c₁ γ ζ a u +
          wAnalyticDyadicWeightedBlock U K j false β c₁ γ ζ a u) := by
  rw [wExtractedKeyExponential_eq_fixedWeight hN hQ]
  exact sum_wAnalyticDyadicBlocks _ _

theorem wAnalyticDyadicBlock_coordinates_mem
    {H : ℕ → ℕ → ℕ} {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock (wExtractedKeyFiber H N Q a P R S ξ b K)
      j positive) :
    wAnalyticCoordinates t ∈ Rectangle.box (wAnalyticBoxLo j) (wAnalyticBoxHi j) := by
  apply (Rectangle.mem_box _ _ _).mpr
  intro i
  have hb := wAnalyticDyadicBlock_bounds hN hQ ht i
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2.le

theorem wAnalyticDyadicWeightedBlock_norm_le_variation
    {N Q : Finset ℕ} (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    (H : ℕ → ℕ → ℕ) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ)
    (P : WOriginalTuple → Prop) (R S ξ : ℝ) (b : ℕ) (K : WExtractedKey)
    (j : Fin 5 → ℕ) (positive : Bool) (u : ℝ) :
    let U := wExtractedKeyFiber H N Q a P R S ξ b K
    ‖wAnalyticDyadicWeightedBlock U K j positive β c₁ γ ζ a u‖ ≤
      wBlockAmplitude K j *
        Rectangle.variation (wAnalyticBoxLo j) (wAnalyticBoxHi j)
          (wAnalyticGridWeight K j positive a u) *
        wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j positive) j β c₁ γ ζ a := by
  dsimp only
  rw [wAnalyticDyadicWeightedBlock_eq_normalized, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by unfold wBlockAmplitude; positivity)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by unfold wBlockAmplitude; positivity)
  exact Rectangle.norm_coordinate_sum_le_variation_mul_max _ _ _ _ _ _
    (fun _ ht => wAnalyticDyadicBlock_coordinates_mem hN hQ ht)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
