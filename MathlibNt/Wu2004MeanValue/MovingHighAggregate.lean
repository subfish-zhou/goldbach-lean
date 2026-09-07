import MathlibNt.Wu2004MeanValue.MovingCell
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHighAggregate

/-!
# High primitive conductors with one common moving profile

The entire source sum is inside the norm. The cutoff may vary arbitrarily
with its source coordinate, but is the same for every modulus and character.
-/

noncomputable section
open Classical Complex Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def movingHighSource (f : ℕ → ℂ) (v : ℕ → ℕ) (m x A₁ A₂ : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊,
    (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
      ‖movingAmplitude (panSourceG f m) (panSourceD m) v A₁ A₂ χ‖

/-- The moving cutoff remains unchanged throughout the exact dyadic partition. -/
theorem movingAmplitude_eq_sum_dyadicCells {q : ℕ} (A D : ℕ → ℂ)
    (v : ℕ → ℕ) (A₁ A₂ : ℕ) (hA₁ : 0 < A₁) (χ : PrimitiveCharacter q) :
    movingAmplitude A D v A₁ A₂ χ =
      ∑ k ∈ range (panDyadicDepth A₁ A₂),
        movingAmplitude A D v (A₁ * 2 ^ k) (min (2 * (A₁ * 2 ^ k)) A₂) χ := by
  unfold movingAmplitude
  rw [← panDyadicCells_cover A₁ A₂ hA₁,
    sum_biUnion (panDyadicCells_pairwise A₁ A₂ hA₁)]
  simp only [panDyadicCell]

theorem movingHighSource_le_sum_active_cells
    (f : ℕ → ℂ) (v : ℕ → ℕ) (m x A₁ A₂ : ℕ) (B : ℝ)
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) (hA₁ : 0 < A₁) :
    movingHighSource f v m x A₁ A₂ B ≤
      ∑ j ∈ (range (Nat.log 2 x + 1)).filter
          (fun j => conductorRadius x B j ≤ upperConductor x B),
        ∑ k ∈ range (panDyadicDepth A₁ A₂),
          movingSourceCell f v m A₁ A₂ k (conductorRadius x B j) := by
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x B j ≤ upperConductor x B)
  let w := fun q : ℕ => (q.totient : ℝ)⁻¹ *
    ∑ χ : PrimitiveCharacter q,
      ‖movingAmplitude (panSourceG f m) (panSourceD m) v A₁ A₂ χ‖
  have hw (q : ℕ) : 0 ≤ w q := by dsimp [w]; positivity
  have hcover : Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊ ⊆
      s.biUnion (fun j => conductorCell (conductorRadius x B j)) := by
    intro q hq
    obtain ⟨j, hj, hact, hcell⟩ := mem_active_conductorCell hx hB hq
    exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨hj, hact⟩, hcell⟩
  calc
    _ ≤ ∑ q ∈ s.biUnion (fun j => conductorCell (conductorRadius x B j)), w q :=
      sum_le_sum_of_subset_of_nonneg hcover (by intro q _ _; exact hw q)
    _ ≤ ∑ j ∈ s, ∑ q ∈ conductorCell (conductorRadius x B j), w q :=
      sum_biUnion_le_sum_sum_nonneg s _ w hw
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ q ∈ conductorCell (conductorRadius x B j), (q.totient : ℝ)⁻¹ *
            ∑ χ : PrimitiveCharacter q,
              ∑ k ∈ range (panDyadicDepth A₁ A₂),
                ‖movingAmplitude (panSourceG f m) (panSourceD m) v
                  (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ := by
          apply sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum
          intro χ hχ
          rw [movingAmplitude_eq_sum_dyadicCells
            (panSourceG f m) (panSourceD m) v A₁ A₂ hA₁ χ]
          convert norm_sum_le _ _ using 1 <;>
            first | rfl | simp [pow_succ, mul_comm, mul_left_comm]
        _ = ∑ k ∈ range (panDyadicDepth A₁ A₂),
            movingSourceCell f v m A₁ A₂ k (conductorRadius x B j) := by
          unfold movingSourceCell
          simp_rw [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro q hq
          rw [sum_comm]

private theorem chosen_moving_high_depth_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (v : ℕ → ℕ),
      (∀ a, 1 ≤ v a ∧ v a ≤ x) →
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      movingHighSource f v m x A₁ A₂ B ≤
        (Nat.log 2 x + 1 : ℝ) ^ 2 *
          (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
  obtain ⟨C, hC, hcell⟩ := chosen_source_moving_cell_log_saving
  refine ⟨C, hC, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hcell B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f v hv hAx hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hA₁ : 0 < A₁ := by
    have hp : (0 : ℝ) < Real.log x ^ (2 * B) :=
      Real.rpow_pos_of_pos (by linarith) _
    have : (0 : ℝ) < A₁ := hp.trans_le hAlow
    exact_mod_cast this
  let M := C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)
  have hM : 0 ≤ M := by
    dsimp [M]
    have : 0 ≤ Real.log (x : ℝ) := by linarith
    positivity
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x B j ≤ upperConductor x B)
  have hs : s.card ≤ Nat.log 2 x + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  calc
    _ ≤ ∑ j ∈ s, ∑ k ∈ range (panDyadicDepth A₁ A₂),
        movingSourceCell f v m A₁ A₂ k (conductorRadius x B j) :=
      movingHighSource_le_sum_active_cells f v m x A₁ A₂ B hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact hX₁ x ((le_max_left X₁ X₂).trans hx) j m A₁ A₂ k f v hv hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]

/-- A complete high-conductor producer for an arbitrary COMMON moving
profile. Only values on the source interval are constrained; zero cutoffs
are allowed. This does not allow a profile selected separately by modulus. -/
theorem chosen_high_source_common_moving_profile_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ) (v : ℕ → ℕ),
      (∀ a ∈ Ioc A₁ A₂, v a ≤ x) →
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      movingHighSource f v m x A₁ A₂ B ≤
        C * (x : ℝ) * Real.log x ^ (6 - B) +
          6984 * (Real.log x) ^ 2 / (x : ℝ) := by
  obtain ⟨C, hC, hdepth⟩ := chosen_moving_high_depth_saving
  refine ⟨9 * C, by positivity, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hdepth B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f v hv hAx hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hxpos : 1 ≤ x := source_pos_of_log (by linarith)
  let f' : ℕ → ℂ := fun a => if v a = 0 then 0 else f a
  let v' : ℕ → ℕ := fun a => if a ∈ Ioc A₁ A₂ then max 1 (v a) else 1
  have hf' : ∀ a, ‖f' a‖ ≤ 1 := by
    intro a
    dsimp [f']
    split_ifs <;> simp [hf]
  have hv' : ∀ a, 1 ≤ v' a ∧ v' a ≤ x := by
    intro a
    dsimp [v']
    split_ifs with ha
    · exact ⟨le_max_left _ _, max_le hxpos (hv a ha)⟩
    · exact ⟨le_rfl, hxpos⟩
  have heq : movingHighSource f v m x A₁ A₂ B = movingHighSource f' v' m x A₁ A₂ B := by
    unfold movingHighSource
    apply sum_congr rfl
    intro q hq
    congr 1
    apply sum_congr rfl
    intro χ hχ
    congr 1
    unfold movingAmplitude
    apply sum_congr rfl
    intro a ha
    by_cases hz : v a = 0
    · simp [f', hz, panSourceG]
    · have hpos : 1 ≤ v a := by omega
      have hva : v' a = v a := by simp only [v', if_pos ha, max_eq_right hpos]
      rw [hva]
      simp only [panSourceG, f', if_neg hz]
  rw [heq]
  calc
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) :=
      hX₁ x ((le_max_left X₁ X₂).trans hx) m A₁ A₂ f' v' hv' hAx hApower hAlow hf'
    _ ≤ (3 * Real.log x) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - B : ℝ) = 2 + (4 - B) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      ring

end Wu2004MeanValue