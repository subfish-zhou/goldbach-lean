import MathlibNt.Wu2004MeanValue.SelectedCell
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHighAggregate

/-!
# The complete high-conductor selected-prefix source producer

Every character keeps its chosen prefix throughout the exact source dyadic
partition. Triangle inequalities separate only complete source blocks, not
individual coefficients. Prefix zero is included.
-/

noncomputable section
open Classical Complex Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def selectedHighSource (f : ℕ → ℂ) (m x A₁ A₂ : ℕ) (B : ℝ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ) : ℝ :=
  ∑ q ∈ Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊,
    (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
      ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ) A₁ A₂ χ‖

/-- Exact active conductor coverage and complete source-block partition,
with each selected prefix unchanged by both finite summations. -/
theorem selectedHighSource_le_sum_active_cells
    (f : ℕ → ℂ) (m x A₁ A₂ : ℕ) (B : ℝ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) (hA₁ : 0 < A₁) :
    selectedHighSource f m x A₁ A₂ B y ≤
      ∑ j ∈ (range (Nat.log 2 x + 1)).filter
          (fun j => conductorRadius x B j ≤ upperConductor x B),
        ∑ k ∈ range (panDyadicDepth A₁ A₂),
          selectedSourceCell f m A₁ A₂ k y (conductorRadius x B j) := by
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x B j ≤ upperConductor x B)
  let w := fun q : ℕ => (q.totient : ℝ)⁻¹ *
    ∑ χ : PrimitiveCharacter q,
      ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ) A₁ A₂ χ‖
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
                ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ)
                  (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ := by
          apply sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum
          intro χ hχ
          rw [panSourceCharacterAmplitude_eq_sum_dyadicCells
            (panSourceG f m) (panSourceD m) (y q χ) A₁ A₂ hA₁ χ]
          convert norm_sum_le _ _ using 1 <;>
            first | rfl | simp [pow_succ, mul_comm, mul_left_comm]
        _ = ∑ k ∈ range (panDyadicDepth A₁ A₂),
            selectedSourceCell f m A₁ A₂ k y (conductorRadius x B j) := by
          unfold selectedSourceCell
          simp_rw [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro q hq
          rw [sum_comm]

private theorem chosen_selected_high_depth_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ)
        (y : (q : ℕ) → PrimitiveCharacter q → ℕ),
      (∀ q χ, 1 ≤ y q χ ∧ y q χ ≤ x) →
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      selectedHighSource f m x A₁ A₂ B y ≤
        (Nat.log 2 x + 1 : ℝ) ^ 2 *
          (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
  obtain ⟨C, hC, hcell⟩ := chosen_source_selected_cell_log_saving
  refine ⟨C, hC, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hcell B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f y hy hAx hApower hAlow hf
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
        selectedSourceCell f m A₁ A₂ k y (conductorRadius x B j) :=
      selectedHighSource_le_sum_active_cells f m x A₁ A₂ B y hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact hX₁ x ((le_max_left X₁ X₂).trans hx) j m A₁ A₂ k f y hy hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]

private theorem selectedHighSource_le_positive (f : ℕ → ℂ) (m x A₁ A₂ : ℕ) (B : ℝ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ) :
    selectedHighSource f m x A₁ A₂ B y ≤
      selectedHighSource f m x A₁ A₂ B (fun q χ => max 1 (y q χ)) := by
  apply sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro χ hχ
  by_cases hy : y q χ = 0
  · simp [hy, panSourceCharacterAmplitude]
  · simpa only [max_eq_right (by omega : 1 ≤ y q χ)] using
      (le_refl ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m)
        (y q χ) A₁ A₂ χ‖)

/-- The complete high-conductor W1 source component, uniform in the cofactor,
bounded complex coefficients and independently selected natural prefixes.
The sum is over `log(x)^B < q ≤ sqrt(x)/log(x)^B`; prefix zero is allowed.
This is not the low-conductor, induced-character, or Wu-weight assembly. -/
theorem chosen_high_source_selected_prefix_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ)
        (y : (q : ℕ) → PrimitiveCharacter q → ℕ),
      (∀ q χ, y q χ ≤ x) →
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      selectedHighSource f m x A₁ A₂ B y ≤
        C * (x : ℝ) * Real.log x ^ (6 - B) +
          6984 * (Real.log x) ^ 2 / (x : ℝ) := by
  obtain ⟨C, hC, hdepth⟩ := chosen_selected_high_depth_saving
  refine ⟨9 * C, by positivity, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hdepth B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f y hy hAx hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hxpos : 1 ≤ x := source_pos_of_log (by linarith)
  have hy' : ∀ q χ, 1 ≤ max 1 (y q χ) ∧ max 1 (y q χ) ≤ x :=
    fun q χ => ⟨le_max_left _ _, max_le hxpos (hy q χ)⟩
  calc
    _ ≤ selectedHighSource f m x A₁ A₂ B (fun q χ => max 1 (y q χ)) :=
      selectedHighSource_le_positive f m x A₁ A₂ B y
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) :=
      hX₁ x ((le_max_left X₁ X₂).trans hx) m A₁ A₂ f
        (fun q χ => max 1 (y q χ)) hy' hAx hApower hAlow hf
    _ ≤ (3 * Real.log x) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - B : ℝ) = 2 + (4 - B) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      ring

end Wu2004MeanValue
