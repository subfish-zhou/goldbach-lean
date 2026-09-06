import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPerronAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingTheoremADyadicCoverage

/-!
# The full high-conductor Pan source sum

The outer interval is open on the left and closed on the right. It is a
nonnegative majorant, not an identification, of a strictly truncated outer
modulus carrier. Conductor cells use the exact real radii; only complete
dyadic source blocks are separated by a triangle inequality.
-/

noncomputable section
open Classical Complex Finset Filter
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

/-- Every high conductor belongs to an active cell with the exact real radius. -/
theorem mem_active_conductorCell {x q : ℕ} {B : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hq : q ∈ Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊) :
    ∃ j ∈ range (Nat.log 2 x + 1),
      conductorRadius x B j ≤ upperConductor x B ∧
        q ∈ conductorCell (conductorRadius x B j) := by
  have hL := lowConductor_ge_one hx hB
  have hL0 : 0 ≤ lowConductor x B := zero_le_one.trans hL
  have hD0 : 0 ≤ upperConductor x B := by
    unfold upperConductor
    positivity
  obtain ⟨hql, hqu⟩ := mem_Ioc.mp hq
  have hql' : lowConductor x B < q := (Nat.floor_lt hL0).mp hql
  have hqu' : (q : ℝ) ≤ upperConductor x B := (Nat.le_floor_iff hD0).mp hqu
  have hxpos : 0 < x := source_pos_of_log hx
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hsqrt : Real.sqrt (x : ℝ) ≤ x := by
    exact (Real.sqrt_le_iff).2 ⟨Nat.cast_nonneg x, by nlinarith only [hxone]⟩
  have hqx : (q : ℝ) ≤ x :=
    hqu'.trans ((upperConductor_le_sqrt hx hB).trans hsqrt)
  have hlast : (q : ℝ) ≤ 2 ^ (Nat.log 2 x + 1) * lowConductor x B := by
    have hp : (x : ℝ) < 2 ^ (Nat.log 2 x + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) x
    exact hqx.trans (hp.le.trans
      (le_mul_of_one_le_right (by positivity) hL))
  have hex : ∃ j : ℕ, (q : ℝ) ≤ 2 ^ (j + 1) * lowConductor x B :=
    ⟨Nat.log 2 x, hlast⟩
  let j := Nat.find hex
  have hj : j ≤ Nat.log 2 x := Nat.find_min' hex hlast
  have hu : (q : ℝ) ≤ 2 * conductorRadius x B j := by
    simpa [j, conductorRadius, pow_succ, mul_assoc, mul_comm, mul_left_comm]
      using Nat.find_spec hex
  have hl : conductorRadius x B j < q := by
    cases hj0 : j with
    | zero => simpa [conductorRadius, hj0] using hql'
    | succ i =>
      have hi : i < Nat.find hex := by change i < j; omega
      have hn := Nat.find_min hex hi
      simpa [conductorRadius, hj0] using lt_of_not_ge hn
  refine ⟨j, mem_range.mpr (by omega), hl.le.trans hqu', ?_⟩
  exact (mem_conductorCell_iff
    (zero_le_one.trans (conductorRadius_ge_one j hx hB)) q).mpr ⟨hl, hu⟩

theorem source_depth_le {x A₁ A₂ : ℕ} (hA : A₂ ≤ x) :
    panDyadicDepth A₁ A₂ ≤ Nat.log 2 x + 1 := by
  exact Nat.add_le_add_right
    (Nat.log_mono_right ((Nat.div_le_self A₂ A₁).trans hA)) 1

/-- Domination by active real conductor cells, with triangle inequalities only
over the complete source blocks. The last conductor cell may extend beyond
the closed outer cutoff. -/
theorem panIymHigh_le_sum_active_sourceCells
    (f : ℕ → ℂ) (m x A₁ A₂ : ℕ) (B : ℝ)
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) (hA₁ : 0 < A₁) :
    panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
        ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊ ≤
      ∑ j ∈ (range (Nat.log 2 x + 1)).filter
          (fun j => conductorRadius x B j ≤ upperConductor x B),
        ∑ k ∈ range (panDyadicDepth A₁ A₂),
          sourceCell f m x A₁ A₂ k (conductorRadius x B j) := by
  let s := (range (Nat.log 2 x + 1)).filter
    (fun j => conductorRadius x B j ≤ upperConductor x B)
  let w := fun q : ℕ => (q.totient : ℝ)⁻¹ *
    ∑ χ : PrimitiveCharacter q,
      ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) x A₁ A₂ χ‖
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
                ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) x
                  (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ := by
          apply sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum
          intro χ hχ
          rw [panSourceCharacterAmplitude_eq_sum_dyadicCells
            (panSourceG f m) (panSourceD m) x A₁ A₂ hA₁ χ]
          convert norm_sum_le _ _ using 1 <;>
            first | rfl | simp [pow_succ, mul_comm, mul_left_comm]
        _ = ∑ k ∈ range (panDyadicDepth A₁ A₂),
            sourceCell f m x A₁ A₂ k (conductorRadius x B j) := by
          unfold sourceCell
          simp_rw [mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro q hq
          rw [sum_comm]

/-- The uniform full high-source bound with its explicit logarithmic depths. -/
theorem chosen_high_source_depth_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ),
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
          ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊ ≤
        (Nat.log 2 x + 1 : ℝ) ^ 2 *
          (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
  obtain ⟨C, hC, hcell⟩ := chosen_source_cell_log_saving
  refine ⟨C, hC, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hcell B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f hAx hApower hAlow hf
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
        sourceCell f m x A₁ A₂ k (conductorRadius x B j) :=
      panIymHigh_le_sum_active_sourceCells f m x A₁ A₂ B hxlog1 hB hA₁
    _ ≤ ∑ j ∈ s, ∑ _k ∈ range (panDyadicDepth A₁ A₂), M := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro k hk
      exact hX₁ x ((le_max_left X₁ X₂).trans hx) j m A₁ A₂ k f hAx
        (mem_filter.mp hj).2 hApower hAlow hf
    _ = (s.card : ℝ) * (panDyadicDepth A₁ A₂ : ℝ) * M := by simp; ring
    _ ≤ (Nat.log 2 x + 1 : ℝ) * (Nat.log 2 x + 1 : ℝ) * M := by
      gcongr
      · exact_mod_cast hs
      · exact_mod_cast source_depth_le (A₁ := A₁) hAx
    _ = _ := by rw [pow_two]

theorem log_depth_le_three_log {x : ℕ} (hx : 4 ≤ Real.log x) :
    (Nat.log 2 x + 1 : ℝ) ≤ 3 * Real.log x := by
  have hxpos : 0 < x := source_pos_of_log (by linarith)
  have hp : (2 : ℝ) ^ Nat.log 2 x ≤ x := by
    exact_mod_cast Nat.pow_log_le_self 2 hxpos.ne'
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 x) hp
  rw [Real.log_pow] at hlog
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hn : (0 : ℝ) ≤ Nat.log 2 x := Nat.cast_nonneg _
  nlinarith

/-- Arbitrary logarithmic saving for the full high source sum, with the
explicit Perron remainder after both logarithmic-depth summations.
This does not assert the low-conductor or induced-character discrepancy
assembly. -/
theorem chosen_high_source_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (m A₁ A₂ : ℕ) (f : ℕ → ℂ),
      A₂ ≤ x → (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ A₁ → (∀ n, ‖f n‖ ≤ 1) →
      panIymHigh (panSourceG f m) (panSourceD m) x A₁ A₂
          ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊ ≤
        C * (x : ℝ) * Real.log x ^ (6 - B) +
          6984 * (Real.log x) ^ 2 / (x : ℝ) := by
  obtain ⟨C, hC, hdepth⟩ := chosen_high_source_depth_saving
  refine ⟨9 * C, by positivity, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hdepth B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx m A₁ A₂ f hAx hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  calc
    _ ≤ (Nat.log 2 x + 1 : ℝ) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) :=
      hX₁ x ((le_max_left X₁ X₂).trans hx) m A₁ A₂ f hAx hApower hAlow hf
    _ ≤ (3 * Real.log x) ^ 2 *
        (C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ)) := by
      gcongr
      exact log_depth_le_three_log hxlog
    _ = _ := by
      rw [show (6 - B : ℝ) = 2 + (4 - B) by ring, Real.rpow_add hlogpos,
        Real.rpow_two]
      ring

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
