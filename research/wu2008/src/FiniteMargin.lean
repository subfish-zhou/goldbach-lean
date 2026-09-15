import FiniteIteration

namespace ActualNineFeedback
open Wu2008DoubleSieve NodeExtension
open scoped BigOperators

/-- Finite strict inequalities admit a common positive margin, without evaluation. -/
theorem finite_positive_margin {ι : Type*} (s : Finset ι) (q a : ι → ℝ)
    (h : ∀ j ∈ s, q j < a j) : ∃ μ : ℝ, 0 < μ ∧ ∀ j ∈ s, q j + μ ≤ a j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨μ, hμ, hm⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have hjp : 0 < a j - q j := sub_pos.mpr (h j (Finset.mem_insert_self j s))
    refine ⟨min μ (a j - q j), lt_min hμ hjp, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · have he := min_le_right μ (a k - q k)
      linarith
    · have he := min_le_left μ (a j - q j)
      linarith [hm k hk]

noncomputable def transferredLower (n : ℕ) : Fin 21 → ℝ :=
  matrixApply transferMatrix (lowerIterate n)

noncomputable def transferredDebit (n : ℕ) : Fin 21 → ℝ :=
  matrixApply transferMatrix (debitIterate n)

noncomputable def totalDebit (n : ℕ) : ℝ := ∑ j, transferredDebit n j

theorem transferredDebit_nonneg (n : ℕ) (j : Fin 21) : 0 ≤ transferredDebit n j :=
  matrixApply_nonneg transferMatrix_nonneg (debitIterate_nonneg n) j

theorem totalDebit_nonneg (n : ℕ) : 0 ≤ totalDebit n :=
  Finset.sum_nonneg (fun j _ => transferredDebit_nonneg n j)

theorem transferredDebit_le_total (n : ℕ) (j : Fin 21) :
    transferredDebit n j ≤ totalDebit n :=
  Finset.single_le_sum (fun k _ => transferredDebit_nonneg n k) (Finset.mem_univ j)

noncomputable def marginRadius (K μ : ℝ) : ℝ := min (1 / 10) (μ / (2 * (K + μ)))

theorem marginRadius_pos {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 < μ) :
    0 < marginRadius K μ := by
  exact lt_min (by norm_num) (div_pos hμ (by positivity))

theorem deltaLoss_mul_lt_margin {K μ δ : ℝ} (hK : 0 ≤ K) (hμ : 0 < μ)
    (hd : 0 < δ) (hs : δ < marginRadius K μ) : deltaLoss δ * K < μ := by
  have hsmall : δ < 1 / 10 := hs.trans_le (min_le_left _ _)
  have hfrac : δ < μ / (2 * (K + μ)) := hs.trans_le (min_le_right _ _)
  have hden : 0 < 1 - 2 * δ := by linarith
  have hprod := (lt_div_iff₀ (show 0 < 2 * (K + μ) by positivity)).mp hfrac
  unfold deltaLoss
  rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
  nlinarith only [hprod]

/-- The only remaining premise is a fixed, delta-independent finite output margin. -/
theorem finite_strict_output_eventually (n : ℕ) (q : Fin 21 → ℝ)
    (h : ∀ j, q j < transferredLower n j) :
    ∃ μ : ℝ, 0 < μ ∧ (∀ j, q j + μ ≤ transferredLower n j) ∧
      0 < marginRadius (totalDebit n) μ ∧
      ∀ δ : ℝ, 0 < δ → δ < marginRadius (totalDebit n) μ →
        ∀ j : Fin 21, q j < wuImprovementLimit false δ (rNode (j.val + 1)) := by
  obtain ⟨μ, hμ, hm⟩ := finite_positive_margin Finset.univ q (transferredLower n)
    (fun j _ => h j)
  have hm' : ∀ j, q j + μ ≤ transferredLower n j := fun j => hm j (Finset.mem_univ j)
  refine ⟨μ, hμ, hm', marginRadius_pos (totalDebit_nonneg n) hμ, ?_⟩
  intro δ hd hs j
  have hh : δ ≤ 1 / 10 := hs.le.trans (min_le_left _ _)
  have hb := finite_actual_twentyone hd hh n j
  change transferredLower n j - deltaLoss δ * transferredDebit n j ≤ _ at hb
  have hpay := deltaLoss_mul_lt_margin (totalDebit_nonneg n) hμ hd hs
  have hcost := mul_le_mul_of_nonneg_left (transferredDebit_le_total n j)
    (deltaLoss_nonneg hd hh)
  linarith [hm' j]

end ActualNineFeedback
