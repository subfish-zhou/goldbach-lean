import FeedbackFixedPoint

namespace FeedbackLimit
open Wu2008DoubleSieve NodeExtension ActualNineFeedback DirectFiniteF6
open Set Filter MeasureTheory QuarterTrim
open scoped Topology Classical
noncomputable section

def Winf : Fin 21 → ℝ := matrixApply transferMatrix Ainf

def Cinf : ℝ := Gamma Winf 0

theorem transferredLower_tendsto (j : Fin 21) :
    Tendsto (fun n => transferredLower n j) atTop (𝓝 (Winf j)) :=
  matrixApply_tendsto transferMatrix lowerIterate_tendsto j

theorem transferredLower_le_Winf (n : ℕ) (j : Fin 21) :
    transferredLower n j ≤ Winf j :=
  matrixApply_mono transferMatrix_nonneg (lowerIterate_le_Ainf n) j

theorem Winf_nonneg (j : Fin 21) : 0 ≤ Winf j :=
  matrixApply_nonneg transferMatrix_nonneg Ainf_nonneg j

/-- The original list evaluator selects a fixed coordinate on each original
half-open cell. Only the heights vary; the domain and breakpoints do not. -/
theorem eval_map_tendsto (L : List (Fin 21)) {w : ℕ → Fin 21 → ℝ}
    {z : Fin 21 → ℝ} (h : ∀ j, Tendsto (fun n => w n j) atTop (𝓝 (z j))) (s : ℝ) :
    Tendsto (fun n => Wu08Staircase.eval (L.map (row (w n))) s) atTop
      (𝓝 (Wu08Staircase.eval (L.map (row z)) s)) := by
  induction L with
  | nil => simpa only [List.map_nil, Wu08Staircase.eval] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  | cons j L ih =>
    simp only [List.map_cons, row, Wu08Staircase.eval]
    split_ifs <;> first | exact h j | exact ih

theorem profile_tendsto (s : ℝ) :
    Tendsto (fun n => profile (transferredLower n) s) atTop (𝓝 (profile Winf s)) :=
  eval_map_tendsto _ transferredLower_tendsto s

theorem uniform_tendsto (v : ℝ × ℝ) :
    Tendsto (fun n => uniform (transferredLower n) 0 v) atTop (𝓝 (uniform Winf 0 v)) := by
  unfold uniform
  split_ifs
  · exact (profile_tendsto (u v.1 v.2)).div_const _
  · exact tendsto_const_nhds

/-- Dominated convergence with the existing integrable uniform kernel at T B.
There is no integral-interchange premise or alteration of the original domain. -/
theorem C_tendsto : Tendsto C atTop (𝓝 Cinf) := by
  have hd := tendsto_integral_of_dominated_convergence
    (uniform (matrixApply transferMatrix B) 0)
    (fun n => (uniform_integrable (transferredLower n) le_rfl).aestronglyMeasurable)
    (uniform_integrable (matrixApply transferMatrix B) le_rfl)
    (fun n => Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (uniform_nonneg (transferredLower_nonneg n) le_rfl v)]
      exact uniform_mono (fun j => matrixApply_mono transferMatrix_nonneg
        (lowerIterate_le_B n) j) le_rfl v))
    (Filter.Eventually.of_forall uniform_tendsto)
  exact hd.const_mul 4

theorem C_le_Cinf (n : ℕ) : C n ≤ Cinf :=
  Gamma_mono (transferredLower_le_Winf n) le_rfl

theorem Cinf_nonneg : 0 ≤ Cinf := Gamma_nonneg Winf_nonneg le_rfl

/-- This minimizes only the output on the fixed system's nonnegative
supersolutions. It is not an upper bound on the actual count or sieve gain. -/
theorem Cinf_le_supersolution_output {z : Fin 9 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hs : ∀ i, base i + matrixApply feedbackMatrix z i ≤ z i) :
    Cinf ≤ Gamma (matrixApply transferMatrix z) 0 :=
  Gamma_mono (fun j => matrixApply_mono transferMatrix_nonneg
    (Ainf_le_supersolution hz hs) j) le_rfl

end
end FeedbackLimit
