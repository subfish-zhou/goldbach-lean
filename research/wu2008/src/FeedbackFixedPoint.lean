import FeedbackBound
namespace FeedbackLimit
open Wu2008DoubleSieve NodeExtension ActualNineFeedback Set Filter
open scoped Topology BigOperators
noncomputable section

theorem matrixApply_tendsto {m k : ℕ} (M : Fin m → Fin k → ℝ)
    {x : ℕ → Fin k → ℝ} {z : Fin k → ℝ}
    (h : ∀ j, Tendsto (fun n => x n j) atTop (𝓝 (z j))) (i : Fin m) :
    Tendsto (fun n => matrixApply M (x n) i) atTop (𝓝 (matrixApply M z i)) := by
  exact tendsto_finsetSum _ (fun j _ => (h j).const_mul (M i j))

theorem Ainf_fixed (i : Fin 9) :
    Ainf i = max 0 (base i + matrixApply feedbackMatrix Ainf i) := by
  have hs : Tendsto (fun n => lowerIterate (n+1) i) atTop (𝓝 (Ainf i)) :=
    (lowerIterate_tendsto i).comp (tendsto_add_atTop_nat 1)
  have ht := (tendsto_const_nhds (x := (0 : ℝ))).max
    ((matrixApply_tendsto feedbackMatrix lowerIterate_tendsto i).const_add (base i))
  exact tendsto_nhds_unique hs ht

theorem iterate_le_supersolution {z : Fin 9 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hs : ∀ i, base i + matrixApply feedbackMatrix z i ≤ z i) (n : ℕ) :
    ∀ i, lowerIterate n i ≤ z i := by
  induction n with
  | zero => exact hz
  | succ n ih =>
    intro i
    exact max_le (hz i) ((add_le_add le_rfl
      (matrixApply_mono feedbackMatrix_nonneg ih i)).trans (hs i))

theorem Ainf_le_supersolution {z : Fin 9 → ℝ} (hz : ∀ i, 0 ≤ z i)
    (hs : ∀ i, base i + matrixApply feedbackMatrix z i ≤ z i) (i : Fin 9) :
    Ainf i ≤ z i := ciSup_le (fun n => iterate_le_supersolution hz hs n i)

theorem Ainf_supersolution (i : Fin 9) :
    base i + matrixApply feedbackMatrix Ainf i ≤ Ainf i := by
  rw [Ainf_fixed i]
  exact le_max_right _ _

/-- Least in the specified nonnegative supersolution set, not an optimality
claim over all sieve functions or actual counting gains. -/
theorem Ainf_isLeast : IsLeast
    {z : Fin 9 → ℝ | (∀ i, 0 ≤ z i) ∧
      ∀ i, base i + matrixApply feedbackMatrix z i ≤ z i} Ainf :=
  ⟨⟨Ainf_nonneg, Ainf_supersolution⟩,
    fun _ hz i => Ainf_le_supersolution hz.1 hz.2 i⟩
end
end FeedbackLimit
