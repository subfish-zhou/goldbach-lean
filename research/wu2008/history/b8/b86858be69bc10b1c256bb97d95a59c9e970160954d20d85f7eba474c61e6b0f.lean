import RMapMSigmaRegularity
import RMapMSigmaCoefficients
import RMapMSigmaHGrid

noncomputable section
namespace WuPaper.RMapMSigma
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open scoped Interval BigOperators

def sourceExtended (Y : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i ≤ 10 then Y i
  else ∑ k ∈ Finset.Icc 2 10, sourceCoefficient k i * Y k

theorem sourceExtended_lower {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {Y : ℕ → ℝ} (hY : ∀ i, 2 ≤ i → i ≤ 10 →
      Y i ≤ wuImprovementLimit true δ (rNode i))
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    sourceExtended Y i ≤ wuImprovementLimit true δ (rNode i) := by
  unfold sourceExtended
  split_ifs with h
  · exact hY i hi h
  · exact equation310_input_lower hd hdhi hY (by omega) hi29

theorem sourceExtended_mono {Y Z : ℕ → ℝ}
    (hYZ : ∀ k, 2 ≤ k → k ≤ 10 → Y k ≤ Z k)
    {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) :
    sourceExtended Y i ≤ sourceExtended Z i := by
  unfold sourceExtended
  split_ifs with h
  · exact hYZ i hi h
  · apply Finset.sum_le_sum
    intro k hk
    have hb := Finset.mem_Icc.mp hk
    exact mul_le_mul_of_nonneg_left (hYZ k hb.1 hb.2)
      (sourceCoefficient_nonneg hb.1 hb.2 (by omega) hi29)

theorem original_grid_from_nine {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {Y : ℕ → ℝ} (hY : ∀ i, 2 ≤ i → i ≤ 10 →
      Y i ≤ wuImprovementLimit true δ (rNode i)) :
    (∀ i : ℕ, 2 ≤ i → i ≤ 29 →
      sourceExtended Y i ≤ wuImprovementLimit true δ (rNode i)) ∧
    (∀ j : ℕ, j ≤ 29 →
      hGridExpression (sourceExtended Y) j ≤ wuImprovementLimit false δ (rNode j)) :=
  ⟨fun _ hi hi29 => sourceExtended_lower hd hdhi hY hi hi29,
    fun _ hj => equation311_input_lower hd hdhi
      (fun _ hi hi29 => sourceExtended_lower hd hdhi hY hi hi29) hj⟩

theorem original_grid_uniform {Y : ℕ → ℝ}
    (hY : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ i, 2 ≤ i → i ≤ 10 →
      Y i ≤ wuImprovementLimit true δ (rNode i)) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 →
      (∀ i : ℕ, 2 ≤ i → i ≤ 29 →
        sourceExtended Y i ≤ wuImprovementLimit true δ (rNode i)) ∧
      (∀ j : ℕ, j ≤ 29 →
        hGridExpression (sourceExtended Y) j ≤ wuImprovementLimit false δ (rNode j)) :=
  fun δ hd hdhi => original_grid_from_nine hd hdhi (hY δ hd hdhi)

theorem original_grid_input_mono {Y Z : ℕ → ℝ}
    (hYZ : ∀ k, 2 ≤ k → k ≤ 10 → Y k ≤ Z k) {j : ℕ} (hj : j ≤ 29) :
    hGridExpression (sourceExtended Y) j ≤ hGridExpression (sourceExtended Z) j :=
  hGridExpression_mono (fun _ hi hi29 => sourceExtended_mono hYZ hi hi29) hj

theorem original_lemma61 {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    ((∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * (sigma0 t / t)) ≤
      wuImprovementLimit false δ 4) ∧
    (∀ s ∈ Icc (3 : ℝ) 5,
      (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * upperKernel s t) ≤
        wuImprovementLimit true δ s) ∧
    (∀ a b c : ℝ, 0 < a → a < b → b < 1 → 2 ≤ a * c → b * c ≤ 4 →
      source63RHS (wuImprovementLimit true δ) a b c ≤
        ∫ t in a..b, wuImprovementLimit false δ (c * t) / (t * (1 - t))) :=
  ⟨lemma61 hd hdhi, fun _ hs => lemma62 hd hdhi hs,
    fun _ _ _ ha hab hb hac hbc => lemma63 hd hdhi ha hab hb hac hbc⟩

end WuPaper.RMapMSigma

#check @WuPaper.RMapMSigma.sourceExtended
#check @WuPaper.RMapMSigma.sourceExtended_lower
#check @WuPaper.RMapMSigma.sourceExtended_mono
#check @WuPaper.RMapMSigma.original_grid_from_nine
#check @WuPaper.RMapMSigma.original_grid_uniform
#check @WuPaper.RMapMSigma.original_grid_input_mono
#check @WuPaper.RMapMSigma.original_lemma61
#print axioms WuPaper.RMapMSigma.sourceExtended
#print axioms WuPaper.RMapMSigma.sourceExtended_lower
#print axioms WuPaper.RMapMSigma.sourceExtended_mono
#print axioms WuPaper.RMapMSigma.original_grid_from_nine
#print axioms WuPaper.RMapMSigma.original_grid_uniform
#print axioms WuPaper.RMapMSigma.original_grid_input_mono
#print axioms WuPaper.RMapMSigma.original_lemma61

#check @NodeExtension.actual_continuous_extension
#check @NodeExtension.sigma_feedback
#check @NodeExtension.D0_bounds
#check @Wu2008DoubleSieve.wuImprovementLimit_upper_cross
#check @Wu2008DoubleSieve.wuImprovementLimit_lower_cross
#check @Wu2008DoubleSieve.wuImprovementLimit_upper_antitone
#check @WuSource.SrcGrid.full_tables_lower
#print axioms NodeExtension.actual_continuous_extension
#print axioms NodeExtension.sigma_feedback
#print axioms NodeExtension.D0_bounds
#print axioms Wu2008DoubleSieve.wuImprovementLimit_upper_cross
#print axioms Wu2008DoubleSieve.wuImprovementLimit_lower_cross
#print axioms Wu2008DoubleSieve.wuImprovementLimit_upper_antitone
#print axioms WuSource.SrcGrid.full_tables_lower
