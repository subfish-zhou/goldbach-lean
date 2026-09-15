import MathlibNt.Wu2008DoubleSieve.FourSeventhsBuchstab
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalJointTailTransport
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPositiveMatrix

namespace Wu2008DoubleSieve.SecondFunctionalFourSevenths
open Set Real MeasureTheory LiLiuPrereqBuchstab SecondFunctionalJointTail
open SecondFunctionalParameters SecondFunctionalPositive
open scoped BigOperators

/-- The six fixed endpoint inequalities, with their original multiplicities. -/
def EndpointGate (b c e f : ℝ) : Prop :=
  (15/4)*c + f ≤ 2 ∧ c + (15/4)*e ≤ 2 ∧ (15/4)*b + f ≤ 2 ∧
    b + (11/4)*c + f ≤ 2 ∧ b + (15/4)*f ≤ 2 ∧ c + (11/4)*e + f ≤ 2

/-- All twenty-four obligations are reduced from the original four rows. -/
theorem original_endpoint_gate (i : Fin 4) :
    EndpointGate (1/(parameters i).kappa1) (1/(parameters i).kappa2)
      (1/(parameters i).kappa3) (1/(parameters i).s) := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [EndpointGate, row1, row2, row3, row4]

/-- Every point of each literal closed ordered domain satisfies the affine gate. -/
theorem lower_domain_gate {a b c e f : ℝ} (hg : EndpointGate b c e f) (j : Fin 6)
    {t : Fin 3 → ℝ} (ht : t ∈ LowerTripleContinuous.D a b c e f j) :
    t 0 + (11/4) * t 1 + t 2 ≤ 2 := by
  have hall : ∀ j : Fin 6, t ∈ LowerTripleContinuous.D a b c e f j →
      t 0 + (11/4) * t 1 + t 2 ≤ 2 := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
      LowerTripleContinuous.D, LowerTripleGrouped.bands,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    rcases hg with ⟨hg0, hg1, hg2, hg3, hg4, hg5⟩
    repeat' constructor
    all_goals rintro ⟨_, ht0, _, ht1, _, ht2, _, _⟩
    all_goals linarith
  exact hall j ht

/-- The actual rows supply all compact positivity hypotheses internally. -/
theorem original_compact (i : Fin 4) :
    LowerTripleContinuous.CompactParameters (1/(parameters i).S)
      (1/(parameters i).kappa1) (1/(parameters i).kappa2)
      (1/(parameters i).kappa3) (1/(parameters i).s) := by
  revert i
  simp only [parameters, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [LowerTripleContinuous.CompactParameters, row1, row2, row3, row4]

/-- The lower-kernel argument is in the proved Buchstab tail, including phi=2. -/
theorem original_lower_argument (i : Fin 4) (j : Fin 6) {phi : ℝ} (hphi : 2 ≤ phi)
    {t : Fin 3 → ℝ} (ht : t ∈ LowerTripleContinuous.D (1/(parameters i).S)
      (1/(parameters i).kappa1) (1/(parameters i).kappa2)
      (1/(parameters i).kappa3) (1/(parameters i).s) j) :
    (7/4 : ℝ) ≤ (phi - (t 0 + t 1 + t 2)) / t 1 := by
  have hg := lower_domain_gate (original_endpoint_gate i) j ht
  have hc := LowerTripleContinuous.D_subset_cube (original_compact i) j ht
  have hp : 0 < t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  apply (le_div_iff₀ hp).2
  linarith

/-- All six actual integrals are bounded by their own true reciprocal masses. -/
theorem original_lower_mass_bound (i : Fin 4) (j : Fin 6) {phi : ℝ} (hphi : 2 ≤ phi) :
    LowerTripleContinuous.K (1/(parameters i).S) (1/(parameters i).kappa1)
      (1/(parameters i).kappa2) (1/(parameters i).kappa3) (1/(parameters i).s) j phi ≤
      (4/7) * lowerMass (parameters i) j := by
  have hsub := LowerTripleContinuous.D_subset_cube (original_compact i) j
  have hw := geometricWeight_integrable 1 hsub
  have hk := LowerTripleContinuous.K_integrable (original_compact i) j phi
  change (∫ t in _, LowerTripleContinuous.G phi t * continuousDensity t) ≤
    (4/7) * ∫ t in _, geometricWeight 1 t
  rw [← integral_const_mul]
  apply setIntegral_mono_on hk (hw.const_mul _) (LowerTripleContinuous.D_measurable _ _ _ _ _ j)
  intro t ht
  have hc := hsub ht
  rw [LowerTripleContinuous.G_cube_literal hphi hc]
  have hb := buchstab_le_four_sevenths (original_lower_argument i j hphi ht)
  have hd := continuousDensity_nonneg hc
  have hp : 0 < t 1 := by linarith [(hc 1 (mem_univ 1)).1]
  calc
    _ ≤ ((4/7) / t 1) * continuousDensity t :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hp.le) hd
    _ = _ := by unfold geometricWeight; ring

/-- Addition is at one and the same phi, with six independent original labels. -/
theorem original_lower_sum_bound (i : Fin 4) {phi : ℝ} (hphi : 2 ≤ phi) :
    (∑ j : Fin 6, LowerTripleContinuous.K (1/(parameters i).S)
      (1/(parameters i).kappa1) (1/(parameters i).kappa2)
      (1/(parameters i).kappa3) (1/(parameters i).s) j phi) ≤
      (4/7) * ∑ j : Fin 6, lowerMass (parameters i) j := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => original_lower_mass_bound i j hphi)

end Wu2008DoubleSieve.SecondFunctionalFourSevenths
