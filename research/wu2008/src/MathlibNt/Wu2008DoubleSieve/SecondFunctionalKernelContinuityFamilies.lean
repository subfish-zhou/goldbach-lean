import MathlibNt.Wu2008DoubleSieve.SecondFunctionalKernelContinuityBuchstab

namespace Wu2008DoubleSieve.SecondFunctionalJointTail
open Set MeasureTheory
open scoped BigOperators

/-- Removing a duplicate legal gate does not remove the gate in the integrand. -/
theorem integral_inter_legal {n : ℕ} (j : Fin n) (phi : ℝ) (D : Set (Fin n → ℝ)) :
    (∫ t in D ∩ HighNonunitLegal.legal j phi,
      HighNonunitLegal.G j phi t * continuousDensity t) =
    ∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t := by
  rw [← setIntegral_indicator (HighNonunitLegal.legal_measurable j phi)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ HighNonunitLegal.legal j phi
  · exact indicator_of_mem ht _
  · simp only [indicator_of_notMem ht, HighNonunitLegal.G_of_illegal ht, zero_mul]

theorem high_K20_continuous {a2 a3 b : ℝ} (ha : 1 / 10 ≤ a2) (hb : b ≤ 1 / 2) :
    Continuous (HighNonunitLegal.K20 a2 a3 b) := by
  let E : Set (Fin 5 → ℝ) :=
    {t | a2 ≤ t 0 ∧ t 0 ≤ a3 ∧ a3 ≤ t 1 ∧ Monotone t ∧ t 4 ≤ b}
  have he : HighNonunitLegal.D20 a2 a3 b (a3 + 5*b) = E := D20_eq_of_tail le_rfl
  have hm : MeasurableSet E := he ▸ HighNonunitLegal.D20_measurable a2 a3 b _
  have hc : E ⊆ continuousCube 5 := he ▸ HighNonunitLegal.D20_subset_cube ha hb
  apply (buchstab_integral_continuous 3 E hm hc).congr
  intro phi
  exact (integral_inter_legal 3 phi E).symm

theorem high_K21_continuous {a3 b : ℝ} (ha : 1 / 10 ≤ a3) (hb : b ≤ 1 / 2) :
    Continuous (HighNonunitLegal.K21 a3 b) := by
  let E : Set (Fin 6 → ℝ) := {t | a3 ≤ t 0 ∧ Monotone t ∧ t 5 ≤ b}
  have he : HighNonunitLegal.D21 a3 b (7*b) = E := D21_eq_of_tail le_rfl
  have hm : MeasurableSet E := he ▸ HighNonunitLegal.D21_measurable a3 b _
  have hc : E ⊆ continuousCube 6 := he ▸ HighNonunitLegal.D21_subset_cube ha hb
  apply (buchstab_integral_continuous 4 E hm hc).congr
  intro phi
  exact (integral_inter_legal 4 phi E).symm

/-- All four original full-dimensional four-prime integrals. -/
theorem four_legalK_continuous {b c e f : ℝ}
    (hp : FourPrimeContinuous.CompactParameters b c e f) (j : Fin 4) :
    Continuous (fun phi => FourPrimeNonunit.legalK b c e f phi j) := by
  have h16 : Continuous (FourPrimeContinuous.K16 c e) :=
    buchstab_integral_continuous 2 _ (FourPrimeContinuous.D16_measurable c e)
      (FourPrimeContinuous.D16_subset_cube hp)
  have h17 : Continuous (FourPrimeContinuous.K17 c e f) :=
    buchstab_integral_continuous 2 _ (FourPrimeContinuous.D17_measurable c e f)
      (FourPrimeContinuous.D17_subset_cube hp)
  have h18 : Continuous (FourPrimeContinuous.K18 c e f) :=
    buchstab_integral_continuous 2 _ (FourPrimeContinuous.D18_measurable c e f)
      (FourPrimeContinuous.D18_subset_cube hp)
  have h19 : Continuous (FourPrimeContinuous.K19 b c e f) :=
    buchstab_integral_continuous 2 _ (FourPrimeContinuous.D19_measurable b c e f)
      (FourPrimeContinuous.D19_subset_cube hp)
  have hall : ∀ j : Fin 4, Continuous (fun phi => FourPrimeNonunit.legalK b c e f phi j) := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨h16, h17, h18, h19⟩
  exact hall j

end Wu2008DoubleSieve.SecondFunctionalJointTail
