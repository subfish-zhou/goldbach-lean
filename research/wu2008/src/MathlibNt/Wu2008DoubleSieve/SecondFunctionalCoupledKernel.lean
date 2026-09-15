import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairGainKThetaMother

namespace Wu2008DoubleSieve.SecondFunctionalCoupled
open Finset Real HighSourcePayload
open scoped Classical

/-- All fourteen original integrals are added at one common phi before any supremum. -/
noncomputable def kernel (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j : Fin 6, LowerTripleContinuous.K (1/p.S) (1/p.kappa1) (1/p.kappa2)
    (1/p.kappa3) (1/p.s) j phi) +
  ((HighUnit.J20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
    HighUnit.J21 (1/p.kappa3) (1/p.s) phi) +
    (HighNonunitLegal.K20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
      HighNonunitLegal.K21 (1/p.kappa3) (1/p.s) phi) +
    ∑ j : Fin 4, FourPrimeNonunit.legalK (1/p.kappa1) (1/p.kappa2)
      (1/p.kappa3) (1/p.s) phi j)

/-- Exact original source identification, including the shared supported d. -/
theorem kernel_actual (N d : ℕ) (δ : ℝ) (p : SecondFunctionalParameters) :
    kernel p (omega3XPhi N d δ) =
      (∑ j : Fin 6, LowerTripleSourceK.sourceIntegralK N d δ p j) +
        secondFunctionalCombinedKernel N d δ p := by
  simp only [kernel, LowerTripleSourceK.sourceIntegralK, secondFunctionalCombinedKernel,
    paired, unitPair, HighNonunit.sourceLegalK, FourPrimeNonunit.sourceLegalK,
    Bool.false_eq_true, ↓reduceIte]

/-- A deliberately coarse existence bound, never the headline scalar coefficient. -/
def existenceCap : ℝ := 6*10*4^3 + 2000 + 10*4^5 + 10*4^6 + 4*10*4^4

theorem kernel_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) : 0 ≤ kernel p phi ∧ kernel p phi ≤ existenceCap := by
  have hl (j : Fin 6) := LowerTripleContinuous.K_bounds
    (LowerTripleContinuous.mother_compact_parameters p hp hs) j phi
  have hf (j : Fin 4) := FourPrimeNonunit.legalK_bounds
    (FourPrimeNonunit.legalK_mother_compact p hp hs) phi j
  obtain ⟨ha, haa, hab, hb⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  have hj0 := add_nonneg (HighUnit.J20_nonneg ha haa hab hb phi)
    (HighUnit.J21_nonneg (ha.trans haa) hb phi)
  have hj1 := (add_le_add (HighUnit.J20_log_cap ha haa hab hb phi)
    (HighUnit.J21_log_cap (ha.trans haa) hab hb phi)).trans
      (HighUnitSource.unitLogCap_pair_compact ha haa hab hb).2
  have h20 := HighNonunitLegal.K20_bounds (a3 := 1/p.kappa3) ha hb phi
  have h21 := HighNonunitLegal.K21_bounds (ha.trans haa) hb phi
  have hl0 := sum_nonneg (fun j (_ : j ∈ (univ : Finset (Fin 6))) => (hl j).1)
  have hf0 := sum_nonneg (fun j (_ : j ∈ (univ : Finset (Fin 4))) => (hf j).1)
  have hl1 := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 6))) => (hl j).2)
  have hf1 := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => (hf j).2)
  norm_num only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hl1 hf1
  unfold kernel existenceCap
  constructor <;> linarith only [hl0, hf0, hj0, hj1, h20.1, h20.2, h21.1, h21.2, hl1, hf1]

/-- The admissible phi domain is fixed independently of depth, N and boxes. -/
def values (p : SecondFunctionalParameters) : Set ℝ := kernel p '' Set.Ici 2

noncomputable def jointSup (p : SecondFunctionalParameters) : ℝ := sSup (values p)

theorem values_nonempty (p : SecondFunctionalParameters) : (values p).Nonempty :=
  ⟨kernel p 2, 2, (by simp), rfl⟩

theorem values_bddAbove (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : BddAbove (values p) := by
  refine ⟨existenceCap, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (kernel_bounds p hp hs phi).2

theorem kernel_le_jointSup (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) : kernel p phi ≤ jointSup p :=
  le_csSup (values_bddAbove p hp hs) ⟨phi, hphi, rfl⟩

theorem jointSup_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : 0 ≤ jointSup p ∧ jointSup p ≤ existenceCap := by
  refine ⟨(kernel_bounds p hp hs 2).1.trans (kernel_le_jointSup p hp hs le_rfl), ?_⟩
  apply csSup_le (values_nonempty p)
  rintro _ ⟨phi, _, rfl⟩
  exact (kernel_bounds p hp hs phi).2

/-- The original box geometry automatically places the actual phi in the fixed domain. -/
theorem actual_phi_ge_two {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    2 ≤ omega3XPhi N d δ := by
  have hg := omega3XPhi_source_bounds (by omega) hδ hδhi hb hd
  have hgap : 0 ≤ 2*δ/(1/2-δ) := div_nonneg (by positivity) (by linarith)
  linarith [hg.2.2.1]

/-- Exact original true-li and totient-weighted summation; no division by Theta. -/
theorem theta_exact (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) :
    theta N δ Δ V (fun d => kernel p (omega3XPhi N d δ)) =
      (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
        secondFunctionalCombinedTheta N δ Δ V p := by
  simp_rw [kernel_actual]
  rw [← LowerTripleSourceK.sourceKTheta_sum]
  simp only [theta, secondFunctionalCombinedTheta, mul_add, sum_add_distrib]

/-- Every original payload is controlled by the actual same-phi joint supremum. -/
theorem theta_scalarization {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    0 ≤ (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
        secondFunctionalCombinedTheta N δ Δ V p ∧
    (∑ j : Fin 6, LowerTripleSourceK.sourceKTheta N δ Δ V p j) +
        secondFunctionalCombinedTheta N δ Δ V p ≤
      jointSup p * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  rw [← theta_exact]
  apply theta_bounds hN hδ hδhi hb
  intro d hd
  exact ⟨(kernel_bounds p hp hs _).1,
    kernel_le_jointSup p hp hs (actual_phi_ge_two hN hδ hδhi hb hd)⟩

end Wu2008DoubleSieve.SecondFunctionalCoupled
