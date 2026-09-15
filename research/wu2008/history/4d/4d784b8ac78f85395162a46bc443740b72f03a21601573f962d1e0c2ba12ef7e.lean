import SrcNineAnalyticExtension

noncomputable section
namespace WuSource.SrcNine.Analytic
open Set MeasureTheory Wu2008DoubleSieve
open scoped BigOperators Interval

def rawSum (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j, rawTriple p j phi) + (∑ j, rawFour p j phi) + rawFive p phi + rawSix p phi

def illegalSum (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j, illegalFour p j phi) + illegalFive p phi + illegalSix p phi

def unitSum (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  HighUnit.J20 (1/p.kappa2) (1/p.kappa3) (1/p.s) phi +
    HighUnit.J21 (1/p.kappa3) (1/p.s) phi

theorem kernel_literal_split (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    SecondFunctionalCoupled.kernel p phi + illegalSum p phi =
      rawSum p phi + unitSum p phi := by
  have hf := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => four_split p hp hs phi j)
  rw [Finset.sum_add_distrib] at hf
  have h5 := five_split p hp hs phi
  have h6 := six_split p hp hs phi
  simp only [SecondFunctionalCoupled.kernel, triple_eq_raw p hp hs hphi,
    rawSum, illegalSum, unitSum]
  linarith only [hf, h5, h6]

theorem illegalSum_nonneg (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) : 0 ≤ illegalSum p phi := by
  exact add_nonneg (add_nonneg
    (Finset.sum_nonneg (fun j _ =>
      illegalIntegral_nonneg 2 phi (fourDomain_measurable p hp hs j)
        (fourDomain_subset_cube p hp hs j)))
    (illegalIntegral_nonneg 3 phi (fiveDomain_measurable p) (fiveDomain_subset_cube p hp hs)))
    (illegalIntegral_nonneg 4 phi (sixDomain_measurable p) (sixDomain_subset_cube p hp hs))

def rawEnvelope {n : ℕ} (j : Fin n) (D : Set (Fin n → ℝ)) : ℝ :=
  sSup (rawIntegral j D '' Ici 2)

def separateTwelve (p : SecondFunctionalParameters) : ℝ :=
  (∑ j, rawEnvelope 1 (tripleDomain p j)) +
    (∑ j, rawEnvelope 2 (fourDomain p j)) +
    rawEnvelope 3 (fiveDomain p) + rawEnvelope 4 (sixDomain p)

def synchronizationLoss (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j, (rawEnvelope 1 (tripleDomain p j) - rawTriple p j phi)) +
    (∑ j, (rawEnvelope 2 (fourDomain p j) - rawFour p j phi)) +
    (rawEnvelope 3 (fiveDomain p) - rawFive p phi) +
    (rawEnvelope 4 (sixDomain p) - rawSix p phi)

theorem synchronizationLoss_eq (p : SecondFunctionalParameters) (phi : ℝ) :
    synchronizationLoss p phi = separateTwelve p - rawSum p phi := by
  simp only [synchronizationLoss, separateTwelve, rawSum, Finset.sum_sub_distrib]
  ring

theorem raw_le_envelope {n : ℕ} (j : Fin n) {D : Set (Fin n → ℝ)}
    (hm : MeasurableSet D) (hD : D ⊆ continuousCube n)
    {phi : ℝ} (hphi : 2 ≤ phi) : rawIntegral j D phi ≤ rawEnvelope j D :=
  le_csSup (raw_values_bddAbove j hm hD) ⟨phi, hphi, rfl⟩

theorem synchronizationLoss_nonneg (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    0 ≤ synchronizationLoss p phi := by
  exact add_nonneg (add_nonneg (add_nonneg
    (Finset.sum_nonneg (fun j _ => sub_nonneg.mpr
      (raw_le_envelope 1 (tripleDomain_measurable p hp hs j)
        (tripleDomain_subset_cube p hp hs j) hphi)))
    (Finset.sum_nonneg (fun j _ => sub_nonneg.mpr
      (raw_le_envelope 2 (fourDomain_measurable p hp hs j)
        (fourDomain_subset_cube p hp hs j) hphi))))
    (sub_nonneg.mpr (raw_le_envelope 3 (fiveDomain_measurable p)
      (fiveDomain_subset_cube p hp hs) hphi)))
    (sub_nonneg.mpr (raw_le_envelope 4 (sixDomain_measurable p)
      (sixDomain_subset_cube p hp hs) hphi))

def sourceCorrection (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  unitSum p phi - illegalSum p phi - synchronizationLoss p phi

def correctionSup (p : SecondFunctionalParameters) : ℝ :=
  sSup (sourceCorrection p '' Ici 2)

def extendedSeparateCost (p : SecondFunctionalParameters) : ℝ :=
  omega3XIntegralEnvelope p.kappa3 p.kappa1 + separateTwelve p

theorem kernel_corrected (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    SecondFunctionalCoupled.kernel p phi = separateTwelve p + sourceCorrection p phi := by
  have h := kernel_literal_split p hp hs hphi
  rw [sourceCorrection, synchronizationLoss_eq]
  linarith only [h]

theorem correction_values_nonempty (p : SecondFunctionalParameters) :
    (sourceCorrection p '' Ici 2).Nonempty :=
  ⟨sourceCorrection p 2, 2, (by simp), rfl⟩

theorem correction_values_bddAbove (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    BddAbove (sourceCorrection p '' Ici 2) := by
  refine ⟨SecondFunctionalCoupled.existenceCap - separateTwelve p, ?_⟩
  rintro _ ⟨phi, hphi, rfl⟩
  have h := (SecondFunctionalCoupled.kernel_bounds p hp hs phi).2
  rw [kernel_corrected p hp hs hphi] at h
  linarith only [h]

theorem jointSup_corrected (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    SecondFunctionalCoupled.jointSup p = separateTwelve p + correctionSup p := by
  have hl : SecondFunctionalCoupled.jointSup p ≤ separateTwelve p + correctionSup p := by
    apply csSup_le (SecondFunctionalCoupled.values_nonempty p)
    rintro _ ⟨phi, hphi, rfl⟩
    rw [kernel_corrected p hp hs hphi]
    exact add_le_add le_rfl
      (le_csSup (correction_values_bddAbove p hp hs) ⟨phi, hphi, rfl⟩)
  have hu : correctionSup p ≤ SecondFunctionalCoupled.jointSup p - separateTwelve p := by
    apply csSup_le (correction_values_nonempty p)
    rintro _ ⟨phi, hphi, rfl⟩
    have h := SecondFunctionalCoupled.kernel_le_jointSup p hp hs hphi
    rw [kernel_corrected p hp hs hphi] at h
    linarith only [h]
  linarith only [hl, hu]

theorem coupledCostMass_corrected (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    ActualNineFeedback.coupledCostMass p = extendedSeparateCost p + correctionSup p := by
  rw [ActualNineFeedback.coupledCostMass, jointSup_corrected p hp hs]
  simp only [extendedSeparateCost, add_assoc]

theorem correction_le_unit (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    sourceCorrection p phi ≤ unitSum p phi := by
  have hi := illegalSum_nonneg p hp hs phi
  have hs := synchronizationLoss_nonneg p hp hs hphi
  unfold sourceCorrection
  linarith only [hi, hs]

theorem unitSum_zero_tail (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 3 ≤ phi) : unitSum p phi = 0 := by
  obtain ⟨h5, h6⟩ := SecondFunctionalJointTail.mother_unit_pair_zero p hp hs hphi
  simp only [unitSum, h5, h6, add_zero]

theorem illegalSum_zero_tail (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 7/2 ≤ phi) : illegalSum p phi = 0 := by
  have h4 (j : Fin 4) : illegalFour p j phi = 0 :=
    illegalIntegral_zero_of_legal 2 phi
      ((fourDomain_subset_cube p hp hs j).trans
        (SecondFunctionalJointTail.cube_legal 2 (by norm_num; linarith)))
  have h5 : illegalFive p phi = 0 := illegalIntegral_zero_of_legal 3 phi
    ((fiveDomain_subset_cube p hp hs).trans
      (SecondFunctionalJointTail.cube_legal 3 (by norm_num; linarith)))
  have h6 : illegalSix p phi = 0 := illegalIntegral_zero_of_legal 4 phi
    ((sixDomain_subset_cube p hp hs).trans
      (SecondFunctionalJointTail.cube_legal 4 (by norm_num; linarith)))
  simp only [illegalSum, h4, h5, h6, Finset.sum_const_zero, add_zero]

theorem correction_tail_nonpos (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 3 ≤ phi) :
    sourceCorrection p phi ≤ 0 := by
  have h := correction_le_unit p hp hs (show 2 ≤ phi by linarith)
  rwa [unitSum_zero_tail p hp hs hphi] at h

theorem kernel_eq_raw_tail (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 7/2 ≤ phi) :
    SecondFunctionalCoupled.kernel p phi = rawSum p phi := by
  have h := kernel_literal_split p hp hs (show 2 ≤ phi by linarith)
  simpa only [illegalSum_zero_tail p hp hs hphi,
    unitSum_zero_tail p hp hs (show 3 ≤ phi by linarith), add_zero] using h

theorem ninth_literal (p : SecondFunctionalParameters) :
    omega3XIntegralEnvelope p.kappa3 p.kappa1 =
      sSup ((fun phi : ℝ => ∫ t in 1/p.kappa1..1/p.kappa3,
        ∫ u in t..1/p.kappa3, ∫ v in u..1/p.kappa3,
          LiLiuPrereqBuchstab.buchstab ((phi-t-u-v)/u) / (t*u^2*v)) '' Ici 2) := rfl

end WuSource.SrcNine.Analytic
