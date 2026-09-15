import WR2PsiCostsKernels

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail ActualNineFeedback NodeExtension
open scoped BigOperators
noncomputable section

def phiSup (f : ℝ → ℝ) : ℝ := sSup (f '' Ici 2)

theorem phiValues_nonempty (f : ℝ → ℝ) : (f '' Ici 2).Nonempty :=
  ⟨f 2, 2, (by simp : (2 : ℝ) ∈ Ici 2), rfl⟩

theorem phiSup_le {f : ℝ → ℝ} {c : ℝ} (h : ∀ phi, 2 ≤ phi → f phi ≤ c) :
    phiSup f ≤ c := by
  apply csSup_le (phiValues_nonempty f)
  rintro _ ⟨phi, hphi, rfl⟩
  exact h phi hphi

theorem le_phiSup {f : ℝ → ℝ} (hb : BddAbove (f '' Ici 2))
    {phi : ℝ} (hphi : 2 ≤ phi) : f phi ≤ phiSup f :=
  le_csSup hb ⟨phi, hphi, rfl⟩

theorem phiSup_congr {f g : ℝ → ℝ} (h : ∀ phi, 2 ≤ phi → f phi = g phi) :
    phiSup f = phiSup g := by
  unfold phiSup
  congr 1
  ext y
  constructor
  · rintro ⟨phi, hphi, rfl⟩
    exact ⟨phi, hphi, (h phi hphi).symm⟩
  · rintro ⟨phi, hphi, rfl⟩
    exact ⟨phi, hphi, h phi hphi⟩

theorem phiSup_sum_le {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hb : ∀ j, BddAbove (f j '' Ici 2)) :
    phiSup (fun phi => ∑ j, f j phi) ≤ ∑ j, phiSup (f j) := by
  apply phiSup_le
  intro phi hphi
  exact Finset.sum_le_sum (fun j _ => le_phiSup (hb j) hphi)

def I9 (p : SecondFunctionalParameters) : ℝ := phiSup (K9 p)
def lowerI (p : SecondFunctionalParameters) (j : Fin 6) : ℝ := phiSup (lowerK p j)
def fourI (p : SecondFunctionalParameters) (j : Fin 4) : ℝ := phiSup (fourK p j)
def I20 (p : SecondFunctionalParameters) : ℝ := phiSup (K20 p)
def I21 (p : SecondFunctionalParameters) : ℝ := phiSup (K21 p)

def originalCost (p : SecondFunctionalParameters) : ℝ :=
  I9 p + (∑ j, lowerI p j) + (∑ j, fourI p j) + I20 p + I21 p

def originalI (p : SecondFunctionalParameters) : Fin 13 → ℝ :=
  ![I9 p, lowerI p 0, lowerI p 1, lowerI p 2, lowerI p 3, lowerI p 4, lowerI p 5,
    fourI p 0, fourI p 1, fourI p 2, fourI p 3, I20 p, I21 p]

theorem originalCost_thirteen (p : SecondFunctionalParameters) :
    originalCost p = ∑ j : Fin 13, originalI p j := by
  simp [originalCost, originalI, Fin.sum_univ_succ]
  ring

theorem I9_eq (p : SecondFunctionalParameters) :
    I9 p = omega3XIntegralEnvelope p.kappa3 p.kappa1 := rfl

theorem lowerI_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) :
    lowerI p j = phiSup (fun phi => LowerTripleContinuous.K
      (1 / p.S) (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) j phi) :=
  phiSup_congr (fun _ hphi => lowerK_eq p hp hs j hphi)

theorem fourI_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) :
    fourI p j = phiSup (fun phi =>
      FourPrimeNonunit.legalK (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3)
        (1 / p.s) phi j + missingMass 2 (fourDomain p j) phi) :=
  phiSup_congr (fun phi _ => fourK_split p hp hs j phi)

theorem I20_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    I20 p = phiSup (fun phi =>
      HighNonunitLegal.K20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi +
        missingMass 3 (D20 p) phi) :=
  phiSup_congr (fun phi _ => K20_split p hp hs phi)

theorem I21_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    I21 p = phiSup (fun phi =>
      HighNonunitLegal.K21 (1 / p.kappa3) (1 / p.s) phi + missingMass 4 (D21 p) phi) :=
  phiSup_congr (fun phi _ => K21_split p hp hs phi)

theorem lowerK_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) (phi : ℝ) :
    0 ≤ lowerK p j phi ∧ lowerK p j phi ≤ lowerMass p j := by
  have h := fullIntegral_bounds 1 phi (lowerDomain_measurable p hp hs j)
    (lowerDomain_cube p hp hs j)
  simpa only [lowerK, lowerDomain_eq p hp hs, lowerMass] using h

theorem fourK_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) (phi : ℝ) :
    0 ≤ fourK p j phi ∧ fourK p j phi ≤ fourMass p j := by
  have h := fullIntegral_bounds 2 phi (fourDomain_measurable p hp hs j)
    (fourDomain_cube p hp hs j)
  simpa only [fourK, fourDomain_eq p hp hs, fourMass] using h

theorem K20_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    0 ≤ K20 p phi ∧ K20 p phi ≤ highMass20 p :=
  fullIntegral_bounds 3 phi (D20_measurable p) (D20_cube p hp hs)

theorem K21_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    0 ≤ K21 p phi ∧ K21 p phi ≤ highMass21 p :=
  fullIntegral_bounds 4 phi (D21_measurable p) (D21_cube p hp hs)

theorem lowerK_bdd (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) : BddAbove (lowerK p j '' Ici 2) := by
  refine ⟨lowerMass p j, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (lowerK_bounds p hp hs j phi).2

theorem fourK_bdd (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) : BddAbove (fourK p j '' Ici 2) := by
  refine ⟨fourMass p j, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (fourK_bounds p hp hs j phi).2

theorem K20_bdd (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : BddAbove (K20 p '' Ici 2) := by
  refine ⟨highMass20 p, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (K20_bounds p hp hs phi).2

theorem K21_bdd (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : BddAbove (K21 p '' Ici 2) := by
  refine ⟨highMass21 p, ?_⟩
  rintro _ ⟨phi, _, rfl⟩
  exact (K21_bounds p hp hs phi).2

def remainingKernel (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j, lowerK p j phi) + (∑ j, fourK p j phi) + K20 p phi + K21 p phi

def unitKernel (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  HighUnit.J20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi +
    HighUnit.J21 (1 / p.kappa3) (1 / p.s) phi

def missingKernel (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  (∑ j, missingMass 2 (fourDomain p j) phi) +
    missingMass 3 (D20 p) phi + missingMass 4 (D21 p) phi

theorem remainingKernel_identity (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    remainingKernel p phi + unitKernel p phi =
      SecondFunctionalCoupled.kernel p phi + missingKernel p phi := by
  unfold remainingKernel unitKernel missingKernel SecondFunctionalCoupled.kernel
  simp_rw [lowerK_eq p hp hs _ hphi, fourK_split p hp hs, K20_split p hp hs,
    K21_split p hp hs, Finset.sum_add_distrib]
  ring

def separationGap (p : SecondFunctionalParameters) : ℝ :=
  (∑ j, lowerI p j) + (∑ j, fourI p j) + I20 p + I21 p -
    phiSup (remainingKernel p)

theorem separationGap_nonneg (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : 0 ≤ separationGap p := by
  apply sub_nonneg.mpr
  apply phiSup_le
  intro phi hphi
  have hl := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 6))) =>
    le_phiSup (lowerK_bdd p hp hs j) hphi)
  have hf := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
    le_phiSup (fourK_bdd p hp hs j) hphi)
  exact add_le_add (add_le_add (add_le_add hl hf)
    (le_phiSup (K20_bdd p hp hs) hphi)) (le_phiSup (K21_bdd p hp hs) hphi)

theorem originalCost_exact_coupled (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    originalCost p = coupledCostMass p + separationGap p +
      (phiSup (fun phi => SecondFunctionalCoupled.kernel p phi +
        missingKernel p phi - unitKernel p phi) - SecondFunctionalCoupled.jointSup p) := by
  have he : phiSup (remainingKernel p) = phiSup (fun phi =>
      SecondFunctionalCoupled.kernel p phi + missingKernel p phi - unitKernel p phi) := by
    apply phiSup_congr
    intro phi hphi
    linarith only [remainingKernel_identity p hp hs hphi]
  unfold originalCost separationGap coupledCostMass
  rw [I9_eq, he]
  ring

end
end WuPaper.R2PsiCosts
