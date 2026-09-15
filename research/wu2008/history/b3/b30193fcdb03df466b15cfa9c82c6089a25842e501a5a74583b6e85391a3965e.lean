import R2PsiCostsRemaining

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail SecondFunctionalFourSevenths
open scoped BigOperators
noncomputable section

theorem phiSup_mono {f g : ℝ → ℝ} (hg : BddAbove (g '' Ici 2))
    (h : ∀ phi, 2 ≤ phi → f phi ≤ g phi) : phiSup f ≤ phiSup g :=
  phiSup_le (fun phi hphi => (h phi hphi).trans (le_phiSup hg hphi))

theorem zeroBuchstab_le_full (u : ℝ) : zeroBuchstab u ≤ LiLiuPrereqBuchstab.buchstab u := by
  unfold zeroBuchstab
  split_ifs
  · exact le_rfl
  · exact (buchstab_global_bounds u).1

theorem zeroIntegral_eq_masked {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    (∫ t in D, zeroWeight j phi t) =
      ∫ t in D, HighNonunitLegal.G j phi t * continuousDensity t :=
  setIntegral_congr_fun hD (fun _ ht => zeroWeight_eq_masked j phi (hsub ht))

theorem zeroWeight_integrable {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    IntegrableOn (zeroWeight j phi) D :=
  (HighNonunitLegal.weighted_integrable_on j phi hsub).congr_fun
    (fun _ ht => (zeroWeight_eq_masked j phi (hsub ht)).symm) hD

theorem zeroIntegral_le_full {n : ℕ} (j : Fin n) (phi : ℝ)
    {D : Set (Fin n → ℝ)} (hD : MeasurableSet D) (hsub : D ⊆ continuousCube n) :
    (∫ t in D, zeroWeight j phi t) ≤ ∫ t in D, fullWeight j phi t := by
  apply setIntegral_mono_on (zeroWeight_integrable j phi hD hsub)
    (fullWeight_integrable j phi hD hsub) hD
  intro t ht
  exact mul_le_mul_of_nonneg_right (zeroBuchstab_le_full _)
    (geometricWeight_nonneg j (hsub ht))

def zeroFourK (p : SecondFunctionalParameters) (j : Fin 4) (phi : ℝ) : ℝ :=
  ∫ t in fourDomain p j, zeroWeight 2 phi t

def zeroK20 (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  ∫ t in D20 p, zeroWeight 3 phi t

def zeroK21 (p : SecondFunctionalParameters) (phi : ℝ) : ℝ :=
  ∫ t in D21 p, zeroWeight 4 phi t

theorem zero_lower_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 6) {phi : ℝ} (hphi : 2 ≤ phi) :
    (∫ t in lowerDomain p j, zeroWeight 1 phi t) = lowerK p j phi := by
  rw [zeroIntegral_eq_masked 1 phi (lowerDomain_measurable p hp hs j)
    (lowerDomain_cube p hp hs j), lowerK_eq p hp hs j hphi, lowerDomain_eq p hp hs]
  rfl

theorem zeroFourK_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (j : Fin 4) (phi : ℝ) :
    zeroFourK p j phi =
      FourPrimeNonunit.legalK (1 / p.kappa1) (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi j := by
  rw [zeroFourK, zeroIntegral_eq_masked 2 phi (fourDomain_measurable p hp hs j)
    (fourDomain_cube p hp hs j), four_fixed_domain, fourDomain_eq p hp hs]

theorem zeroK20_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    zeroK20 p phi = HighNonunitLegal.K20 (1 / p.kappa2) (1 / p.kappa3) (1 / p.s) phi := by
  rw [zeroK20, zeroIntegral_eq_masked 3 phi (D20_measurable p) (D20_cube p hp hs),
    K20_fixed_domain]
  rfl

theorem zeroK21_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (phi : ℝ) :
    zeroK21 p phi = HighNonunitLegal.K21 (1 / p.kappa3) (1 / p.s) phi := by
  rw [zeroK21, zeroIntegral_eq_masked 4 phi (D21_measurable p) (D21_cube p hp hs),
    K21_fixed_domain]
  rfl

def zeroOriginalCost (p : SecondFunctionalParameters) : ℝ :=
  I9 p + (∑ j, lowerI p j) + (∑ j, phiSup (zeroFourK p j)) +
    phiSup (zeroK20 p) + phiSup (zeroK21 p)

theorem zeroOriginalCost_le_full (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) :
    zeroOriginalCost p ≤ originalCost p := by
  have hf (j : Fin 4) : phiSup (zeroFourK p j) ≤ fourI p j :=
    phiSup_mono (fourK_bdd p hp hs j) (fun phi _ =>
      zeroIntegral_le_full 2 phi (fourDomain_measurable p hp hs j) (fourDomain_cube p hp hs j))
  have h20 : phiSup (zeroK20 p) ≤ I20 p :=
    phiSup_mono (K20_bdd p hp hs) (fun phi _ =>
      zeroIntegral_le_full 3 phi (D20_measurable p) (D20_cube p hp hs))
  have h21 : phiSup (zeroK21 p) ≤ I21 p :=
    phiSup_mono (K21_bdd p hp hs) (fun phi _ =>
      zeroIntegral_le_full 4 phi (D21_measurable p) (D21_cube p hp hs))
  exact add_le_add (add_le_add (add_le_add le_rfl
    (Finset.sum_le_sum (fun j _ => hf j))) h20) h21

theorem first_zeroOriginalCost_paid :
    zeroOriginalCost SecondFunctionalParameters.row1 ≤ Wu04CurveCost.costCap :=
  (zeroOriginalCost_le_full _ (original_mother 0) (original_s_ge_two 0)).trans
    first_originalCost_paid

theorem remaining_zeroOriginalCost_paid (i : Fin 3) :
    zeroOriginalCost (Wu04RemainingCore.row i) ≤ Wu04RemainingStrongCompleteCost.costCap i :=
  (zeroOriginalCost_le_full _ (original_mother i.succ) (original_s_ge_two i.succ)).trans
    (remaining_originalCost_paid i)

def zeroPsi (p : SecondFunctionalParameters) : ℝ :=
  (Wu08OriginalPsiRecovery.classicalNumerator p - 2 * zeroOriginalCost p) / 5

theorem fullPsi_le_zeroPsi (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : fullPsi p ≤ zeroPsi p := by
  unfold fullPsi zeroPsi
  linarith only [zeroOriginalCost_le_full p hp hs]

end
end WuPaper.R2PsiCosts
