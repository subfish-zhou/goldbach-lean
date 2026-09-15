import WR2PsiCostsZeroExtension

namespace WuPaper.R2PsiCosts
open Wu2008DoubleSieve Set MeasureTheory
open SecondFunctionalJointTail SecondFunctionalFourSevenths
open scoped BigOperators
noncomputable section

theorem D20_chain (p : SecondFunctionalParameters) (t : Fin 5 → ℝ) :
    t ∈ D20 p ↔ 1 / p.kappa2 ≤ t 0 ∧ t 0 ≤ 1 / p.kappa3 ∧
      1 / p.kappa3 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ t 4 ∧ t 4 ≤ 1 / p.s := by
  constructor
  · rintro ⟨ha, hb, hc, hm, hd⟩
    exact ⟨ha, hb, hc, hm (by decide), hm (by decide), hm (by decide), hd⟩
  · rintro ⟨ha, hb, hc, h12, h23, h34, hd⟩
    refine ⟨ha, hb, hc, ?_, hd⟩
    apply Fin.monotone_iff_le_succ.mpr
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨hb.trans hc, h12, h23, h34⟩

theorem D21_chain (p : SecondFunctionalParameters) (t : Fin 6 → ℝ) :
    t ∈ D21 p ↔ 1 / p.kappa3 ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧
      t 2 ≤ t 3 ∧ t 3 ≤ t 4 ∧ t 4 ≤ t 5 ∧ t 5 ≤ 1 / p.s := by
  constructor
  · rintro ⟨ha, hm, hb⟩
    exact ⟨ha, hm (by decide), hm (by decide), hm (by decide),
      hm (by decide), hm (by decide), hb⟩
  · rintro ⟨ha, h01, h12, h23, h34, h45, hb⟩
    refine ⟨ha, ?_, hb⟩
    apply Fin.monotone_iff_le_succ.mpr
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    exact ⟨h01, h12, h23, h34, h45⟩

theorem K9_bounds (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    0 ≤ K9 p phi ∧ K9 p phi ≤ 10000 * (1 / p.kappa3 - 1 / p.kappa1) ^ 3 :=
  omega3XIntegral_bounds (hs.trans hp.s_le_kappa3)
    (hp.kappa3_lt_kappa2.le.trans hp.kappa2_lt_kappa1.le)
    (hp.kappa1_le_S.trans hp.S_le_ten) hphi

theorem K9_bdd (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) : BddAbove (K9 p '' Ici 2) := by
  refine ⟨10000 * (1 / p.kappa3 - 1 / p.kappa1) ^ 3, ?_⟩
  rintro _ ⟨phi, hphi, rfl⟩
  exact (K9_bounds p hp hs hphi).2

theorem zero_K9_eq (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) {phi : ℝ} (hphi : 2 ≤ phi) :
    (∫ t in (1 / p.kappa1)..(1 / p.kappa3),
      ∫ u in t..(1 / p.kappa3), ∫ v in u..(1 / p.kappa3),
        zeroBuchstab ((phi - t - u - v) / u) / (t * u ^ 2 * v)) = K9 p phi := by
  obtain ⟨ha, hab, hbc, hce, hef, hf⟩ :=
    LowerTripleContinuous.mother_compact_parameters p hp hs
  have hlo : 1 / 10 ≤ 1 / p.kappa1 := ha.trans hab
  have hhi : 1 / p.kappa3 ≤ 1 / 2 := hef.trans hf
  have horder : 1 / p.kappa1 ≤ 1 / p.kappa3 := hbc.trans hce
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le horder] at ht
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht.2] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu.2] at hv
  have hu0 : 0 < u := by linarith [ht.1, hu.1]
  have harg : 1 ≤ (phi - t - u - v) / u := by
    apply (le_div_iff₀ hu0).2
    linarith [ht.2, hu.2, hv.2]
  simp only [zeroBuchstab, if_pos harg]

theorem originalI_nonnegative (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) :
    0 ≤ I9 p ∧ (∀ j, 0 ≤ lowerI p j) ∧ (∀ j, 0 ≤ fourI p j) ∧ 0 ≤ I20 p ∧ 0 ≤ I21 p := by
  exact ⟨(K9_bounds p hp hs (phi := 2) le_rfl).1.trans (le_phiSup (K9_bdd p hp hs) le_rfl),
    fun j => (lowerK_bounds p hp hs j 2).1.trans (le_phiSup (lowerK_bdd p hp hs j) le_rfl),
    fun j => (fourK_bounds p hp hs j 2).1.trans (le_phiSup (fourK_bdd p hp hs j) le_rfl),
    (K20_bounds p hp hs 2).1.trans (le_phiSup (K20_bdd p hp hs) le_rfl),
    (K21_bounds p hp hs 2).1.trans (le_phiSup (K21_bdd p hp hs) le_rfl)⟩

theorem originalCost_nonnegative (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) : 0 ≤ originalCost p := by
  obtain ⟨h9, hl, hf, h20, h21⟩ := originalI_nonnegative p hp hs
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg h9
    (Finset.sum_nonneg (fun j _ => hl j))) (Finset.sum_nonneg (fun j _ => hf j))) h20) h21

def existingCap : Fin 4 → ℝ :=
  Fin.cases Wu04CurveCost.costCap Wu04RemainingStrongCompleteCost.costCap

def existingPublication : Fin 4 → ℝ :=
  Fin.cases Wu04CurvePaid.publication Wu04RemainingCore.publication

theorem originalCost_paid_all (i : Fin 4) :
    originalCost (SecondFunctionalPositive.parameters i) ≤ existingCap i := by
  refine Fin.cases first_originalCost_paid (fun j => ?_) i
  exact remaining_originalCost_paid j

theorem fullPsi_published_all (i : Fin 4) :
    existingPublication i ≤ fullPsi (SecondFunctionalPositive.parameters i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change Wu04CurvePaid.publication ≤ fullPsi SecondFunctionalParameters.row1
    linarith only [first_fullPsi_lower, Wu04CurvePaid.slack_pos]
  · change Wu04RemainingCore.publication j ≤ fullPsi (Wu04RemainingCore.row j)
    linarith only [remaining_fullPsi_lower j, Wu04RemainingStrongPublication.slack_pos j]

theorem zeroPsi_published_all (i : Fin 4) :
    existingPublication i ≤ zeroPsi (SecondFunctionalPositive.parameters i) :=
  (fullPsi_published_all i).trans
    (fullPsi_le_zeroPsi _ (original_mother i) (original_s_ge_two i))

end
end WuPaper.R2PsiCosts
