import FeedbackProfiles

namespace ActualNineFeedback
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension
open scoped Interval BigOperators

/-- Only fixed parameter geometry; no gain or integral comparison is stored here. -/
def CoupledGeometry (p : SecondFunctionalParameters) : Prop :=
  MotherPair.AnalyticParameters p ∧ 3 ≤ p.kappa1 ∧
    2 ≤ p.S - p.S / p.s ∧ 2 ≤ p.S - p.S / p.kappa2 ∧ 2 ≤ p.S - p.S / p.kappa3

noncomputable def coupledBase (p : SecondFunctionalParameters) : ℝ :=
  wuUpperCoefficient p.s +
    (fourthRowClassicalJ p.s p.S + fourthRowClassicalJ p.kappa2 p.S +
      fourthRowClassicalJ p.kappa3 p.S -
      (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 +
        SecondFunctionalCoupledFeedback.classical p + 2 * coupledCostMass p)) / 5

noncomputable def coupledFeedback (p : SecondFunctionalParameters) (z : Fin 9 → ℝ) : ℝ :=
  (4 * eProfile (nineProfile z) p.S + eProfile (nineProfile z) p.kappa1 +
    profileJ z p.s p.S + profileJ z p.kappa2 p.S + profileJ z p.kappa3 p.S +
    densityMoment p z) / 5

theorem coupled_geometry_bounds {p : SecondFunctionalParameters} (hp : CoupledGeometry p) :
    2 ≤ p.s ∧ p.s ≤ p.S ∧ 2 ≤ p.kappa2 ∧ p.kappa2 ≤ p.S ∧
      2 ≤ p.kappa3 ∧ p.kappa3 ≤ p.S ∧ p.kappa1 ≤ 5 := by
  have hm := hp.1.mother
  have h3 := hm.s_le_kappa3
  have h2 := hm.kappa3_lt_kappa2.le
  have h1 := hm.kappa2_lt_kappa1.le
  have hS := hm.kappa1_le_S
  exact ⟨hp.1.two_lt_s.le, h3.trans (h2.trans (h1.trans hS)),
    hp.1.two_lt_s.le.trans (h3.trans h2), h1.trans hS,
    hp.1.two_lt_s.le.trans h3, h2.trans (h1.trans hS), hS.trans hp.1.S_le_five⟩

theorem coupledLoss_nonneg {p : SecondFunctionalParameters} (hp : CoupledGeometry p) :
    0 ≤ coupledLoss p := by
  have hg := coupled_geometry_bounds hp
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 5)
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply add_nonneg
  · exact (omega3XIntegralEnvelope_bounds hg.2.2.2.2.1
      (hp.1.mother.kappa3_lt_kappa2.le.trans hp.1.mother.kappa2_lt_kappa1.le)
      (hg.2.2.2.2.2.2.trans (by norm_num))).1
  · exact (SecondFunctionalCoupled.jointSup_bounds p hp.1.mother hp.1.two_lt_s.le).1

theorem coupledFeedback_nonneg {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) : 0 ≤ coupledFeedback p z := by
  have hg := coupled_geometry_bounds hp
  have he := (profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2
  have h0 := he p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := he p.kappa1 ⟨hp.2.1, hg.2.2.2.2.2.2⟩
  have hj0 := profileJ_nonneg hz hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_nonneg hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_nonneg hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hd := densityMoment_nonneg p hp.1 hz
  unfold coupledFeedback
  linarith

theorem coupledFeedback_expansion {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    (z : Fin 9 → ℝ) :
    coupledFeedback p z = ∑ k : Fin 9, coupledFeedback p (nodeBasis k) * z k := by
  have hg := coupled_geometry_bounds hp
  unfold coupledFeedback
  rw [eProfile_expansion z hp.1.three_le_S hp.1.S_le_five,
    eProfile_expansion z hp.2.1 hg.2.2.2.2.2.2,
    profileJ_expansion z hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1,
    profileJ_expansion z hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1,
    profileJ_expansion z hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.2.2.1 hp.2.2.2.2, densityMoment_expansion p hp.1 z,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The original genuine mother, its exact cost, three genuine J splits and the legal density. -/
theorem coupled_actual {p : SecondFunctionalParameters} (hp : CoupledGeometry p)
    {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    coupledBase p - deltaLoss δ * coupledLoss p + coupledFeedback p (actualNine δ) ≤
      wuImprovementLimit true δ p.s := by
  have hg := coupled_geometry_bounds hp
  have hh' : δ < 1 / 2 := by linarith
  have he := (actual_nine_extension hd hh).2.2.2
  have h0 := he p.S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
  have h1 := he p.kappa1 ⟨hp.2.1, hg.2.2.2.2.2.2⟩
  have hj0 := profileJ_le_actual hd hh hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1
  have hj2 := profileJ_le_actual hd hh hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.1 hp.2.2.2.1
  have hj3 := profileJ_le_actual hd hh hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
    hg.2.2.2.2.2.1 hp.2.2.2.2
  have hdens := densityMoment_le_actual p hp.1 hd hh
  have hsrc := SecondFunctionalCoupledFeedback.actual_limit p hp.1 hd hh
  have hcost := exact_cost_loss p hh
  unfold SecondFunctionalCoupledFeedback.gain at hsrc
  rw [SecondFunctionalSignedCore.J_split hd hh' hg.1 hg.2.1 hp.1.three_le_S
      hp.1.S_le_five hp.2.2.1,
    SecondFunctionalSignedCore.J_split hd hh' hg.2.2.1 hg.2.2.2.1 hp.1.three_le_S
      hp.1.S_le_five hp.2.2.2.1,
    SecondFunctionalSignedCore.J_split hd hh' hg.2.2.2.2.1 hg.2.2.2.2.2.1 hp.1.three_le_S
      hp.1.S_le_five hp.2.2.2.2] at hsrc
  unfold coupledBase coupledFeedback
  linarith only [hsrc, hcost, h0, h1, hj0, hj2, hj3, hdens]

noncomputable def firstFeedback (z : Fin 9 → ℝ) (s S : ℝ) : ℝ :=
  eProfile (nineProfile z) S + profileJ z s S / 2

theorem firstFeedback_expansion (z : Fin 9 → ℝ) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) :
    firstFeedback z s S = ∑ k : Fin 9, firstFeedback (nodeBasis k) s S * z k := by
  unfold firstFeedback
  rw [eProfile_expansion z hS hS5, profileJ_expansion z hs hS hS5 hsS hr,
    Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem firstFeedback_nonneg {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) {s S : ℝ}
    (hs : 2 ≤ s) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hsS : s ≤ S) (hr : 2 ≤ S - S / s) : 0 ≤ firstFeedback z s S := by
  exact add_nonneg ((profiles_nonneg (fun t _ => nineProfile_nonneg hz t)).2.2 S ⟨hS, hS5⟩)
    (div_nonneg (profileJ_nonneg hz hs hS hS5 hsS hr) (by norm_num))

theorem first_actual {δ s S : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    (hs : 2 ≤ s) (hs3 : s ≤ 3) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hr : 2 ≤ S - S / s) :
    firstFunctionalGainPsiOne s S - deltaLoss δ * omega3XIntegralEnvelope s S +
      firstFeedback (actualNine δ) s S ≤ wuImprovementLimit true δ s := by
  have hsrc := wuImprovementLimit_firstFunctionalGain_source hd hh hs hs3 hS hS5 hr
  have he := (actual_nine_extension hd hh).2.2.2 S ⟨hS, hS5⟩
  have hj := profileJ_le_actual hd hh hs hS hS5 (hs3.trans hS) hr
  change profileJ (actualNine δ) s S ≤
    ∫ u in (1 - 1 / s)..(1 - 1 / S), wuImprovementLimit false δ (S * u) / (u * (1 - u)) at hj
  unfold deltaLoss firstFeedback
  linarith only [hsrc, he, hj]

noncomputable def coupledRow (i : Fin 4) : SecondFunctionalParameters :=
  SecondFunctionalPositive.parameters i

theorem coupledRow_geometry (i : Fin 4) : CoupledGeometry (coupledRow i) :=
  ⟨SecondFunctionalPositive.parameters_analytic i, SecondFunctionalSignedCore.original_log_domains i⟩

noncomputable def firstNode (i : Fin 5) : ℝ := (26 + (i.val : ℝ)) / 10
noncomputable def firstS : Fin 5 → ℝ := ![358/100, 347/100, 334/100, 319/100, 3]

theorem first_geometry (i : Fin 5) :
    2 ≤ firstNode i ∧ firstNode i ≤ 3 ∧ 3 ≤ firstS i ∧ firstS i ≤ 5 ∧
      2 ≤ firstS i - firstS i / firstNode i := by
  revert i
  simp only [firstNode, firstS, Fin.forall_fin_succ, Fin.forall_fin_zero, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- A fixed functional on the nine original coordinates, with the terminal row retained. -/
noncomputable def feedback (z : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledFeedback (coupledRow ⟨i.val, h⟩) z
  else firstFeedback z (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

noncomputable def base (i : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledBase (coupledRow ⟨i.val, h⟩)
  else if i.val = 8 then 0 else
    firstFunctionalGainPsiOne (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

noncomputable def loss (i : Fin 9) : ℝ :=
  if h : i.val < 4 then coupledLoss (coupledRow ⟨i.val, h⟩)
  else if i.val = 8 then 0 else
    omega3XIntegralEnvelope (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩)

/-- The actual 9 by 9 matrix, not an identification with the printed matrix. -/
noncomputable def feedbackMatrix (i k : Fin 9) : ℝ := feedback (nodeBasis k) i

theorem feedback_expansion (z : Fin 9 → ℝ) (i : Fin 9) :
    feedback z i = ∑ k : Fin 9, feedbackMatrix i k * z k := by
  unfold feedbackMatrix feedback
  split_ifs with h
  · exact coupledFeedback_expansion (coupledRow_geometry _) z
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    exact firstFeedback_expansion z hg.1 hg.2.2.1 hg.2.2.2.1 (hg.2.1.trans hg.2.2.1) hg.2.2.2.2

theorem feedbackMatrix_nonneg (i k : Fin 9) : 0 ≤ feedbackMatrix i k := by
  unfold feedbackMatrix feedback
  split_ifs with h
  · exact coupledFeedback_nonneg (coupledRow_geometry _) (nodeBasis_nonneg k)
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    exact firstFeedback_nonneg (nodeBasis_nonneg k) hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2

theorem loss_nonneg (i : Fin 9) : 0 ≤ loss i := by
  unfold loss
  split_ifs with h he
  · exact coupledLoss_nonneg (coupledRow_geometry _)
  · exact le_rfl
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    exact (omega3XIntegralEnvelope_bounds hg.1 (hg.2.1.trans hg.2.2.1)
      (hg.2.2.2.1.trans (by norm_num))).1

theorem coupledRow_node (i : Fin 4) :
    (coupledRow i).s = upperNode ⟨i.val, by omega⟩ := by
  revert i
  simp only [coupledRow, SecondFunctionalPositive.parameters, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num [SecondFunctionalParameters.row1,
    SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
    SecondFunctionalParameters.row4, upperNode]

theorem actual_feedback {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) (i : Fin 9) :
    base i - deltaLoss δ * loss i + feedback (actualNine δ) i ≤ actualNine δ i := by
  unfold base loss feedback
  split_ifs with h he
  · have hsrc := coupled_actual (coupledRow_geometry ⟨i.val, h⟩) hd hh
    rw [coupledRow_node] at hsrc
    exact hsrc
  · have hi : i = (8 : Fin 9) := Fin.ext he
    subst i
    have hext := (actual_nine_extension hd hh).2.2.2 3 ⟨by norm_num, by norm_num⟩
    convert hext using 1 <;> norm_num [firstFeedback, profileJ, firstNode, firstS, actualNine, upperNode]
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hg := first_geometry j
    have hsrc := first_actual hd hh hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
    have hn : firstNode j = upperNode i := by
      dsimp [firstNode, upperNode, j]
      rw [Nat.cast_sub (by omega : 4 ≤ i.val)]
      norm_num
      ring
    change _ ≤ wuImprovementLimit true δ (upperNode i)
    rw [← hn]
    exact hsrc

/-- Fixed positive-delta feedback and the frozen 21 by 9 transfer, with no numerical premises. -/
theorem actual_nine_system {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10) :
    (∀ i k, 0 ≤ feedbackMatrix i k) ∧ (∀ i, 0 ≤ loss i) ∧
    (∀ i, 0 ≤ actualNine δ i) ∧
    (∀ i, base i - deltaLoss δ * loss i +
      ∑ k : Fin 9, feedbackMatrix i k * actualNine δ k ≤ actualNine δ i) ∧
    (∀ j : Fin 21, (∑ k : Fin 9, transferMatrix j k * actualNine δ k) ≤
      wuImprovementLimit false δ (rNode (j.val + 1))) := by
  refine ⟨feedbackMatrix_nonneg, loss_nonneg, actualNine_nonneg hd hh, ?_, actual_twentyone_matrix hd hh⟩
  intro i
  rw [← feedback_expansion]
  exact actual_feedback hd hh i

end ActualNineFeedback
