import W05JRational

noncomputable section
namespace WuTarget.W05
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped BigOperators

def assembleJ (c : ℝ → ℝ → Fin 9 → ℝ) (i k : Fin 9) : ℝ :=
  if h : i.val < 4 then
    (c (coupledRow ⟨i.val, h⟩).s (coupledRow ⟨i.val, h⟩).S k +
      c (coupledRow ⟨i.val, h⟩).kappa2 (coupledRow ⟨i.val, h⟩).S k +
      c (coupledRow ⟨i.val, h⟩).kappa3 (coupledRow ⟨i.val, h⟩).S k) / 5
  else c (firstNode ⟨i.val - 4, by omega⟩) (firstS ⟨i.val - 4, by omega⟩) k / 2

def jMatrix : Fin 9 → Fin 9 → ℝ := assembleJ jCoefficient
def rationalJMatrix : Fin 9 → Fin 9 → ℝ := assembleJ rationalJCoefficient

def jSigmaWeight (i : Fin 9) : ℝ :=
  assembleJ (fun s S _ => log ((S - 1) / (s - 1))) i 0

def otherFeedback (z : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if h : i.val < 4 then
    (4 * eProfile (nineProfile z) (coupledRow ⟨i.val, h⟩).S +
      eProfile (nineProfile z) (coupledRow ⟨i.val, h⟩).kappa1 +
      densityMoment (coupledRow ⟨i.val, h⟩) z) / 5
  else eProfile (nineProfile z) (firstS ⟨i.val - 4, by omega⟩)

theorem assembleJ_apply (c : ℝ → ℝ → Fin 9 → ℝ) (z : Fin 9 → ℝ) (i : Fin 9) :
    (∑ k : Fin 9, assembleJ c i k * z k) =
      if h : i.val < 4 then
        ((∑ k : Fin 9, c (coupledRow ⟨i.val, h⟩).s (coupledRow ⟨i.val, h⟩).S k * z k) +
          (∑ k : Fin 9, c (coupledRow ⟨i.val, h⟩).kappa2 (coupledRow ⟨i.val, h⟩).S k * z k) +
          (∑ k : Fin 9, c (coupledRow ⟨i.val, h⟩).kappa3 (coupledRow ⟨i.val, h⟩).S k * z k)) / 5
      else (∑ k : Fin 9, c (firstNode ⟨i.val - 4, by omega⟩)
        (firstS ⟨i.val - 4, by omega⟩) k * z k) / 2 := by
  unfold assembleJ
  split_ifs with h <;>
    simp only [add_mul, div_mul_eq_mul_div, ← Finset.sum_div, Finset.sum_add_distrib]

theorem assembleJ_mono {c d : ℝ → ℝ → Fin 9 → ℝ}
    (hcd : ∀ {s S : ℝ}, 2 ≤ s → 3 ≤ S → S ≤ 5 → s ≤ S →
      2 ≤ S - S / s → ∀ k, c s S k ≤ d s S k) (i k : Fin 9) :
    assembleJ c i k ≤ assembleJ d i k := by
  unfold assembleJ
  split_ifs with h
  · have hp := coupledRow_geometry ⟨i.val, h⟩
    have hg := coupled_geometry_bounds hp
    exact div_le_div_of_nonneg_right
      (add_le_add (add_le_add
        (hcd hg.1 hp.1.three_le_S hp.1.S_le_five hg.2.1 hp.2.2.1 k)
        (hcd hg.2.2.1 hp.1.three_le_S hp.1.S_le_five hg.2.2.2.1 hp.2.2.2.1 k))
        (hcd hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
          hg.2.2.2.2.2.1 hp.2.2.2.2 k)) (by norm_num)
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    exact div_le_div_of_nonneg_right
      (hcd hg.1 hg.2.2.1 hg.2.2.2.1 (hg.2.1.trans hg.2.2.1) hg.2.2.2.2 k)
      (by norm_num)

theorem assembleJ_nonneg {c : ℝ → ℝ → Fin 9 → ℝ}
    (hc : ∀ {s S : ℝ}, 2 ≤ s → 3 ≤ S → S ≤ 5 → s ≤ S →
      2 ≤ S - S / s → ∀ k, 0 ≤ c s S k) (i k : Fin 9) :
    0 ≤ assembleJ c i k := by
  have h := assembleJ_mono (c := fun _ _ _ => 0) hc i k
  have he : assembleJ (fun _ _ _ => 0) i k = 0 := by
    unfold assembleJ
    split_ifs <;> norm_num
  simpa only [he] using h

theorem rationalJMatrix_le (i k : Fin 9) : rationalJMatrix i k ≤ jMatrix i k :=
  assembleJ_mono rationalJCoefficient_le i k

theorem rationalJMatrix_nonneg (i k : Fin 9) : 0 ≤ rationalJMatrix i k :=
  assembleJ_nonneg rationalJCoefficient_nonneg i k

theorem jMatrix_nonneg (i k : Fin 9) : 0 ≤ jMatrix i k :=
  assembleJ_nonneg jCoefficient_nonneg i k

theorem jSigmaWeight_nonneg (i : Fin 9) : 0 ≤ jSigmaWeight i := by
  apply assembleJ_nonneg
  intro s S hs _ _ hsS _ _
  exact log_nonneg ((one_le_div (by linarith : 0 < s - 1)).mpr (by linarith))

/-- E, density and the unpaid Sigma coefficient remain outside the W05 tail block. -/
theorem feedback_separated_payment {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    otherFeedback z i + aProfile (nineProfile z) * jSigmaWeight i +
      ∑ k : Fin 9, jMatrix i k * z k ≤ feedback z i := by
  unfold jMatrix
  rw [assembleJ_apply]
  unfold otherFeedback jSigmaWeight assembleJ feedback
  split_ifs with h
  · have hp := coupledRow_geometry ⟨i.val, h⟩
    have hg := coupled_geometry_bounds hp
    have h0 := jCoefficients_paid hz hg.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.1 hp.2.2.1
    have h2 := jCoefficients_paid hz hg.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.1 hp.2.2.2.1
    have h3 := jCoefficients_paid hz hg.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five
      hg.2.2.2.2.2.1 hp.2.2.2.2
    unfold coupledFeedback
    linarith only [h0, h2, h3]
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    have hj := jCoefficients_paid hz hg.1 hg.2.2.1 hg.2.2.2.1
      (hg.2.1.trans hg.2.2.1) hg.2.2.2.2
    unfold firstFeedback
    linarith only [hj]

theorem matrix_separated_payment (i k : Fin 9) :
    otherFeedback (nodeBasis k) i + aProfile (nineProfile (nodeBasis k)) * jSigmaWeight i +
      jMatrix i k ≤ feedbackMatrix i k := by
  have h := feedback_separated_payment (nodeBasis_nonneg k) i
  classical
  simpa [nodeBasis, feedbackMatrix] using h

theorem elementary_le_other (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k ≤ otherFeedback (nodeBasis k) i := by
  unfold Wu04Bypass.elementaryMatrix otherFeedback
  split_ifs with h
  · have hp := coupledRow_geometry ⟨i.val, h⟩
    have he := Wu04Bypass.cells_le_eProfile (nodeBasis_nonneg k) hp.2.1
      (Wu04Bypass.coupled_kappa_cell ⟨i.val, h⟩)
    rw [Wu04Bypass.cells_basis] at he
    have heS := (profiles_nonneg (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)).2.2
      (coupledRow ⟨i.val, h⟩).S ⟨hp.1.three_le_S, hp.1.S_le_five⟩
    have hd := densityMoment_nonneg (coupledRow ⟨i.val, h⟩) hp.1 (nodeBasis_nonneg k)
    linarith only [he, heS, hd]
  · have hg := first_geometry (⟨i.val - 4, by omega⟩ : Fin 5)
    have he := Wu04Bypass.cells_le_eProfile (nodeBasis_nonneg k) hg.2.2.1
      (Wu04Bypass.first_cell ⟨i.val - 4, by omega⟩)
    simpa only [Wu04Bypass.cells_basis] using he

theorem elementary_add_jMatrix_le (i k : Fin 9) :
    Wu04Bypass.elementaryMatrix i k + jMatrix i k ≤ feedbackMatrix i k := by
  have h := matrix_separated_payment i k
  have he := elementary_le_other i k
  have ha := (profiles_nonneg (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)).1
  have hs := mul_nonneg ha (jSigmaWeight_nonneg i)
  linarith only [h, he, hs]

theorem baselineM_le_elementary (i k : Fin 9) :
    Wu04Bypass.M i k ≤ Wu04Bypass.elementaryMatrix i k := by
  fin_cases i
  · exact Wu04Bypass.matrix_row0 k
  · exact Wu04Bypass.matrix_row1 k
  · exact Wu04Bypass.matrix_row2 k
  · exact Wu04Bypass.matrix_row3 k
  · exact Wu04Bypass.matrix_row4 k
  · exact Wu04Bypass.matrix_row5 k
  · exact Wu04Bypass.matrix_row6 k
  · exact Wu04Bypass.matrix_row7 k
  · exact Wu04Bypass.matrix_row8 k

def paidMatrix (i k : Fin 9) : ℝ := Wu04Bypass.M i k + rationalJMatrix i k

theorem paidMatrix_le (i k : Fin 9) : paidMatrix i k ≤ feedbackMatrix i k :=
  (add_le_add (baselineM_le_elementary i k) (rationalJMatrix_le i k)).trans
    (elementary_add_jMatrix_le i k)

theorem paidMatrix_preserves_baseline (i k : Fin 9) : Wu04Bypass.M i k ≤ paidMatrix i k :=
  le_add_of_nonneg_right (rationalJMatrix_nonneg i k)

theorem paid_feedback {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (i : Fin 9) :
    matrixApply paidMatrix z i ≤ feedback z i := by
  rw [feedback_expansion]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (paidMatrix_le i k) (hz k))

theorem paid_actual {δ : ℝ} (hd : 0 < δ) (hh : δ ≤ 1 / 10)
    {z : Fin 9 → ℝ} (hz : ∀ k, 0 ≤ z k) (hza : ∀ k, z k ≤ actualNine δ k) (i : Fin 9) :
    base i - deltaLoss δ * loss i + matrixApply paidMatrix z i ≤ actualNine δ i := by
  have hm := matrixApply_mono feedbackMatrix_nonneg hza i
  have hp := paid_feedback hz i
  rw [feedback_expansion] at hp
  have ha := actual_feedback hd hh i
  rw [feedback_expansion] at ha
  exact (add_le_add le_rfl (hp.trans hm)).trans ha

theorem v8_paid_actual : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d → ∀ i : Fin 9,
      base i - deltaLoss δ * loss i + matrixApply paidMatrix Wu04Bypass.v8 i ≤
        actualNine δ i := by
  obtain ⟨d, hd, hcap, hx⟩ := Wu04Bypass.new_nine_actual
  refine ⟨d, hd, hcap, ?_⟩
  intro δ hδ hr i
  exact paid_actual hδ (hr.trans hcap) (fun k => (Wu04Bypass.new_vector_positive k).le)
    (hx δ hδ hr) i

theorem terminal_jMatrix_zero (k : Fin 9) : jMatrix 8 k = 0 := by
  norm_num [jMatrix, assembleJ, firstNode, firstS, terminal_coefficient_zero]

theorem terminal_rationalJMatrix_zero (k : Fin 9) : rationalJMatrix 8 k = 0 := by
  norm_num [rationalJMatrix, assembleJ, firstNode, firstS, rational_terminal_zero]

end WuTarget.W05
