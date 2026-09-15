import NodeTransfer
import Wu04BypassCells

noncomputable section
namespace WuTarget.W02
open Real Set MeasureTheory NodeExtension
open scoped Interval BigOperators

def tailLeft (S : ℝ) (k : Fin 9) : ℝ := max (upperLeft k) (S - 2)

def tailIntegral (S : ℝ) (k : Fin 9) : ℝ :=
  if tailLeft S k ≤ upperNode k then
    ∫ t in tailLeft S k..upperNode k, log ((t + 1) / (S - 1)) / t
  else 0

def tailCell (S : ℝ) (k : Fin 9) : ℝ :=
  if tailLeft S k ≤ upperNode k then
    Wu04Bypass.cell S (tailLeft S k) (upperNode k)
  else 0

theorem logMoment_basis_eq {S : ℝ} (_hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    logMoment (nodeBasis k) S = tailIntegral S k := by
  have he (t : ℝ) :
      nineProfile (nodeBasis k) t / t * log ((t + 1) / (S - 1)) =
        (Ioc (upperLeft k) (upperNode k)).indicator
          (fun t => log ((t + 1) / (S - 1)) / t) t := by
    rw [nineProfile_basis]
    by_cases ht : t ∈ Ioc (upperLeft k) (upperNode k)
    · simp only [indicator_of_mem ht]
      ring
    · simp only [indicator_of_notMem ht, zero_div, zero_mul]
  have hs : Ioc (upperLeft k) (upperNode k) ∩ Ioc (S - 2) 3 =
      Ioc (tailLeft S k) (upperNode k) := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, tailLeft, max_lt_iff]
    constructor
    · rintro ⟨⟨hl, hu⟩, ⟨hlo, _⟩⟩
      exact ⟨⟨hl, hlo⟩, hu⟩
    · rintro ⟨⟨hl, hlo⟩, hu⟩
      exact ⟨⟨hl, hu⟩, ⟨hlo, hu.trans (upperNode_bounds k).2⟩⟩
  unfold logMoment
  simp_rw [he]
  rw [intervalIntegral.integral_of_le (by linarith : S - 2 ≤ 3),
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, hs]
  unfold tailIntegral
  split_ifs with hab
  · exact (intervalIntegral.integral_of_le hab).symm
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hab)]
    simp

theorem tailCell_nonneg {S : ℝ} (_hS : 3 ≤ S) (k : Fin 9) :
    0 ≤ tailCell S k := by
  unfold tailCell
  split_ifs with hab
  · have ha : S - 2 ≤ tailLeft S k := le_max_right _ _
    have hb : 0 < upperNode k := lt_of_lt_of_le (by norm_num) (upperNode_bounds k).1
    unfold Wu04Bypass.cell
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (by linarith)
    · positivity
  · exact le_rfl

theorem tailCell_le_logMoment {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    tailCell S k ≤ logMoment (nodeBasis k) S := by
  rw [logMoment_basis_eq hS hS5]
  unfold tailCell tailIntegral
  split_ifs with hab
  · exact Wu04Bypass.cell_le_integral hS (le_max_right _ _) hab
  · exact le_rfl

theorem logMoment_basis_nonneg {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    0 ≤ logMoment (nodeBasis k) S :=
  (tailCell_nonneg hS k).trans (tailCell_le_logMoment hS hS5 k)

theorem eProfile_basis_decomposition {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    eProfile (nineProfile (nodeBasis k)) S =
      aProfile (nineProfile (nodeBasis k)) * log (4 / (S - 1)) + tailIntegral S k := by
  change _ + logMoment (nodeBasis k) S = _
  rw [logMoment_basis_eq hS hS5]

theorem eProfile_basis_lower {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    aProfile (nineProfile (nodeBasis k)) * log (4 / (S - 1)) + tailCell S k ≤
      eProfile (nineProfile (nodeBasis k)) S :=
  add_le_add le_rfl (tailCell_le_logMoment hS hS5 k)

theorem tailCell_le_eProfile {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    tailCell S k ≤ eProfile (nineProfile (nodeBasis k)) S := by
  have ha := (profiles_nonneg (fun t _ => nineProfile_nonneg (nodeBasis_nonneg k) t)).1
  have hl : 0 ≤ log (4 / (S - 1)) :=
    log_nonneg ((one_le_div (by linarith : 0 < S - 1)).mpr (by linarith))
  exact (le_add_of_nonneg_left (mul_nonneg ha hl)).trans (eProfile_basis_lower hS hS5 k)

def logLower (a b : ℝ) : ℝ := (b - a) / b

theorem logLower_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ logLower a b :=
  div_nonneg (sub_nonneg.mpr hab) (ha.trans_le hab).le

theorem logLower_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logLower a b ≤ log (b / a) := by
  have hb := ha.trans_le hab
  have hh := log_le_sub_one_of_pos (div_pos ha hb)
  rw [log_div ha.ne' hb.ne'] at hh
  rw [log_div hb.ne' ha.ne']
  have he : logLower a b = 1 - a / b := by
    unfold logLower
    field_simp
  rw [he]
  linarith only [hh]

end WuTarget.W02
