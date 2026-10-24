import WR2ClassicalLogSplit
import U8SymbolicSmallGain

noncomputable section
namespace WuPaper.ClassicalEighthCorrection
open Real Set MeasureTheory
open scoped Interval

abbrev a : ℝ := OriginalU8.SymbolicSmallGain.a
abbrev b : ℝ := OriginalU8.SymbolicSmallGain.b

def gain (t : ℝ) : ℝ := (b-t)*log (2-3*t)/(t*(1-t)^2)
def cellCoefficient (l r : ℝ) : ℝ :=
  WuSource.SrcFourEnclosure.logLo (2-3*r)/(r*(1-l)^2)
def cellPayment (l r : ℝ) : ℝ := (r-l)*(b-(l+r)/2)*cellCoefficient l r

/-- Retain the moving numerator; only the logarithm and denominator are frozen. -/
theorem cell_point_lower {l r t : ℝ} (ha : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b)
    (ht : t ∈ Icc l r) : cellCoefficient l r*(b-t) ≤ gain t := by
  have ha0 : (0:ℝ) < a := by norm_num [a,OriginalU8.SymbolicSmallGain.a]
  have hb1 : b < (1:ℝ) := by norm_num [b,OriginalU8.SymbolicSmallGain.b]
  have ht0 : 0 < t := ha0.trans_le (ha.trans ht.1)
  have hr0 : 0 < r := ht0.trans_le ht.2
  have hl1 : 0 < 1-l := by linarith
  have ht1 : 0 < 1-t := by linarith [ht.2]
  have hbt : 0 ≤ b-t := by linarith [ht.2]
  have harg : 1 ≤ 2-3*r := by
    dsimp [b,OriginalU8.SymbolicSmallGain.b] at hrb
    linarith
  obtain ⟨hlo,hl,_⟩ := WuSource.SrcFourEnclosure.log_bounds harg
  have hlog : WuSource.SrcFourEnclosure.logLo (2-3*r) ≤ log (2-3*t) :=
    hl.trans (log_le_log (by linarith) (by linarith [ht.2]))
  have hsq : (1-t)^2 ≤ (1-l)^2 := pow_le_pow_left₀ ht1.le (by linarith [ht.1]) 2
  have hden : t*(1-t)^2 ≤ r*(1-l)^2 :=
    mul_le_mul ht.2 hsq (sq_nonneg _) hr0.le
  have hh := div_le_div₀ (hlo.trans hlog) hlog (mul_pos ht0 (sq_pos_of_pos ht1)) hden
  have hm := mul_le_mul_of_nonneg_right hh hbt
  calc
    cellCoefficient l r*(b-t) ≤ log (2-3*t)/(t*(1-t)^2)*(b-t) := hm
    _ = gain t := by unfold gain; ring

theorem affine_integral (l r c : ℝ) :
    (∫ t in l..r, c*(b-t)) = (r-l)*(b-(l+r)/2)*c := by
  let P : ℝ → ℝ := fun t => c*(b*t-t^2/2)
  have hd (t : ℝ) : HasDerivAt P (c*(b-t)) t := by
    have h := (((hasDerivAt_id t).const_mul b).sub (((hasDerivAt_id t).pow 2).div_const 2)).const_mul c
    change HasDerivAt P _ t at h
    apply h.congr_deriv
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => c*(b-t))).intervalIntegrable l r)]
  dsimp [P]
  ring

theorem gain_integrable {l r : ℝ} (ha : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) :
    IntervalIntegrable gain volume l r := by
  unfold gain
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    rw [uIcc_of_le hlr] at ht
    have hb : b = (1:ℝ)/10 := rfl
    linarith [ht.2]
  · fun_prop
  · intro t ht
    rw [uIcc_of_le hlr] at ht
    have ha0 : (0:ℝ) < a := by norm_num [a,OriginalU8.SymbolicSmallGain.a]
    have hb : b = (1:ℝ)/10 := rfl
    exact (mul_pos (by linarith [ht.1]) (sq_pos_of_pos (by linarith [ht.2]))).ne'

theorem cell_lower {l r : ℝ} (ha : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) :
    cellPayment l r ≤ ∫ t in l..r, gain t := by
  have hf := gain_integrable ha hlr hrb
  unfold cellPayment
  rw [← affine_integral]
  exact intervalIntegral.integral_mono_on hlr
    ((by fun_prop : Continuous (fun t : ℝ => cellCoefficient l r*(b-t))).intervalIntegrable l r)
    hf (fun t ht => cell_point_lower ha hlr hrb ht)

/-- Sum certified affine cell payments over any partition of the small interval. -/
theorem panels_lower {n : ℕ} {grid : ℕ → ℝ} {q : ℕ → ℝ}
    (h0 : grid 0 = a) (hn : grid n = b)
    (hstep : ∀ i < n, grid i ≤ grid (i+1))
    (hbounds : ∀ i ≤ n, grid i ∈ Icc a b)
    (hq : ∀ i < n, q i ≤ cellPayment (grid i) (grid (i+1))) :
    (∑ i ∈ Finset.range n, q i) ≤ ∫ t in a..b, gain t := by
  have hi (i : ℕ) (hin : i < n) : IntervalIntegrable gain volume (grid i) (grid (i+1)) :=
    gain_integrable (hbounds i (by omega)).1 (hstep i hin) (hbounds (i+1) (by omega)).2
  rw [← h0,← hn,← intervalIntegral.sum_integral_adjacent_intervals hi]
  apply Finset.sum_le_sum
  intro i him
  have hin := Finset.mem_range.mp him
  exact (hq i hin).trans (cell_lower (hbounds i (by omega)).1 (hstep i hin)
    (hbounds (i+1) (by omega)).2)

end WuPaper.ClassicalEighthCorrection
#print axioms WuPaper.ClassicalEighthCorrection.cell_lower

#print axioms WuPaper.ClassicalEighthCorrection.panels_lower
