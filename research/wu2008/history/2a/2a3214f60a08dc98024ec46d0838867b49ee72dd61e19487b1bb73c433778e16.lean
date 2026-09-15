import SrcFourFineProfile

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve Wu08OriginalFourWeights
open FourRoughClosedMass WuTarget.E10FourMajor

namespace WuSource.SrcFour

def tailAmount : ℝ := 8*(∫ x in outerCut..beta, profile x)
def tailLogCap : ℝ := SharpLogRecurrence.upperLog (beta/outerCut)
def tailCap : ℝ :=
  8*∑ i : Fin 5,
    (coefA i*tailLogCap^(i.val+3)/(i.val+3 : ℝ)+
      coefB i*tailLogCap^(i.val+4)/(i.val+4 : ℝ))
def fineCap (c : ℝ) : ℝ := scale c*pairCap+(1-scale c)*tailCap

theorem outerCut_pos : 0 < outerCut := by
  linarith only [geometry.2.1]

theorem tail_log_bounds :
    0 ≤ log beta-log outerCut ∧ log beta-log outerCut ≤ tailLogCap := by
  have hd := outerCut_pos
  have hb := hd.trans geometry.2.2.1
  have hu := SharpLogRecurrence.log_upper
    ((le_div_iff₀ hd).mpr (by simpa using geometry.2.2.1.le))
  rw [log_div hb.ne' hd.ne'] at hu
  exact ⟨sub_nonneg.mpr (log_le_log hd geometry.2.2.1.le),hu⟩

theorem tail_exact :
    tailAmount =
      8*∑ i : Fin 5,
        (coefA i*(log beta-log outerCut)^(i.val+3)/(i.val+3 : ℝ)+
          coefB i*(log beta-log outerCut)^(i.val+4)/(i.val+4 : ℝ)) := by
  unfold tailAmount
  rw [profile_integral outerCut_pos geometry.2.2.1.le]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi (n : ℕ) :
      (∫ x in outerCut..beta, WuTarget.W13.tail n x) =
        (log beta-log outerCut)^(n+1)/((n : ℝ)+1) := by
    simpa only [WuTarget.W13.tail,one_mul] using
      ClassicalLogFourBounds.integral_log_tail (C := (1 : ℝ))
        outerCut_pos geometry.2.2.1.le n
  rw [hi,hi]
  norm_num only [Nat.cast_add,Nat.cast_ofNat]
  rw [show i.val+2+1 = i.val+3 by omega,show i.val+3+1 = i.val+4 by omega]
  ring

theorem tail_upper : tailAmount ≤ tailCap := by
  rw [tail_exact]
  unfold tailCap
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  have hp (n : ℕ) := pow_le_pow_left₀ tail_log_bounds.1 tail_log_bounds.2 n
  exact add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hp (i.val+3)) (coefficients_pos i).1.le) (by positivity))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hp (i.val+4)) (coefficients_pos i).2.le) (by positivity))

theorem original_pair_split {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c) :
    original10+original11 ≤
      scale c*(∑ i : Fin 5, momentTerm i)+(1-scale c)*tailAmount := by
  have ha := geometry.2.2.2.1
  have hsmall : alpha ≤ WuTarget.W13.cut := by
    exact geometry.1.le
  have hmiddle : WuTarget.W13.cut ≤ outerCut := geometry.2.1.le
  have hlarge : outerCut ≤ beta := geometry.2.2.1.le
  have ho : Continuous (fun x => regularOuter10 x+regularOuter11 x) :=
    regularOuter10_continuous.add regularOuter11_continuous
  have hws := weighted_integrable ho
  have his := intervalIntegral.integral_mono_on hsmall hws
    (weighted_profile_integrable.const_mul (scale c)) (fun x hx => by
      have hden : 0 ≤ 1-x := by
        have hxcut : x ≤ (1/10 : ℝ) := hx.2
        linarith only [hxcut]
      have hf := div_le_div_of_nonneg_right
        (outer_fine hc0 hc ⟨hx.1,hx.2.trans hmiddle⟩) hden
      simpa only [mul_div_assoc] using hf)
  have him := intervalIntegral.integral_mono_on hmiddle
    (ho.intervalIntegrable (μ := volume) WuTarget.W13.cut outerCut)
    ((profile_integrable (by norm_num [WuTarget.W13.cut]) hmiddle).const_mul (scale c))
    (fun x hx => outer_fine hc0 hc ⟨hsmall.trans hx.1,hx.2⟩)
  have hit := intervalIntegral.integral_mono_on hlarge
    (ho.intervalIntegrable (μ := volume) outerCut beta)
    (profile_integrable outerCut_pos hlarge)
    (fun x hx => outer_pair_upper ⟨hsmall.trans (hmiddle.trans hx.1),hx.2⟩)
  have hoa := intervalIntegral.integral_add_adjacent_intervals
    (ho.intervalIntegrable (μ := volume) WuTarget.W13.cut outerCut)
    (ho.intervalIntegrable (μ := volume) outerCut beta)
  have hpa := intervalIntegral.integral_add_adjacent_intervals
    (profile_integrable (by norm_num [WuTarget.W13.cut]) hmiddle)
    (profile_integrable outerCut_pos hlarge)
  rw [intervalIntegral.integral_const_mul] at his him
  have hs10 := weighted_integrable regularOuter10_continuous
  have hs11 := weighted_integrable regularOuter11_continuous
  have hl10 := regularOuter10_continuous.intervalIntegrable (μ := volume)
    WuTarget.W13.cut beta
  have hl11 := regularOuter11_continuous.intervalIntegrable (μ := volume)
    WuTarget.W13.cut beta
  simp_rw [add_div] at his
  dsimp only [WuTarget.W13.cut] at his
  rw [intervalIntegral.integral_add hs10 hs11] at his
  rw [intervalIntegral.integral_add hl10 hl11] at hoa
  rw [← weighted_amount_identity]
  rw [← hpa]
  unfold original10 original11 original tailAmount
  dsimp only [WuTarget.W13.cut] at his him hit hoa hpa ⊢
  linarith only [his,him,hit,hoa]

theorem original_pair_fineCap {c : ℝ} (hc0 : 0 ≤ c) (hc4 : c ≤ (4/7 : ℝ))
    (hc : ∀ u : ℝ, (17/5 : ℝ) ≤ u → LiLiuPrereqBuchstab.buchstab u ≤ c) :
    original10+original11 ≤ fineCap c := by
  have hs0 : 0 ≤ scale c := by unfold scale; positivity
  have hs1 : 0 ≤ 1-scale c := by unfold scale; linarith only [hc4]
  have hm : (∑ i : Fin 5, momentTerm i) ≤ pairCap :=
    Finset.sum_le_sum (fun i _ => momentTerm_upper i)
  exact (original_pair_split hc0 hc).trans
    (add_le_add (mul_le_mul_of_nonneg_left hm hs0)
      (mul_le_mul_of_nonneg_left tail_upper hs1))

#check @tail_exact
#check @tail_upper
#check @original_pair_split
#check @original_pair_fineCap
#print axioms tail_exact
#print axioms tail_upper
#print axioms original_pair_split
#print axioms original_pair_fineCap
end WuSource.SrcFour
