import WR2ClassicalCKernel

noncomputable section
namespace WuPaper.ClassicalC
open Real

theorem left_bounds {u : ℝ} (hu : 2 ≤ u) (hu5 : u ≤ 5) :
    0 ≤ left u ∧ |left u| ≤ 2 ∧ |leftD1 u| ≤ 2 ∧ |leftD2 u| ≤ 2 := by
  have h0 : 0 < u := by linarith
  have h1 : 0 < u-1 := by linarith
  have hl0 : 0 ≤ log (u-1) := log_nonneg (by linarith)
  have hl3 : log (u-1) ≤ 3 := (log_le_sub_one_of_pos h1).trans (by linarith)
  have hL0 : 0 ≤ left u := div_nonneg hl0 h0.le
  have hL : left u ≤ (3:ℝ)/2 := by
    exact div_le_div₀ (by norm_num) hl3 (by norm_num) hu
  have ha0 : 0 ≤ 1/(u-1)/u := by positivity
  have ha : 1/(u-1)/u ≤ (1:ℝ)/2 := by
    calc
      _ ≤ 1/(1:ℝ)/2 := by gcongr; linarith
      _ = _ := by norm_num
  have hb0 : 0 ≤ log (u-1)/u^2 := by positivity
  have hb : log (u-1)/u^2 ≤ (3:ℝ)/4 := by
    apply div_le_div₀ (by norm_num) hl3 (by norm_num)
    nlinarith
  have hD1 : |leftD1 u| ≤ 2 := by
    unfold leftD1
    have hh := abs_sub (1/(u-1)/u) (log (u-1)/u^2)
    rw [abs_of_nonneg ha0,abs_of_nonneg hb0] at hh
    linarith
  have hc0 : 0 ≤ 1/(u-1)^2/u := by positivity
  have hc : 1/(u-1)^2/u ≤ (1:ℝ)/2 := by
    calc
      _ ≤ 1/(1:ℝ)^2/2 := by gcongr; linarith
      _ = _ := by norm_num
  have hd0 : 0 ≤ 2/(u-1)/u^2 := by positivity
  have hd : 2/(u-1)/u^2 ≤ (1:ℝ)/2 := by
    calc
      _ ≤ 2/(1:ℝ)/2^2 := by gcongr; linarith
      _ = _ := by norm_num
  have he0 : 0 ≤ 2*log (u-1)/u^3 := by positivity
  have he : 2*log (u-1)/u^3 ≤ (3:ℝ)/4 := by
    calc
      _ ≤ 2*(3:ℝ)/2^3 := by gcongr
      _ = _ := by norm_num
  have hD2 : |leftD2 u| ≤ 2 := by
    have hh : |-(1/(u-1)^2/u)-2/(u-1)/u^2+2*log (u-1)/u^3| ≤
        1/(u-1)^2/u+2/(u-1)/u^2+2*log (u-1)/u^3 := by
      calc
        _ ≤ |-(1/(u-1)^2/u)-2/(u-1)/u^2|+|2*log (u-1)/u^3| := abs_add_le _ _
        _ ≤ |-(1/(u-1)^2/u)|+|2/(u-1)/u^2|+|2*log (u-1)/u^3| :=
          add_le_add_left (abs_sub _ _) _
        _ = _ := by rw [abs_neg,abs_of_nonneg hc0,abs_of_nonneg hd0,abs_of_nonneg he0]
    unfold leftD2
    rw [show -1/(u-1)^2/u = -(1/(u-1)^2/u) by ring]
    linarith
  exact ⟨hL0,by rw [abs_of_nonneg hL0]; linarith,hD1,hD2⟩


theorem right_bounds {s u : ℝ} (hs : s ≤ 7) (hu : 2 ≤ u) (hus : u ≤ s-2) :
    0 ≤ right s u ∧ right s u ≤ 1 := by
  have hs0 : s-1 ≠ 0 := by linarith
  have hu0 : u+1 ≠ 0 := by linarith
  have hr1 : 1 ≤ (s-1)/(u+1) := (one_le_div (by linarith)).mpr (by linarith)
  have hr2 : (s-1)/(u+1) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [right,← log_div hs0 hu0]
  exact ⟨log_nonneg hr1,(log_le_sub_one_of_pos (by linarith : 0 < (s-1)/(u+1))).trans (by linarith)⟩

theorem kernelD2_bound {s u : ℝ} (hs : s ≤ 7) (hu : 2 ≤ u) (hus : u ≤ s-2) :
    |kernelD2 s u| ≤ 8 := by
  obtain ⟨hL0,hL,hD1,hD2⟩ := left_bounds hu (by linarith)
  obtain ⟨hR0,hR⟩ := right_bounds hs hu hus
  have hA : |leftD2 u*right s u| ≤ 2 := by
    rw [abs_mul,abs_of_nonneg hR0]
    have h := mul_le_mul hD2 hR hR0 (by norm_num : (0:ℝ) ≤ 2)
    norm_num at h
    exact h
  have hB : |2*leftD1 u/(u+1)| ≤ 4 := by
    rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos (by linarith : 0<u+1)]
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have hC : |left u/(u+1)^2| ≤ 2 := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos (by linarith : 0<u+1))]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<u+1))).mpr
    nlinarith
  unfold kernelD2
  calc
    _ ≤ |leftD2 u*right s u-2*leftD1 u/(u+1)|+|left u/(u+1)^2| := abs_add_le _ _
    _ ≤ |leftD2 u*right s u|+|2*leftD1 u/(u+1)|+|left u/(u+1)^2| :=
      add_le_add_left (abs_sub _ _) _
    _ ≤ 8 := by linarith

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.left_bounds

#print axioms WuPaper.ClassicalC.kernelD2_bound
