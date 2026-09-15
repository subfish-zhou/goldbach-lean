import MathlibNt.Wu2008DoubleSieve.MotherPairGainBounds

/-! General four-term inverse coordinates and exact closed legal sections.
No fixed parameter row is used. -/
namespace Wu2008DoubleSieve.MotherPair
open Set Real MeasureTheory
open scoped Classical Topology Interval

noncomputable def feedbackJac (p : SecondFunctionalParameters) : Term → ℝ → ℝ
  | .gammaFive, _ => 1/p.S
  | .gammaSix, _ => 1/p.S
  | .gammaSeven, t => t
  | .gammaEight, t => t

noncomputable def feedbackU (p : SecondFunctionalParameters) (j : Term) (v t : ℝ) : ℝ :=
  1-t-feedbackJac p j t*v

noncomputable def feedbackLower (p : SecondFunctionalParameters) (j : Term) (v : ℝ) : ℝ :=
  match j with
  | .gammaFive | .gammaSix =>
    max (1/p.S) (max (1-v/p.S-upperQ p j) (1-v/p.S-1/2))
  | .gammaSeven | .gammaEight =>
    max (1/p.S) (max ((1-upperQ p j)/(v+1)) (1/(2*(v+1))))

noncomputable def feedbackUpper (p : SecondFunctionalParameters) (j : Term) (v : ℝ) : ℝ :=
  match j with
  | .gammaFive | .gammaSix =>
    min (upperP p j) (min (1-v/p.S-lowerQ p j) (min ((1-v/p.S)/2) (v/p.S)))
  | .gammaSeven | .gammaEight =>
    min (upperP p j) (min ((1-lowerQ p j)/(v+1)) (1/(v+2)))

theorem feedback_jac_bounds {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) :
    0 < feedbackJac p j t ∧ feedbackJac p j t ≤ 1 := by
  obtain ⟨ha,_,hBU,_,_,_,hU⟩ := gain_endpoint_order h j
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : t ≤ 1 := by linarith [ht.2]
  have hA0 : 0 < 1/p.S := by linarith
  have hA1 : 1/p.S ≤ 1 := by linarith [ht.1]
  cases j <;> simp only [feedbackJac] <;> exact ⟨by assumption, by assumption⟩

theorem feedback_inverse_ratio {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) (v : ℝ) :
    Hratio p j t (feedbackU p j v t) = v := by
  have hS : p.S ≠ 0 := ne_of_gt (by linarith [h.three_le_S])
  have ht0 : t ≠ 0 := ne_of_gt (by
    have := (gain_endpoint_order h j).1
    linarith [ht.1])
  cases j <;> dsimp [Hratio, feedbackU, feedbackJac] <;> field_simp <;> ring

theorem feedback_inverse_source {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {t : ℝ} (ht : t ∈ Icc (1/p.S) (upperP p j)) (u : ℝ) :
    feedbackU p j (Hratio p j t u) t = u := by
  have hS : p.S ≠ 0 := ne_of_gt (by linarith [h.three_le_S])
  have ht0 : t ≠ 0 := ne_of_gt (by
    have := (gain_endpoint_order h j).1
    linarith [ht.1])
  cases j <;> dsimp [Hratio, feedbackU, feedbackJac] <;> field_simp <;> ring

/-- The inverse map has derivative minus its positive absolute Jacobian. -/
theorem feedback_inverse_derivative (p : SecondFunctionalParameters) (j : Term) (t v : ℝ) :
    HasDerivAt (fun w => feedbackU p j w t) (-feedbackJac p j t) v := by
  convert! (hasDerivAt_const v (1-t)).sub
    ((hasDerivAt_id v).const_mul (feedbackJac p j t)) using 1
  simp

theorem feedback_fixed_section (A B C D q r t : ℝ) (hqr : q+r=1) :
    (A ≤ t ∧ t ≤ B ∧ C ≤ q-t ∧ q-t ≤ D ∧ t ≤ q-t ∧
      2*(q-t) ≤ 1 ∧ q-t+2*t ≤ 1) ↔
    max A (max (q-D) (q-1/2)) ≤ t ∧
      t ≤ min B (min (q-C) (min (q/2) r)) := by
  simp only [max_le_iff, le_min_iff]
  constructor
  · rintro ⟨ha,hb,hc,hd,ho,h1,h2⟩
    exact ⟨⟨ha,by linarith,by linarith⟩,hb,by linarith,by linarith,by linarith⟩
  · rintro ⟨⟨ha,hd,h1⟩,hb,hc,ho,h2⟩
    exact ⟨ha,hb,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem feedback_selected_section {A B C D v t : ℝ} (hA : 0 < A) (hv : 1 ≤ v) :
    (A ≤ t ∧ t ≤ B ∧ C ≤ 1-(v+1)*t ∧ 1-(v+1)*t ≤ D ∧
      t ≤ 1-(v+1)*t ∧ 2*(1-(v+1)*t) ≤ 1 ∧ 1-(v+1)*t+2*t ≤ 1) ↔
    max A (max ((1-D)/(v+1)) (1/(2*(v+1)))) ≤ t ∧
      t ≤ min B (min ((1-C)/(v+1)) (1/(v+2))) := by
  have hv1 : 0 < v+1 := by linarith
  have hv2 : 0 < v+2 := by linarith
  have hv12 : 0 < 2*(v+1) := by positivity
  simp only [max_le_iff, le_min_iff, div_le_iff₀ hv1, div_le_iff₀ hv12,
    le_div_iff₀ hv1, le_div_iff₀ hv2]
  constructor
  · rintro ⟨ha,hb,hc,hd,ho,h1,_⟩
    exact ⟨⟨ha,by nlinarith,by nlinarith⟩,hb,by nlinarith,by nlinarith⟩
  · rintro ⟨⟨ha,hd,h1⟩,hb,hc,ho⟩
    have ht : 0 < t := hA.trans_le ha
    exact ⟨ha,hb,by nlinarith,by nlinarith,by nlinarith,by nlinarith,
      by nlinarith [mul_nonneg (sub_nonneg.mpr hv) ht.le]⟩

/-- Exact section equivalence, including empty and singleton sections. -/
theorem feedback_section_iff {p : SecondFunctionalParameters} (h : AnalyticParameters p)
    (j : Term) {v : ℝ} (hv : v ∈ Icc 1 3) (t : ℝ) :
    (t,feedbackU p j v t) ∈ gainRegion p j ↔
      t ∈ Icc (feedbackLower p j v) (feedbackUpper p j v) := by
  have he : ∀ u, (t,u) ∈ gainRegion p j ↔
      1/p.S ≤ t ∧ t ≤ upperP p j ∧ lowerQ p j ≤ u ∧ u ≤ upperQ p j ∧
        t ≤ u ∧ 2*u ≤ 1 ∧ u+2*t ≤ 1 := by
    intro u
    simp only [gainRegion, mem_ofPred_eq, pairRegion_iff h j, mem_Icc, max_le_iff,
      gamma5GainLegal]
    tauto
  rw [he]
  have ha : 0 < 1/p.S := by have := (gain_endpoint_order h j).1; linarith
  cases j with
  | gammaFive =>
    simpa only [feedbackU,feedbackJac,feedbackLower,feedbackUpper,mem_Icc,
      one_div_mul_eq_div, show 1-t-v/p.S = (1-v/p.S)-t by ring] using
      feedback_fixed_section (1/p.S) (upperP p .gammaFive) (lowerQ p .gammaFive)
        (upperQ p .gammaFive) (1-v/p.S) (v/p.S) t (by ring)
  | gammaSix =>
    simpa only [feedbackU,feedbackJac,feedbackLower,feedbackUpper,mem_Icc,
      one_div_mul_eq_div, show 1-t-v/p.S = (1-v/p.S)-t by ring] using
      feedback_fixed_section (1/p.S) (upperP p .gammaSix) (lowerQ p .gammaSix)
        (upperQ p .gammaSix) (1-v/p.S) (v/p.S) t (by ring)
  | gammaSeven =>
    simpa only [feedbackU,feedbackJac,feedbackLower,feedbackUpper,mem_Icc,
      show 1-t-t*v = 1-(v+1)*t by ring] using
      feedback_selected_section (B := upperP p .gammaSeven) (C := lowerQ p .gammaSeven)
        (D := upperQ p .gammaSeven) (t := t) ha hv.1
  | gammaEight =>
    simpa only [feedbackU,feedbackJac,feedbackLower,feedbackUpper,mem_Icc,
      show 1-t-t*v = 1-(v+1)*t by ring] using
      feedback_selected_section (B := upperP p .gammaEight) (C := lowerQ p .gammaEight)
        (D := upperQ p .gammaEight) (t := t) ha hv.1

end Wu2008DoubleSieve.MotherPair
