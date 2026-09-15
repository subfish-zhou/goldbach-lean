import HighO2TerminalGeometry

namespace HighO2Terminal
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- The source prime quadrature on the actual selected modulus d*N. The
single divisor-deletion theorem pays both p|N and p|d, without multiplicity
or endpoint changes. This is independent of source-box admissibility. -/
theorem selected_fibre_integral {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ d : ℕ, 0 < d → d ≤ N →
      ∀ q : ℝ, (N : ℝ)^(10*highEta) ≤ q → ∀ f : ℝ → ℝ,
      MonotoneOn f (Set.Icc 1 10) → (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |(∑ p ∈ primeWindow (d*N) (q^(1/t)) (q^(1/s)),
          f (t*(1-log (p : ℝ)/log q))/(((p : ℝ)-2)*(1-log (p : ℝ)/log q))) -
        ∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))| ≤ ε := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨Q0,_,hquad⟩ := omega2_source_prime_integral_uniform
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos hε)
  obtain ⟨T0,hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show 0 < highEta/2 by positivity) (show (0 : ℝ) ≤ 11 by norm_num) (half_pos hε)
  obtain ⟨T1,hgrow⟩ := eventually_atTop.mp
    ((((tendsto_rpow_atTop (show 0 < 10*highEta by positivity)).comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN d hd hdN q hq f hf hfb s t hs hst ht ht5
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNq : 1 < q := (one_lt_rpow hNr (by positivity : 0 < 10*highEta)).trans_le hq
  have hN0 : T0 ≤ N := (le_max_left T0 T1).trans ((le_max_right _ _).trans hN)
  have hN1 : T1 ≤ N := (le_max_right T0 T1).trans ((le_max_right _ _).trans hN)
  have hlow : ((d*N : ℕ) : ℝ)^(highEta/2) ≤ q^(1/t) := by
    calc
      _ ≤ ((N : ℝ)^2)^(highEta/2) := by
        apply rpow_le_rpow (Nat.cast_nonneg _)
        · rw [Nat.cast_mul,pow_two]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdN) (Nat.cast_nonneg N)
        · positivity
      _ = (N : ℝ)^highEta := by
        rw [← rpow_two,← rpow_mul (Nat.cast_nonneg N)]
        congr 1
        ring
      _ ≤ (N : ℝ)^((10*highEta)*(1/t)) := rpow_le_rpow_of_exponent_le hNr.le (by
        rw [mul_one_div]; apply (le_div_iff₀ (show 0 < t by linarith)).mpr; nlinarith)
      _ = ((N : ℝ)^(10*highEta))^(1/t) := rpow_mul (Nat.cast_nonneg N) _ _
      _ ≤ _ := rpow_le_rpow (by positivity) hq (by positivity)
  have hparam : ∀ M p, p ∈ primeWindow M (q^(1/t)) (q^(1/s)) →
      |f (t*(1-log (p : ℝ)/log q))| ≤ 11 := by
    intro M p hp
    have hh := mem_primeWindow.mp hp
    exact hfb _ (omega2_window_parameter_mem hNq (by exact_mod_cast hh.1.one_lt)
      hs hst ht ht5 hh.2.2.1 hh.2.2.2)
  have hdel := hdelete (d*N) (hN0.trans (by nlinarith)) q (q^(1/t)) (q^(1/s))
    (fun p => f (t*(1-log (p : ℝ)/log q))) hNq hlow
    (rpow_le_rpow_of_exponent_le hNq.le (one_div_le_one_div_of_le (by norm_num) hs))
    (hparam 1)
  have hpr := hquad q ((hgrow N hN1).trans hq) f hf hfb s t hs hst ht ht5
  rw [abs_sub_comm] at hdel
  exact (abs_sub_le _ _ _).trans ((add_le_add hdel hpr).trans_eq (by ring))

/-- True-li, singular factors, selected moduli and every original tuple
multiplicity survive the full-window quadrature on both original rectangles. -/
theorem original_selected_integral {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ, 0 < Δ →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ u ∈ Set.Icc (1 : ℝ) 10, |f u| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      |reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V)
          (fun d p => f (ratio N d p δ t)) -
        (∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))) *
          boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)| ≤
      ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := selected_fibre_integral hε
  refine ⟨T,hT4,?_⟩
  intro N hN Δ hΔ V hV hr f hf hfb s t hs hst ht ht5
  have hN4 := hT4.trans hN
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ)^(1/2-δ)
  let I := ∫ u in (1-1/s)..(1-1/t), f (t*u)/(u*(1-u))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ)*wuSingularSeries (d*N)/((Nat.totient d : ℝ)*log (Q/d))
  have hg := fun d hd => original_support (show 2 ≤ N by omega) hδ hδhi hΔ hV hr (d := d) hd
  have hpoint : ∀ d ∈ boxConvolutionSupport W,
      |(∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) - I| ≤ ε := by
    intro d hd
    exact hT N hN d (hg d hd).1 (hg d hd).2.1 (Q/d) (hg d hd).2.2.2.1 f hf hfb s t hs hst ht ht5
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hd
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos (hg d hd).1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hg d hd).2.2.2.2).le)
  have hli : 0 ≤ 4*logarithmicIntegral N := mul_nonneg (by norm_num)
    ((by positivity : (0 : ℝ) ≤ N/(2*log N)).trans (box_trueLi_lower hN4))
  change |4*logarithmicIntegral N*(∑ d ∈ boxConvolutionSupport W, w d *
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d)))) -
      I*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε*(4*logarithmicIntegral N*∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I,← mul_sub,abs_mul,abs_of_nonneg hli,mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I,sum_mul,← sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d*((∑ p ∈ primeWindow (d*N)
        (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        f (ratio N d p δ t)/(((p : ℝ)-2)*(1-log (p : ℝ)/log (Q/d))))-I)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d*ε := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← sum_mul,mul_comm]

end
end HighO2Terminal
