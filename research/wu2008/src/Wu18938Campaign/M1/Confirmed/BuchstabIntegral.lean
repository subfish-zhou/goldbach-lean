import Wu18938Campaign.M1.Confirmed.BuchstabNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology Interval

theorem shifted_parameter_mem {D p s t : ℝ} (hD : 1 < D) (hp : 1 < p)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hlo : D ^ (1 / t) ≤ p) (hhi : p < D ^ (1 / s)) :
    log D / log p - 1 ∈ Set.Icc (1 : ℝ) 10 := by
  have hh := buchstab_shifted_parameter hD hp (by linarith : 0 < s) (by linarith : 0 < t) hlo hhi
  rw [log_div (by linarith : D ≠ 0) (by linarith : p ≠ 0),sub_div,
    div_self (log_pos hp).ne'] at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

theorem shifted_prime_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) -
        (∫ u in (s - 1)..(t - 1), f u / u) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨Q0,_,hprime⟩ := primeCoefficient_source_log_uniform
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos he)
  obtain ⟨T1,hdelete⟩ := primeCoefficient_all_to_coprime_uniform
    (show 0 < η / 10 by positivity) (show (0 : ℝ) ≤ 11 by norm_num) (half_pos he)
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN i Δ V hb f hf hfb s t hs hst ht
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let I := ∫ u in (s - 1)..(t - 1), f u / u
  let g := fun d p : ℕ => f (log (Q / d) / log p - 1)
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      |(∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I| ≤ ε := by
    have hgeom := hb.support_geometry (by omega) hη hδ hd
    have hwin := window_geometry hb (by omega) hη hδ hd hs hst ht
    have hmain := hprime (Q / d) ((h2 N (by omega)).trans (hb.remaining d hd)) f hf hfb s t hs hst ht
    have hdel := hdelete N (by omega) (Q / d) (wuLocalCutoff N δ d t)
      (wuLocalCutoff N δ d s) (g d) hgeom.2.2.1 hwin.1 hwin.2 (by
        intro p hp
        have hh := mem_primeWindow.mp hp
        exact hfb _ (shifted_parameter_mem hgeom.2.2.1 (by exact_mod_cast hh.1.one_lt)
          hs hst ht hh.2.2.1 hh.2.2.2))
    rw [abs_sub_comm] at hdel
    exact (abs_sub_le _ _ _).trans ((add_le_add hdel hmain).trans_eq (by ring))
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  let w := fun d => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
    ((Nat.totient d : ℝ) * log (Q / d))
  have hw := fun d hd => roughBox_theta_weight hb (by omega) hη hδ (d := d) hd
  change |4 * logarithmicIntegral N *
      (∑ d ∈ boxConvolutionSupport W, w d *
        ∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) -
      I * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)
  rw [mul_left_comm I,← mul_sub,abs_mul,abs_of_nonneg hli,mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  rw [mul_comm I,sum_mul,← sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d *
        ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))) - I)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d * ε := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul,abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← sum_mul,mul_comm]

theorem shiftedPrime_to_source (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, (∀ v ∈ Set.Icc (1 : ℝ) 10, 0 ≤ f v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      shiftedPrime f N δ Δ V t r ≤
        reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) +
        shiftedBoundary f N δ Δ V t := by
  obtain ⟨T,hT4,hT⟩ := scale m hη hδ
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb f hf0 s t hs hst ht r hr
  obtain ⟨hΔ,_,_,hq,_,hmesh⟩ := hT N hN i Δ V hb
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let F := fun d p : ℕ => f (log (Q / d) / log p - 1) /
    (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : 0 < q := by dsimp [q,Q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNpos η).trans_le (hb.endpoint_lower l)
  have hD := fun d hd => reboxing_support_level_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
    hΔ0 hV (N := N) (d := d) hd
  have hfibre (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), F d p) ≤
      (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), F d p) +
      ∑ p ∈ primeWindow N (q ^ (1 / t)) (wuLocalCutoff N δ d t), |F d p| := by
    let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
    let B := primeWindow N (q ^ (1 / t)) (wuLocalCutoff N δ d t)
    let S := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
    have hAC := (reboxing_support_cutoff_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
      hΔ0 hV (show 0 < t by linarith) hd).1
    have hBD := (reboxing_support_cutoff_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
      hΔ0 hV (show 0 < s by linarith) hd).1
    have hCD := hb.cutoff_antitone (by omega) hη hδ hd (show 0 < s by linarith) hst
    have hsub : A ⊆ S ∪ B := by
      intro p hp
      obtain ⟨hpp,hpc,hpl,hpu⟩ := mem_primeWindow.mp hp
      by_cases hc : (p : ℝ) < wuLocalCutoff N δ d t
      · exact mem_union_right _ (mem_primeWindow.mpr
          ⟨hpp,hpc,by simpa only [reboxingAlpha_zero] using hpl,hc⟩)
      · exact mem_union_left _ (mem_primeWindow.mpr
          ⟨hpp,hpc,le_of_not_gt hc,hpu.trans_le (hr.trans hBD)⟩)
    have hdis : Disjoint S B := disjoint_left.mpr (fun p hp hp' =>
      (not_lt_of_ge (mem_primeWindow.mp hp).2.2.1) (mem_primeWindow.mp hp').2.2.2)
    have hsum : (∑ p ∈ A, F d p) ≤ (∑ p ∈ S, F d p) + ∑ p ∈ B, F d p := by
      rw [← sum_union hdis]
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hpall : p ∈ primeWindow N (q ^ (1 / t)) (wuLocalCutoff N δ d s) := by
        rcases mem_union.mp hp with hh | hh
        · have hh' := mem_primeWindow.mp hh
          exact mem_primeWindow.mpr ⟨hh'.1,hh'.2.1,hAC.trans hh'.2.2.1,hh'.2.2.2⟩
        · have hh' := mem_primeWindow.mp hh
          exact mem_primeWindow.mpr ⟨hh'.1,hh'.2.1,hh'.2.2.1,hh'.2.2.2.trans_le hCD⟩
      have hh := mem_primeWindow.mp hpall
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hh.1.pos
      have hu := reboxingLowerNormalization_parameter_mem hq hΔ hs hst ht
        (hD d hd).1 (hD d hd).2 hmesh hh.2.2.1 hh.2.2.2
      have hupper := hh.2.2.2.le.trans (window_geometry hb (by omega) hη hδ hd hs hst ht).2
      have hgap := reboxing_log_ratio_half (hb.support_geometry (by omega) hη hδ hd).2.2.1 hp0 hupper
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hh.1.two_le
      exact div_nonneg (hf0 _ hu) (mul_nonneg (by linarith) (by linarith))
    exact hsum.trans (add_le_add le_rfl (sum_le_sum (fun _ _ => le_abs_self _)))
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  unfold shiftedPrime reboxingPrimeSum shiftedBoundary
  simp only [Bool.false_eq_true,if_false]
  rw [← mul_add,← sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ hli
  apply sum_le_sum
  intro d hd
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (hfibre d hd) (roughBox_theta_weight hb (by omega) hη hδ hd)

end Wu18938Campaign.M1.Confirmed.Rebox
