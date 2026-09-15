import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21KernelTailBound

noncomputable section
open MeasureTheory Set Complex Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- The literal scale is at least one at the explicit cutoff. -/
theorem chen1973Lemma6_eq21_one_le_perronScale {x : ℕ} (hx : 3 ≤ x) :
    1 ≤ chen1973PerronScale (x : ℝ) := by
  unfold chen1973PerronScale
  exact Real.one_le_rpow (chen1973Lemma6_eq17_one_le_log_and_order hx).1 (by norm_num)

/-- Discarding only the smoothing factor, not changing the actual kernel. -/
theorem eq21_kernel_le_inv {x : ℕ} (hx : 1 < x) {σ t b : ℝ}
    (hσ : 0 ≤ σ) (hb : 0 < b) (hbs : b ≤ ‖(σ : ℂ) + t * I‖) :
    ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ ≤ b⁻¹ := by
  have hp := chen1973Lemma6_eq17_one_le_norm_one_add_div
    (chen1973Lemma6_eq17_perronScale_pos hx)
    (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have hpN := one_le_pow₀ (n := chen1973PerronOrder (x : ℝ) + 1) hp
  unfold chen1973MellinKernel
  rw [norm_div, norm_one, norm_mul, norm_pow, ← one_div]
  apply one_div_le_one_div_of_le hb
  exact hbs.trans (le_mul_of_one_le_right (norm_nonneg _) hpN)

private theorem eq21_weight_bounds {d a t : ℝ} (hd : 1 ≤ d)
    (ht : 0 ≤ t) (hta : t ≤ a) (r : ℕ) :
    0 ≤ (1 + Real.log (d * (1 + t))) ^ r ∧
    (1 + Real.log (d * (1 + t))) ^ r ≤
      (1 + Real.log (d * (1 + a))) ^ r := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have h1 : 1 ≤ d * (1 + t) := by nlinarith
  have h0 : 0 ≤ 1 + Real.log (d * (1 + t)) := by
    linarith [Real.log_nonneg h1]
  refine ⟨pow_nonneg h0 _, pow_le_pow_left₀ h0 ?_ r⟩
  have := Real.log_le_log (by positivity : 0 < d * (1 + t))
    (mul_le_mul_of_nonneg_left (by linarith : 1 + t ≤ 1 + a) hd0.le)
  linarith

/-- Head and middle intervals, with their separate sharp elementary budgets. -/
theorem chen1973Lemma6_eq21_weightedKernel_head_middle
    {x : ℕ} (hx : 3 ≤ x) {d σ : ℝ} (hd : 1 ≤ d) (hσ : 0 < σ) (r : ℕ) :
    let a := chen1973PerronScale (x : ℝ)
    let D := 1 + Real.log (d * (1 + a))
    let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
    IntegrableOn f (Ioc 0 1) ∧ IntegrableOn f (Ioc 1 a) ∧
      (∫ t in Ioc 0 1, f t) ≤ σ⁻¹ * D ^ r ∧
      (∫ t in Ioc 1 a, f t) ≤ Real.log a * D ^ r := by
  let a := chen1973PerronScale (x : ℝ)
  let D := 1 + Real.log (d * (1 + a))
  let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
  change IntegrableOn f (Ioc 0 1) ∧ IntegrableOn f (Ioc 1 a) ∧ _
  have ha1 : 1 ≤ a := chen1973Lemma6_eq21_one_le_perronScale hx
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hx1 : 1 < x := by omega
  have hm : Measurable f := by
    dsimp [f]; unfold chen1973MellinKernel; fun_prop
  have hhead : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ f t ∧ f t ≤ σ⁻¹ * D ^ r := by
    intro t ht
    have hw := eq21_weight_bounds hd ht.1.le (ht.2.trans ha1) r
    have hs : σ ≤ ‖(σ : ℂ) + t * I‖ := by
      simpa [abs_of_pos hσ] using Complex.abs_re_le_norm ((σ : ℂ) + t * I)
    exact ⟨mul_nonneg (norm_nonneg _) hw.1,
      mul_le_mul (eq21_kernel_le_inv hx1 hσ.le hσ hs) hw.2 hw.1 (by positivity)⟩
  have hmid : ∀ t ∈ Ioc (1 : ℝ) a, 0 ≤ f t ∧ f t ≤ t⁻¹ * D ^ r := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    have hw := eq21_weight_bounds hd ht0.le ht.2 r
    have hs : t ≤ ‖(σ : ℂ) + t * I‖ := by
      simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((σ : ℂ) + t * I)
    exact ⟨mul_nonneg (norm_nonneg _) hw.1,
      mul_le_mul (eq21_kernel_le_inv hx1 hσ.le ht0 hs) hw.2 hw.1 (by positivity)⟩
  have hH : IntegrableOn (fun _ : ℝ => σ⁻¹ * D ^ r) (Ioc 0 1) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hM0 : IntegrableOn (fun t : ℝ => t⁻¹) (Ioc 1 a) := by
    have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Icc 1 a) :=
      continuousOn_id.inv₀ (fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hM := hM0.mul_const (D ^ r)
  have hfH : IntegrableOn f (Ioc 0 1) := by
    apply hH.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hhead t ht).1]
    exact (hhead t ht).2
  have hfM : IntegrableOn f (Ioc 1 a) := by
    apply hM.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hmid t ht).1]
    exact (hmid t ht).2
  refine ⟨hfH, hfM, ?_, ?_⟩
  · calc
      _ ≤ ∫ t in Ioc (0 : ℝ) 1, σ⁻¹ * D ^ r :=
        setIntegral_mono_on hfH hH measurableSet_Ioc (fun t ht => (hhead t ht).2)
      _ = _ := by simp [D, a]
  · calc
      _ ≤ ∫ t in Ioc (1 : ℝ) a, t⁻¹ * D ^ r :=
        setIntegral_mono_on hfM hM measurableSet_Ioc (fun t ht => (hmid t ht).2)
      _ = _ := by
        rw [integral_mul_const, ← intervalIntegral.integral_of_le ha1,
          integral_inv_of_pos zero_lt_one ha]
        simp [D, a]

/-- Complex conjugation proves the norm is even on a vertical line. -/
theorem chen1973Lemma6_eq21_mellinKernel_norm_neg (x σ t : ℝ) :
    ‖chen1973MellinKernel x ((σ : ℂ) + (-t) * I)‖ =
      ‖chen1973MellinKernel x ((σ : ℂ) + t * I)‖ := by
  have hc : star (chen1973MellinKernel x ((σ : ℂ) + t * I)) =
      chen1973MellinKernel x ((σ : ℂ) + (-t) * I) := by
    simp [chen1973MellinKernel, star_div₀, star_mul, star_add, star_pow,
      mul_comm]
  rw [← hc, norm_star]

/-- Positive ray assembled from head, middle and the already-proved exact tail. -/
theorem chen1973Lemma6_eq21_weightedKernel_positive_integrable_and_bound
    {x : ℕ} (hx : 3 ≤ x) {d σ : ℝ} (hd : 1 ≤ d) (hσ : 0 < σ) (r : ℕ) :
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let D := 1 + Real.log (d * (1 + a))
    let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
    IntegrableOn f (Ioi 0) ∧ (∫ t in Ioi 0, f t) ≤
      (σ⁻¹ + Real.log a) * D ^ r +
        ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
          ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1)) := by
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let D := 1 + Real.log (d * (1 + a))
  let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
  change IntegrableOn f (Ioi 0) ∧ _
  obtain ⟨hH, hM, bH, bM⟩ := chen1973Lemma6_eq21_weightedKernel_head_middle hx hd hσ r
  obtain ⟨hT, bT⟩ := chen1973Lemma6_eq21_weightedKernel_tail_integrable_and_bound
    (σ := σ) (by omega : 1 < x) hd r
  change IntegrableOn f (Ioc 0 1) at hH
  change IntegrableOn f (Ioc 1 a) at hM
  change IntegrableOn f (Ioi a) at hT
  have ha1 : 1 ≤ a := chen1973Lemma6_eq21_one_le_perronScale hx
  have ha : 0 ≤ a := zero_le_one.trans ha1
  have hHM : IntegrableOn f (Ioc 0 a) := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one ha1]
    exact hH.union hM
  have hP : IntegrableOn f (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi ha]
    exact hHM.union hT
  have hsplitHM : (∫ t in Ioc 0 a, f t) =
      (∫ t in Ioc 0 1, f t) + ∫ t in Ioc 1 a, f t := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one ha1]
    apply setIntegral_union _ measurableSet_Ioc hH hM
    exact disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'.1)
  have hsplit : (∫ t in Ioi 0, f t) =
      (∫ t in Ioc 0 a, f t) + ∫ t in Ioi a, f t := by
    rw [← Ioc_union_Ioi_eq_Ioi ha]
    apply setIntegral_union _ measurableSet_Ioi hHM hT
    exact disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht')
  refine ⟨hP, ?_⟩
  change (∫ t in Ioc 0 1, f t) ≤ σ⁻¹ * D ^ r at bH
  change (∫ t in Ioc 1 a, f t) ≤ Real.log a * D ^ r at bM
  change (∫ t in Ioi a, f t) ≤ _ at bT
  rw [hsplit, hsplitHM]
  calc
    _ ≤ (σ⁻¹ * D ^ r + Real.log a * D ^ r) + _ :=
      add_le_add (add_le_add bH bM) bT
    _ = _ := by dsimp [D, a, N]; ring

/-- Full real-line weighted norm budget for the actual Mellin kernel.
This is a kernel estimate only, not a logarithmic-derivative estimate or
an unconditional version of equation (21). -/
theorem chen1973Lemma6_eq21_weightedKernel_full_integrable_and_bound
    {x : ℕ} (hx : 3 ≤ x) {d σ : ℝ} (hd : 1 ≤ d) (hσ : 0 < σ) (r : ℕ) :
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let D := 1 + Real.log (d * (1 + a))
    let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + |t|))) ^ r
    Integrable f ∧ (∫ t, f t) ≤ 2 *
      ((σ⁻¹ + Real.log a) * D ^ r +
        ∑ j ∈ Finset.range (r + 1), (Nat.choose r j : ℝ) * D ^ (r - j) *
          ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1))) := by
  let f := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + |t|))) ^ r
  let g := fun t : ℝ => ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
  change Integrable f ∧ _
  have heven : ∀ t, f (-t) = f t := by
    intro t
    dsimp [f]
    rw [abs_neg, Complex.ofReal_neg, chen1973Lemma6_eq21_mellinKernel_norm_neg]
  have hfg : ∀ t ∈ Ioi (0 : ℝ), g t = f t := by
    intro t ht
    dsimp [f, g]
    rw [abs_of_pos ht]
  obtain ⟨hg, bg⟩ :=
    chen1973Lemma6_eq21_weightedKernel_positive_integrable_and_bound hx hd hσ r
  change IntegrableOn g (Ioi 0) at hg
  have hP : IntegrableOn f (Ioi 0) := hg.congr_fun hfg measurableSet_Ioi
  have hL : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun t : ℝ => -t) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, heven, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hP
  have hf : Integrable f := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hL.union hP
  have hreflect : (∫ t in Iic (0 : ℝ), f t) = ∫ t in Ioi (0 : ℝ), f t := by
    calc
      _ = ∫ t in Iic (0 : ℝ), f (-t) := by simp only [heven]
      _ = _ := by rw [integral_comp_neg_Iic, neg_zero]
  have hfull : (∫ t, f t) = 2 * ∫ t in Ioi (0 : ℝ), g t := by
    calc
      _ = (∫ t in Iic (0 : ℝ), f t) + ∫ t in Ioi (0 : ℝ), f t := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hL hP,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ t in Ioi (0 : ℝ), f t := by rw [hreflect]; ring
      _ = _ := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => (hfg t ht).symm)
  refine ⟨hf, ?_⟩
  rw [hfull]
  exact mul_le_mul_of_nonneg_left bg (by norm_num)

end AnalyticNumberTheory.LargeSieve
