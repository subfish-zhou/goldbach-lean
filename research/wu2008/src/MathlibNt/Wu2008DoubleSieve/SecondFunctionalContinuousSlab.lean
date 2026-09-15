import MathlibNt.Wu2008DoubleSieve.SecondFunctionalContinuousRectangle

namespace Wu2008DoubleSieve
open Set MeasureTheory
open scoped BigOperators

/-- The literal closed affine band, before intersecting the cube. -/
def continuousBand {n : ℕ} (c : Fin n → ℝ) (γ η : ℝ) : Set (Fin n → ℝ) :=
  {t | |∑ i, c i * t i - γ| ≤ η}

theorem continuousBand_measurable {n : ℕ} (c : Fin n → ℝ) (γ η : ℝ) :
    MeasurableSet (continuousBand c γ η) := by
  apply measurableSet_le _ measurable_const
  fun_prop

theorem continuousSlab_integrable {n : ℕ} (c : Fin n → ℝ) (γ η : ℝ) :
    IntegrableOn continuousDensity (continuousCube n ∩ continuousBand c γ η) :=
  (continuousDensity_integrable n).mono_set inter_subset_left

/-- The one-dimensional slice lies in a centered interval for either coefficient sign. -/
theorem continuousSlice_subset {c d η : ℝ} (hc : 1 ≤ |c|) :
    {x : ℝ | |c * x - d| ≤ η} ⊆ Icc (d / c - η) (d / c + η) := by
  intro x hx
  have hc0 : c ≠ 0 := by intro h; norm_num [h] at hc
  have hmul : c * (x - d / c) = c * x - d := by field_simp
  have habs : |x - d / c| ≤ η := by
    calc
      _ ≤ |c| * |x - d / c| := le_mul_of_one_le_left (abs_nonneg _) hc
      _ = |c * x - d| := by rw [← abs_mul, hmul]
      _ ≤ η := hx
  constructor <;> linarith [(abs_le.mp habs).1, (abs_le.mp habs).2]

/-- The genuine reciprocal slice integral, uniformly in its intercept. -/
theorem continuousSlice_bound {c d η : ℝ} (hc : 1 ≤ |c|) (hη : 0 ≤ η) :
    (∫ x in Icc (1 / 10 : ℝ) (1 / 2) ∩ {x | |c * x - d| ≤ η}, 1 / x) ≤ 20 * η := by
  let s := Icc (1 / 10 : ℝ) (1 / 2) ∩ {x : ℝ | |c * x - d| ≤ η}
  have hs : MeasurableSet s := measurableSet_Icc.inter (measurableSet_le (by fun_prop) measurable_const)
  have hsub : s ⊆ Icc (1 / 10 : ℝ) (1 / 2) := inter_subset_left
  have hgeom : s ⊆ Icc (d / c - η) (d / c + η) :=
    fun _ hx => continuousSlice_subset hc hx.2
  calc
    _ ≤ ∫ _x in s, (10 : ℝ) := by
      apply setIntegral_mono_on ((continuousReciprocal_integrable (le_refl _)).mono_set hsub)
        (continuousOn_const.integrableOn_Icc.mono_set hsub) hs
      intro x hx
      have hx0 := (hsub hx).1
      apply (div_le_iff₀ (by linarith : 0 < x)).mpr
      linarith
    _ = 10 * volume.real s := by rw [setIntegral_const]; simp [mul_comm]
    _ ≤ 10 * volume.real (Icc (d / c - η) (d / c + η)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hgeom (by simp only [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) (by norm_num)
    _ = 20 * η := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

/-- Selected-coordinate Fubini for the actual restricted product volume. -/
theorem continuousCube_fubini {n : ℕ} (j : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : IntegrableOn f (continuousCube (n + 1))) :
    (∫ t in continuousCube (n + 1), f t) =
      ∫ s in continuousCube n, ∫ x in Icc (1 / 10 : ℝ) (1 / 2), f (j.insertNth x s) := by
  let μ : Measure ℝ := volume.restrict (Icc (1 / 10 : ℝ) (1 / 2))
  have hf' : Integrable f (Measure.pi fun _ : Fin (n + 1) => μ) := by
    simpa only [IntegrableOn, continuousCube, volume_pi, Measure.restrict_pi_pi] using hf
  have e := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j).symm
  have he := (e.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hf'
  have hi := e.integral_comp' f
  have he' : Integrable (fun p : ℝ × (Fin n → ℝ) => f (j.insertNth p.1 p.2))
      (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] using he
  have hi' : (∫ p : ℝ × (Fin n → ℝ), f (j.insertNth p.1 p.2)
      ∂(μ.prod (Measure.pi fun _ : Fin n => μ))) =
      ∫ t, f t ∂(Measure.pi fun _ : Fin (n + 1) => μ) := by
    simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk] using hi
  rw [integral_prod_symm _ he'] at hi'
  simpa only [continuousCube, volume_pi, Measure.restrict_pi_pi] using hi'.symm

/-- Insertion separates the selected reciprocal coordinate exactly. -/
theorem continuousDensity_insertNth {n : ℕ} (j : Fin (n + 1)) (x : ℝ) (s : Fin n → ℝ) :
    continuousDensity (j.insertNth x s) = (1 / x) * continuousDensity s := by
  unfold continuousDensity
  rw [Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- The selected-coordinate split of the affine expression. -/
theorem continuousAffine_insertNth {n : ℕ} (j : Fin (n + 1))
    (c : Fin (n + 1) → ℝ) (x : ℝ) (s : Fin n → ℝ) (γ : ℝ) :
    (∑ i, c i * (j.insertNth x s : Fin (n + 1) → ℝ) i) - γ =
      c j * x - (γ - ∑ i, c (j.succAbove i) * s i) := by
  rw [Fin.sum_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

/-- Literal weighted-volume Fubini factorization for an affine face. -/
theorem continuousSlab_factorization {n : ℕ} (j : Fin (n + 1))
    (c : Fin (n + 1) → ℝ) (γ η : ℝ) :
    (∫ t in continuousCube (n + 1) ∩ continuousBand c γ η, continuousDensity t) =
      ∫ s in continuousCube n, continuousDensity s *
        ∫ x in Icc (1 / 10 : ℝ) (1 / 2) ∩
          {x | |c j * x - (γ - ∑ i, c (j.succAbove i) * s i)| ≤ η}, 1 / x := by
  classical
  have hb := continuousBand_measurable c γ η
  rw [← setIntegral_indicator hb, continuousCube_fubini j _
    ((continuousDensity_integrable (n + 1)).indicator hb)]
  apply integral_congr_ae
  filter_upwards [] with s
  have hi (x : ℝ) : (continuousBand c γ η).indicator continuousDensity (j.insertNth x s) =
      {x : ℝ | |c j * x - (γ - ∑ i, c (j.succAbove i) * s i)| ≤ η}.indicator
        (fun x => 1 / x) x * continuousDensity s := by
    simp only [Set.indicator_apply, continuousBand, mem_ofPred_eq,
      continuousAffine_insertNth, continuousDensity_insertNth]
    split_ifs <;> simp
  simp_rw [hi]
  rw [integral_mul_const, setIntegral_indicator (measurableSet_le (by fun_prop) measurable_const),
    mul_comm]

/-- Uniform thin-band bound in successor dimension, for either selected coefficient sign. -/
theorem continuousSlab_bound_succ {n : ℕ} (j : Fin (n + 1))
    (c : Fin (n + 1) → ℝ) (γ η : ℝ) (hc : 1 ≤ |c j|) (hη : 0 ≤ η) :
    (∫ t in continuousCube (n + 1) ∩ continuousBand c γ η, continuousDensity t) ≤
      (4 : ℝ) ^ n * (20 * η) := by
  rw [continuousSlab_factorization j]
  calc
    _ ≤ ∫ s in continuousCube n, continuousDensity s * (20 * η) := by
      refine integral_mono_of_nonneg ?_ ((continuousDensity_integrable n).mul_const (20 * η)) ?_
      · filter_upwards [ae_restrict_mem (continuousCube_measurable n)] with s hs
        apply mul_nonneg (continuousDensity_nonneg hs)
        apply setIntegral_nonneg (measurableSet_Icc.inter (measurableSet_le (by fun_prop) measurable_const))
        intro x hx
        exact div_nonneg zero_le_one (by linarith [hx.1.1])
      · filter_upwards [ae_restrict_mem (continuousCube_measurable n)] with s hs
        exact mul_le_mul_of_nonneg_left (continuousSlice_bound hc hη) (continuousDensity_nonneg hs)
    _ = (∫ s in continuousCube n, continuousDensity s) * (20 * η) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (continuousCube_integral_bounds n).2 (by positivity)

/-- Dimension zero is excluded only by the explicit selected-coordinate witness. -/
theorem continuousSlab_bounds {n : ℕ} (j : Fin n) (c : Fin n → ℝ)
    (γ η : ℝ) (hc : 1 ≤ |c j|) (hη : 0 ≤ η) :
    0 ≤ (∫ t in continuousCube n ∩ continuousBand c γ η, continuousDensity t) ∧
      (∫ t in continuousCube n ∩ continuousBand c γ η, continuousDensity t) ≤
        (4 : ℝ) ^ (n - 1) * (20 * η) := by
  constructor
  · apply setIntegral_nonneg ((continuousCube_measurable n).inter (continuousBand_measurable c γ η))
    intro t ht
    exact continuousDensity_nonneg ht.1
  · cases n with
    | zero => exact Fin.elim0 j
    | succ n => simpa only [Nat.add_sub_cancel] using continuousSlab_bound_succ j c γ η hc hη

/-- Zero-thickness hyperplanes have zero reciprocal-weighted mass. -/
theorem continuousHyperplane_integral_zero {n : ℕ} (j : Fin n) (c : Fin n → ℝ)
    (γ : ℝ) (hc : 1 ≤ |c j|) :
    (∫ t in continuousCube n ∩ {t | ∑ i, c i * t i = γ}, continuousDensity t) = 0 := by
  have h := continuousSlab_bounds j c γ 0 hc (le_refl _)
  have hz : (∫ t in continuousCube n ∩ continuousBand c γ 0, continuousDensity t) = 0 :=
    le_antisymm (by simpa only [mul_zero] using h.2) h.1
  simpa [continuousBand, sub_eq_zero] using hz

/-- Lebesgue nullness follows from actual integrability and positivity, not from prime atoms. -/
theorem continuousHyperplane_null {n : ℕ} (j : Fin n) (c : Fin n → ℝ)
    (γ : ℝ) (hc : 1 ≤ |c j|) :
    volume (continuousCube n ∩ {t | ∑ i, c i * t i = γ}) = 0 := by
  let s := continuousCube n ∩ {t | ∑ i, c i * t i = γ}
  have hs : MeasurableSet s := (continuousCube_measurable n).inter
    (measurableSet_eq_fun (by fun_prop) measurable_const)
  have hf : IntegrableOn continuousDensity s :=
    (continuousDensity_integrable n).mono_set inter_subset_left
  have hpos : ∀ᵐ t ∂volume.restrict s, 0 < continuousDensity t :=
    (ae_restrict_mem hs).mono (fun _ ht => continuousDensity_pos ht.1)
  have hz := (integral_eq_zero_iff_of_nonneg_ae (hpos.mono (fun _ ht => ht.le)) hf).mp
    (continuousHyperplane_integral_zero j c γ hc)
  have hfalse : ∀ᵐ t ∂volume.restrict s, False := by
    filter_upwards [hpos, hz] with t ht hz
    exact (ne_of_gt ht) hz
  simpa only [ae_iff, not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] using hfalse

/-- Coefficients of the lower/product gate: all one except the last, which is two. -/
def continuousLowerCoefficients (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = Fin.last n then 2 else 1

theorem continuousLower_sum {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (∑ i, continuousLowerCoefficients n i * t i) = (∑ i, t i) + t (Fin.last n) := by
  classical
  calc
    _ = ∑ i, (t i + if i = Fin.last n then t i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold continuousLowerCoefficients
      split_ifs <;> ring
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The moving lower/product face in its original affine form. -/
def continuousLowerFace {n : ℕ} (φ η : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {t | |φ - (∑ i, t i) - t (Fin.last n)| ≤ η}

/-- The actual moving cap b, independent of the ambient cube upper endpoint. -/
def continuousCapFace {n : ℕ} (φ b η : ℝ) : Set (Fin n → ℝ) :=
  {t | |φ - (∑ i, t i) - b| ≤ η}

theorem continuousLowerFace_eq {n : ℕ} (φ η : ℝ) :
    continuousLowerFace (n := n) φ η = continuousBand (continuousLowerCoefficients n) φ η := by
  ext t
  simp only [continuousLowerFace, continuousBand, mem_ofPred_eq, continuousLower_sum]
  rw [show (∑ i, t i) + t (Fin.last n) - φ = -(φ - (∑ i, t i) - t (Fin.last n)) by ring, abs_neg]

theorem continuousCapFace_eq {n : ℕ} (φ b η : ℝ) :
    continuousCapFace (n := n) φ b η = continuousBand (fun _ => 1) (φ - b) η := by
  ext t
  simp only [continuousCapFace, continuousBand, mem_ofPred_eq, one_mul]
  rw [show (∑ i, t i) - (φ - b) = -(φ - (∑ i, t i) - b) by ring, abs_neg]

theorem continuousLowerFace_bounds {n : ℕ} (φ η : ℝ) (hη : 0 ≤ η) :
    0 ≤ (∫ t in continuousCube (n + 1) ∩ continuousLowerFace φ η, continuousDensity t) ∧
      (∫ t in continuousCube (n + 1) ∩ continuousLowerFace φ η, continuousDensity t) ≤
        (4 : ℝ) ^ n * (20 * η) := by
  rw [continuousLowerFace_eq]
  simpa only [Nat.add_sub_cancel] using
    continuousSlab_bounds (Fin.last n) (continuousLowerCoefficients n) φ η
      (by norm_num [continuousLowerCoefficients]) hη

theorem continuousCapFace_bounds {n : ℕ} (j : Fin n) (φ b η : ℝ) (hη : 0 ≤ η) :
    0 ≤ (∫ t in continuousCube n ∩ continuousCapFace φ b η, continuousDensity t) ∧
      (∫ t in continuousCube n ∩ continuousCapFace φ b η, continuousDensity t) ≤
        (4 : ℝ) ^ (n - 1) * (20 * η) := by
  rw [continuousCapFace_eq]
  exact continuousSlab_bounds j (fun _ => 1) (φ - b) η (by norm_num) hη

/-- Both actual moving faces for the four-prefix case, with unrestricted moving parameter. -/
theorem continuousFaces_fin4 (φ b η : ℝ) (hη : 0 ≤ η) :
    (0 ≤ (∫ t in continuousCube 4 ∩ continuousLowerFace φ η, continuousDensity t) ∧
      (∫ t in continuousCube 4 ∩ continuousLowerFace φ η, continuousDensity t) ≤
        (4 : ℝ) ^ 3 * (20 * η)) ∧
    (0 ≤ (∫ t in continuousCube 4 ∩ continuousCapFace φ b η, continuousDensity t) ∧
      (∫ t in continuousCube 4 ∩ continuousCapFace φ b η, continuousDensity t) ≤
        (4 : ℝ) ^ 3 * (20 * η)) :=
  ⟨continuousLowerFace_bounds φ η hη, continuousCapFace_bounds (0 : Fin 4) φ b η hη⟩

/-- Both actual moving faces for the five-prefix case. -/
theorem continuousFaces_fin5 (φ b η : ℝ) (hη : 0 ≤ η) :
    (0 ≤ (∫ t in continuousCube 5 ∩ continuousLowerFace φ η, continuousDensity t) ∧
      (∫ t in continuousCube 5 ∩ continuousLowerFace φ η, continuousDensity t) ≤
        (4 : ℝ) ^ 4 * (20 * η)) ∧
    (0 ≤ (∫ t in continuousCube 5 ∩ continuousCapFace φ b η, continuousDensity t) ∧
      (∫ t in continuousCube 5 ∩ continuousCapFace φ b η, continuousDensity t) ≤
        (4 : ℝ) ^ 4 * (20 * η)) :=
  ⟨continuousLowerFace_bounds φ η hη, continuousCapFace_bounds (0 : Fin 5) φ b η hη⟩

theorem continuousLowerFace_null {n : ℕ} (φ : ℝ) :
    volume (continuousCube (n + 1) ∩ continuousLowerFace (n := n) φ 0) = 0 := by
  rw [continuousLowerFace_eq]
  simpa [continuousBand, sub_eq_zero] using
    continuousHyperplane_null (Fin.last n) (continuousLowerCoefficients n) φ
      (by norm_num [continuousLowerCoefficients])

theorem continuousCapFace_null {n : ℕ} (j : Fin n) (φ b : ℝ) :
    volume (continuousCube n ∩ continuousCapFace (n := n) φ b 0) = 0 := by
  rw [continuousCapFace_eq]
  simpa [continuousBand, sub_eq_zero] using
    continuousHyperplane_null j (fun _ => 1) (φ - b) (by norm_num)

theorem continuousFaces_fin4_null (φ b : ℝ) :
    volume (continuousCube 4 ∩ continuousLowerFace φ 0) = 0 ∧
      volume (continuousCube 4 ∩ continuousCapFace φ b 0) = 0 :=
  ⟨continuousLowerFace_null φ, continuousCapFace_null (0 : Fin 4) φ b⟩

theorem continuousFaces_fin5_null (φ b : ℝ) :
    volume (continuousCube 5 ∩ continuousLowerFace φ 0) = 0 ∧
      volume (continuousCube 5 ∩ continuousCapFace φ b 0) = 0 :=
  ⟨continuousLowerFace_null φ, continuousCapFace_null (0 : Fin 5) φ b⟩

end Wu2008DoubleSieve
