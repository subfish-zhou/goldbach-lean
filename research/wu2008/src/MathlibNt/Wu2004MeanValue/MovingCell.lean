import MathlibNt.Wu2004MeanValue.MovingContour

/-! The frozen short and long large-sieve means apply pointwise to the same
Mellin coefficient for every modulus and character. -/

noncomputable section
open Classical Complex Finset Filter MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def movingSourceCell (f : ℕ → ℂ) (v : ℕ → ℕ) (m A₁ A₂ k : ℕ) (R : ℝ) : ℝ :=
  ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖movingAmplitude (panSourceG f m) (panSourceD m) v
      (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖

private theorem moving_cell_le_integral_means {x : ℕ} {R : ℝ}
    (f : ℕ → ℂ) (v : ℕ → ℕ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hv : ∀ a, 1 ≤ v a ∧ v a ≤ x) (m A₁ A₂ k : ℕ)
    (hx : 4 ≤ Real.log x) (hAx : A₂ ≤ x) (hR : 1 ≤ R) (hH : shortCutoff R ≤ x) :
    movingSourceCell f v m A₁ A₂ k R ≤
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖movingShortIntegral f v x m (shortCutoff R) A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖) +
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖movingLongIntegral f v x m (shortCutoff R) A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖) +
      2 * R * (388 / (x : ℝ) ^ 2) := by
  have hpoint (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖movingAmplitude (panSourceG f m) (panSourceD m) v
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ ≤
      ‖movingShortIntegral f v x m (shortCutoff R) A₁ A₂ k χ
        (1 / 2) (panSourceHeight x)‖ +
      ‖movingLongIntegral f v x m (shortCutoff R) A₁ A₂ k χ
        (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2 := by
    have h := moving_source_cell_perron_shift f v hf hv m (shortCutoff R) A₁ A₂ k χ hx hAx hH
    have ht := norm_le_insert'
      (movingAmplitude (panSourceG f m) (panSourceD m) v
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ)
      (movingShortIntegral f v x m (shortCutoff R) A₁ A₂ k χ
        (1 / 2) (panSourceHeight x) +
       movingLongIntegral f v x m (shortCutoff R) A₁ A₂ k χ
         (panSourceSigma x) (panSourceHeight x))
    exact ht.trans (add_le_add (norm_add_le _ _) h)
  unfold movingSourceCell
  calc
    _ ≤ ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        (‖movingShortIntegral f v x m (shortCutoff R) A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖ +
        ‖movingLongIntegral f v x m (shortCutoff R) A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hpoint q χ) (by positivity)
    _ ≤ _ := by
      simp only [sum_add_distrib, mul_add]
      gcongr
      exact primitive_cell_constant_le hR (by positivity)

/-- An unconditional moving-profile source-cell producer. Constants and
thresholds precede the arbitrary common coefficient and common profile. -/
theorem chosen_source_moving_cell_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ) (v : ℕ → ℕ),
      (∀ a, 1 ≤ v a ∧ v a ≤ x) →
      A₂ ≤ x → conductorRadius x B j ≤ upperConductor x B →
      (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) → Real.log x ^ (2 * B) ≤ A₁ →
      (∀ n, ‖f n‖ ≤ 1) →
      movingSourceCell f v m A₁ A₂ k (conductorRadius x B j) ≤
        C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ) := by
  obtain ⟨C₁, hC₁, hs⟩ := chosen_short_mean_uniform
  obtain ⟨C₂, hC₂, hl⟩ := chosen_long_mean_uniform
  refine ⟨36 * C₁ + 36 * Real.exp 2 * C₂, by positivity, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hs B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx j m A₁ A₂ k f v hv hAx hRD hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hR := conductorRadius_ge_one j hxlog1 hB
  have hH := shortCutoff_le_x hxlog1 hB (by linarith : 0 ≤ conductorRadius x B j) hRD
  have hline (σ : ℝ) : Continuous (liuPanPerronLine σ) := by
    unfold liuPanPerronLine
    fun_prop
  have hσ : 1 ≤ panSourceSigma x := by
    unfold panSourceSigma
    linarith [one_div_pos.mpr hlogpos]
  have hshortInt := primitive_integral_mean_le (conductorCell (conductorRadius x B j))
    (fun q χ t => movingG f v x m A₁ A₂ k χ (liuPanPerronLine (1 / 2) t) *
      panShortF₁ m (shortCutoff (conductorRadius x B j)) χ (liuPanPerronLine (1 / 2) t))
    (le_refl (1 / 2 : ℝ)) (halfStep_pos x)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le)
    (show 0 ≤ C₁ * Real.sqrt x * Real.log x ^ (1 - B) by positivity)
    (fun q _ χ => ((movingG_differentiable f v x m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((panShortF₁_differentiable m
        (shortCutoff (conductorRadius x B j)) χ).continuous.comp (hline _)))
    (fun t _ => hX₁ x ((le_max_left X₁ X₂).trans hx) j m A₁ A₂ k
      (movingCoefficient f v x (liuPanPerronLine (1 / 2) t))
      (liuPanPerronLine (1 / 2) t) hRD hApower
      (movingCoefficient_norm_le f v x hf (fun a => (hv a).2) (by simp [liuPanPerronLine]))
      (by simp [liuPanPerronLine]))
  have hlongInt := primitive_integral_mean_le (conductorCell (conductorRadius x B j))
    (fun q χ t => movingG f v x m A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t) *
      longF₂ m (shortCutoff (conductorRadius x B j)) (panSourceHeight x) χ
        (liuPanPerronLine (panSourceSigma x) t))
    (show 1 / 2 ≤ panSourceSigma x by linarith) (halfStep_pos x)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le)
    (show 0 ≤ C₂ * (Real.log x) ^ 2 / Real.log x ^ B by positivity)
    (fun q _ χ => ((movingG_differentiable f v x m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((longF₂_differentiable m
        (shortCutoff (conductorRadius x B j)) (panSourceHeight x) χ).continuous.comp (hline _)))
    (fun t _ => hl B x x j m A₁ A₂ k
      (movingCoefficient f v x (liuPanPerronLine (panSourceSigma x) t))
      (liuPanPerronLine (panSourceSigma x) t) hB hxlog1 le_rfl hAlow
      (movingCoefficient_norm_le f v x hf (fun a => (hv a).2)
        (by simp only [liuPanPerronLine, add_re, ofReal_re, mul_re, I_re, mul_zero,
          ofReal_im, I_im, zero_mul, sub_self, add_zero]; linarith))
      (by simpa [liuPanPerronLine] using hσ))
  have hmain := (moving_cell_le_integral_means f v hf hv m A₁ A₂ k hxlog hAx hR hH).trans
    (add_le_add (add_le_add hshortInt hlongInt) le_rfl)
  have hsqrt : liuPanPerronHalfStep x ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
    have hsq := Real.sq_sqrt (halfStep_pos x).le
    have hxq := Real.sq_sqrt hx0.le
    have hp := Real.sqrt_nonneg (liuPanPerronHalfStep x)
    have hxp := Real.sqrt_nonneg (x : ℝ)
    unfold liuPanPerronHalfStep at hsq hp ⊢
    nlinarith
  have hlogT := log_source_height_le hxlog1
  have hlognonneg : 0 ≤ Real.log (1 + panSourceHeight x) :=
    Real.log_nonneg (by have : 0 < panSourceHeight x := Real.exp_pos _; linarith)
  have hshort :
      6 * liuPanPerronHalfStep x ^ (1 / 2 : ℝ) *
          (C₁ * Real.sqrt x * Real.log x ^ (1 - B)) * Real.log (1 + panSourceHeight x) ≤
        36 * C₁ * (x : ℝ) * Real.log x ^ (4 - B) := by
    calc
      _ ≤ 6 * (2 * Real.sqrt x) * (C₁ * Real.sqrt x * Real.log x ^ (1 - B)) *
          (3 * (Real.log x) ^ 2) := by gcongr
      _ = 36 * C₁ * (x : ℝ) * Real.log x ^ (3 - B) := by
        rw [show (3 - B : ℝ) = (1 - B) + 2 by ring, Real.rpow_add hlogpos,
          Real.rpow_two]
        calc
          _ = 36 * C₁ * (Real.sqrt (x : ℝ)) ^ 2 *
              (Real.log x ^ (1 - B) * (Real.log x) ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt hx0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hlong :
      6 * liuPanPerronHalfStep x ^ panSourceSigma x *
          (C₂ * (Real.log x) ^ 2 / Real.log x ^ B) * Real.log (1 + panSourceHeight x) ≤
        (36 * Real.exp 2 * C₂) * (x : ℝ) * Real.log x ^ (4 - B) := by
    calc
      _ ≤ 6 * (2 * Real.exp 2 * (x : ℝ)) *
          (C₂ * (Real.log x) ^ 2 / Real.log x ^ B) * (3 * (Real.log x) ^ 2) := by
        gcongr
        exact halfStep_source_power_le_linear hxlog hxpos le_rfl
      _ = _ := by
        rw [Real.rpow_sub hlogpos, Real.rpow_ofNat]
        ring
  have hRx : conductorRadius x B j ≤ (x : ℝ) := by
    refine (hRD.trans (upperConductor_le_sqrt hxlog1 hB)).trans ?_
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg (x : ℝ)]
  have herr : 2 * conductorRadius x B j * (388 / (x : ℝ) ^ 2) ≤ 776 / (x : ℝ) := by
    calc
      _ ≤ 2 * (x : ℝ) * (388 / (x : ℝ) ^ 2) := by gcongr
      _ = _ := by field_simp; norm_num
  refine hmain.trans (add_le_add (add_le_add hshort hlong) herr |>.trans ?_)
  exact le_of_eq (by ring)

end Wu2004MeanValue