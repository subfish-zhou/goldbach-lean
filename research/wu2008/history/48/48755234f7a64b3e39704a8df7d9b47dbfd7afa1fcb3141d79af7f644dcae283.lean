import MathlibNt.Wu2004MeanValue.SelectedContour
import MathlibNt.Wu2004MeanValue.SelectedVerticalIntegral

/-!
# A genuine source-cell producer for independently selected prefixes

The short and long polynomial means are discharged by the frozen analytic
producers. The long mean is evaluated with auxiliary endpoint `x`: its
polynomial has no prefix parameter. Only the Perron power uses the selection.
-/

noncomputable section
open Classical Complex Finset Filter MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

namespace Wu2004MeanValue

def selectedSourceCell (f : ℕ → ℂ) (m A₁ A₂ k : ℕ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ) (R : ℝ) : ℝ :=
  ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ)
      (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖

private theorem selected_cell_le_integral_means {x : ℕ} {R : ℝ}
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m A₁ A₂ k : ℕ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (hx : 4 ≤ Real.log x) (hy : ∀ q χ, 1 ≤ y q χ ∧ y q χ ≤ x) (hAx : A₂ ≤ x)
    (hR : 1 ≤ R) (hH : shortCutoff R ≤ x) :
    selectedSourceCell f m A₁ A₂ k y R ≤
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖halfStepShortIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖) +
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖halfStepLongIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖) +
      2 * R * (388 / (x : ℝ) ^ 2) := by
  have hpoint (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ)
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ ≤
      ‖halfStepShortIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
        (1 / 2) (panSourceHeight x)‖ +
      ‖halfStepLongIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
        (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2 := by
    have h := selected_source_cell_perron_shift f hf m (shortCutoff R) A₁ A₂ k χ
      hx (hy q χ).1 (hy q χ).2 hAx hH
    have ht := norm_le_insert'
      (panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) (y q χ)
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ)
      (halfStepShortIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
        (1 / 2) (panSourceHeight x) +
       halfStepLongIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
         (panSourceSigma x) (panSourceHeight x))
    exact ht.trans (add_le_add (norm_add_le _ _) h)
  unfold selectedSourceCell
  calc
    _ ≤ ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        (‖halfStepShortIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖ +
        ‖halfStepLongIntegral f m (shortCutoff R) (y q χ) A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hpoint q χ) (by positivity)
    _ ≤ _ := by
      simp only [sum_add_distrib, mul_add]
      gcongr
      exact primitive_cell_constant_le hR (by positivity)

private theorem selected_cell_bound_of_means {x : ℕ} {R M₁ M₂ : ℝ}
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m A₁ A₂ k : ℕ)
    (y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (hx : 4 ≤ Real.log x) (hy : ∀ q χ, 1 ≤ y q χ ∧ y q χ ≤ x) (hAx : A₂ ≤ x)
    (hR : 1 ≤ R) (hH : shortCutoff R ≤ x) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs : ∀ s : ℂ, 1 / 2 ≤ s.re → shortMean f m A₁ A₂ k R s ≤ M₁)
    (hl : ∀ s : ℂ, 1 ≤ s.re →
      longMean f m A₁ A₂ k R (panSourceHeight x) s ≤ M₂) :
    selectedSourceCell f m A₁ A₂ k y R ≤
      6 * liuPanPerronHalfStep x ^ (1 / 2 : ℝ) * M₁ * Real.log (1 + panSourceHeight x) +
      6 * liuPanPerronHalfStep x ^ panSourceSigma x * M₂ *
        Real.log (1 + panSourceHeight x) +
      2 * R * (388 / (x : ℝ) ^ 2) := by
  have hline (σ : ℝ) : Continuous (liuPanPerronLine σ) := by
    unfold liuPanPerronLine
    fun_prop
  have hU (q : ℕ) (χ : PrimitiveCharacter q) :
      0 < liuPanPerronHalfStep (y q χ) ∧
        liuPanPerronHalfStep (y q χ) ≤ liuPanPerronHalfStep x := by
    refine ⟨halfStep_pos _, ?_⟩
    unfold liuPanPerronHalfStep
    have : (y q χ : ℝ) ≤ x := by exact_mod_cast (hy q χ).2
    linarith
  have hshort := primitive_integral_selected_mean_le (conductorCell R)
    (fun q χ t => panDyadicG f m A₁ A₂ k χ (liuPanPerronLine (1 / 2) t) *
      panShortF₁ m (shortCutoff R) χ (liuPanPerronLine (1 / 2) t))
    (fun q χ => liuPanPerronHalfStep (y q χ))
    (le_refl (1 / 2 : ℝ)) (halfStep_pos x)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le) hM₁
    (fun q _ χ => ((panDyadicG_differentiable f m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((panShortF₁_differentiable m (shortCutoff R) χ).continuous.comp
        (hline _)))
    (fun q _ χ => hU q χ)
    (fun t _ => hs _ (by simp [liuPanPerronLine]))
  have hσ : 1 ≤ panSourceSigma x := by
    unfold panSourceSigma
    have : 0 < Real.log (x : ℝ) := by linarith
    linarith [one_div_pos.mpr this]
  have hlong := primitive_integral_selected_mean_le (conductorCell R)
    (fun q χ t => panDyadicG f m A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t) *
      longF₂ m (shortCutoff R) (panSourceHeight x) χ (liuPanPerronLine (panSourceSigma x) t))
    (fun q χ => liuPanPerronHalfStep (y q χ))
    (show 1 / 2 ≤ panSourceSigma x by linarith) (halfStep_pos x)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le) hM₂
    (fun q _ χ => ((panDyadicG_differentiable f m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((longF₂_differentiable m (shortCutoff R) (panSourceHeight x) χ).continuous.comp
        (hline _)))
    (fun q _ χ => hU q χ)
    (fun t _ => hl _ (by simpa [liuPanPerronLine] using hσ))
  exact (selected_cell_le_integral_means f hf m A₁ A₂ k y hx hy hAx hR hH).trans
    (add_le_add (add_le_add hshort hlong) le_rfl)

/-- Unconditional analytic saving for a complete source cell, uniformly over
all positive prefixes selected separately for every conductor and primitive
character. Constants precede the common coefficient function and selection. -/
theorem chosen_source_selected_cell_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ)
        (y : (q : ℕ) → PrimitiveCharacter q → ℕ),
      (∀ q χ, 1 ≤ y q χ ∧ y q χ ≤ x) →
      A₂ ≤ x → conductorRadius x B j ≤ upperConductor x B →
      (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) → Real.log x ^ (2 * B) ≤ A₁ →
      (∀ n, ‖f n‖ ≤ 1) →
      selectedSourceCell f m A₁ A₂ k y (conductorRadius x B j) ≤
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
  intro x hx j m A₁ A₂ k f y hy hAx hRD hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hR := conductorRadius_ge_one j hxlog1 hB
  have hH := shortCutoff_le_x hxlog1 hB (by linarith : 0 ≤ conductorRadius x B j) hRD
  have hmain := selected_cell_bound_of_means f hf m A₁ A₂ k y hxlog hy hAx hR hH
    (show 0 ≤ C₁ * Real.sqrt x * Real.log x ^ (1 - B) by positivity)
    (show 0 ≤ C₂ * (Real.log x) ^ 2 / Real.log x ^ B by positivity)
    (fun s hs' => hX₁ x ((le_max_left X₁ X₂).trans hx) j m A₁ A₂ k f s
      hRD hApower hf hs')
    (fun s hs' => hl B x x j m A₁ A₂ k f s hB hxlog1 le_rfl hAlow hf hs')
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
