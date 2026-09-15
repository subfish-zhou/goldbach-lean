import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerPerron
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHalfStepContour
import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerVerticalIntegral
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicClosure

/-!
# The complete Pan source cell after Perron truncation

Both short and long polynomials are retained. The common half-step represents
the exact integer hyperbola, so there is no omitted boundary divisor term.
-/

noncomputable section
open Classical Complex Finset Filter MeasureTheory
open MathlibNt.SieveTheory.LiuWeight
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

theorem perron_polynomial_eq (S : Finset ℕ) (A : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n) {q : ℕ} (χ : PrimitiveCharacter q) (s : ℂ) :
    liuPanPerronDirichletPolynomial S A χ.1 s = polynomial S A χ s := by
  unfold liuPanPerronDirichletPolynomial polynomial
  apply sum_congr rfl
  intro n hn
  have hn0 := (hS n hn).ne'
  rw [liuPanPerronZeroExtension_of_ne A hn0, liuPanPerronNatPower_of_ne hn0,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0)]
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog, show -s * (Real.log n : ℂ) = -((Real.log n : ℂ) * s) by ring,
    Complex.exp_neg, div_eq_mul_inv]

theorem full_prime_polynomial_split {q : ℕ} (m H M : ℕ)
    (hHM : H ≤ M) (χ : PrimitiveCharacter q) (s : ℂ) :
    polynomial (Icc 1 M) (panSourceD m) χ s =
      panShortF₁ m H χ s + polynomial (Ioc H M) (panSourceD m) χ s := by
  have hset : Icc 1 M = Icc 1 H ∪ Ioc H M := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 H) (Ioc H M) := by
    apply disjoint_left.mpr
    intro n hn hm
    have := mem_Icc.mp hn
    have := mem_Ioc.mp hm
    omega
  simp only [polynomial, hset, sum_union hd, panShortF₁]

def halfStepLongKernel {q : ℕ} (f : ℕ → ℂ) (m H y A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (T : ℝ) (s : ℂ) : ℂ :=
  panDyadicG f m A₁ A₂ k χ s * longF₂ m H T χ s *
    (liuPanPerronHalfStep y : ℂ) ^ s / s

def halfStepLongIntegral {q : ℕ} (f : ℕ → ℂ) (m H y A₁ A₂ k : ℕ)
    (χ : PrimitiveCharacter q) (σ T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in -T..T, halfStepLongKernel f m H y A₁ A₂ k χ T (liuPanPerronLine σ t)

theorem longF₂_differentiable {q : ℕ} (m H : ℕ) (T : ℝ)
    (χ : PrimitiveCharacter q) : Differentiable ℂ (longF₂ m H T χ) := by
  unfold longF₂ polynomial
  apply panFinitePolynomial_differentiable
  intro n hn
  exact (Nat.zero_le H).trans_lt (mem_Ioc.mp hn).1

theorem halfStepLongKernel_line_continuous {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) (T σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t => halfStepLongKernel f m H y A₁ A₂ k χ T
      (liuPanPerronLine σ t)) := by
  have hline : Continuous (liuPanPerronLine σ) := by unfold liuPanPerronLine; fun_prop
  have hne (t : ℝ) : liuPanPerronLine σ t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [liuPanPerronLine] at this
    linarith
  have hY : (liuPanPerronHalfStep y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (halfStep_pos y).ne'
  unfold halfStepLongKernel
  exact ((((panDyadicG_differentiable f m A₁ A₂ k χ).continuous.comp hline).mul
    ((longF₂_differentiable m H T χ).continuous.comp hline)).mul
    ((differentiable_id.const_cpow (Or.inl hY)).continuous.comp hline)).div hline hne

/-- Exact passage from the exponential-form Perron integral to both of the
paper's finite complex-power polynomials. -/
theorem perron_integral_eq_short_add_long {q : ℕ} (f : ℕ → ℂ)
    (m H y A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q) {σ T : ℝ}
    (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) (hH : H ≤ ⌊T⌋₊) :
    liuPanTruncatedPerronIntegral
      (Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂)) (Icc 1 ⌊T⌋₊)
      (panSourceG f m) (panSourceD m) χ.1 σ T y =
    halfStepShortIntegral f m H y A₁ A₂ k χ σ T +
      halfStepLongIntegral f m H y A₁ A₂ k χ σ T := by
  have hpoint (t : ℝ) :
      Complex.exp (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep y)) /
          liuPanPerronLine σ t *
        (liuPanPerronDirichletPolynomial
          (Ioc (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂))
          (panSourceG f m) χ.1 (liuPanPerronLine σ t) *
        liuPanPerronDirichletPolynomial (Icc 1 ⌊T⌋₊)
          (panSourceD m) χ.1 (liuPanPerronLine σ t)) =
      halfStepShortKernel f m H y A₁ A₂ k χ (liuPanPerronLine σ t) +
        halfStepLongKernel f m H y A₁ A₂ k χ T (liuPanPerronLine σ t) := by
    rw [perron_polynomial_eq _ _ (fun n hn =>
      (Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1),
      perron_polynomial_eq _ _ (fun n hn => (mem_Icc.mp hn).1),
      full_prime_polynomial_split m H _ hH]
    have hexp : Complex.exp (liuPanPerronLine σ t * Real.log (liuPanPerronHalfStep y)) =
        (liuPanPerronHalfStep y : ℂ) ^ liuPanPerronLine σ t := by
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (halfStep_pos y).ne'),
        ← Complex.ofReal_log (halfStep_pos y).le, mul_comm]
    rw [hexp]
    change _ = _
    unfold halfStepShortKernel halfStepLongKernel longF₂ panDyadicG polynomial
    ring
  have hshort := halfStepShortKernel_vertical_integrable f m H y A₁ A₂ k χ
    (α := σ) hT ⟨hσ, le_rfl⟩
  have hlong := (halfStepLongKernel_line_continuous f m H y A₁ A₂ k χ T σ
    (by linarith)).intervalIntegrable (μ := volume) (-T) T
  unfold liuPanTruncatedPerronIntegral halfStepShortIntegral halfStepLongIntegral
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add hshort hlong, mul_add]

/-- The actual complete source cell, after shifting only the short integral.
The long integral has not been discarded or replaced by a rowwise bound. -/
theorem source_cell_perron_shift {q x y : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m H A₁ A₂ k : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hAy : A₂ ≤ y) (hHx : H ≤ x) :
    ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ -
      (halfStepShortIntegral f m H y A₁ A₂ k χ (1 / 2) (panSourceHeight x) +
        halfStepLongIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x))‖ ≤
      388 / (x : ℝ) ^ 2 := by
  have hp := source_amplitude_perron f hf m (2 ^ k * A₁)
    (min (2 ^ (k + 1) * A₁) A₂) χ hx hy hyx ((min_le_right _ _).trans (hAy.trans hyx))
  rw [perron_integral_eq_short_add_long f m H y A₁ A₂ k χ
    (σ := panSourceSigma x) (T := panSourceHeight x)
    (panSourceSigma_bounds (x := x) (by linarith)).1 (Real.exp_pos _).le
    (hHx.trans (sourceHeight_floor_ge (x := x) (by linarith)))] at hp
  have hc := halfStepShortIntegral_source_inverse_square f hf m H y A₁ A₂ k χ
    hx hy hyx hAy hHx
  refine (norm_sub_le_norm_sub_add_norm_sub _
    (halfStepShortIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x) +
      halfStepLongIntegral f m H y A₁ A₂ k χ (panSourceSigma x) (panSourceHeight x)) _).trans ?_
  rw [add_sub_add_right_eq_sub]
  calc
    _ ≤ 324 * ((x : ℝ) ^ 2)⁻¹ + 64 / (x : ℝ) ^ 2 := add_le_add hp hc
    _ = _ := by ring

def sourceCell (f : ℕ → ℂ) (m y A₁ A₂ k : ℕ) (R : ℝ) : ℝ :=
  ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
      (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖

/-- The reciprocal-totient primitive mass pays the number of conductors,
not the sum of their sizes. -/
theorem primitive_cell_constant_le {R E : ℝ} (hR : 1 ≤ R) (hE : 0 ≤ E) :
    (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ *
      ∑ _χ : PrimitiveCharacter q, E) ≤ 2 * R * E := by
  have hqpos (q : ℕ) (hq : q ∈ conductorCell R) : 0 < q := by
    have := (mem_Ioc.mp hq).1
    omega
  have hcard : ((conductorCell R).card : ℝ) ≤ 2 * R := by
    have hsub : conductorCell R ⊆ Icc 1 ⌊2 * R⌋₊ := by
      intro q hq
      exact mem_Icc.mpr ⟨hqpos q hq, (mem_Ioc.mp hq).2⟩
    have h := card_le_card hsub
    have hnat : (conductorCell R).card ≤ ⌊2 * R⌋₊ := by simpa using h
    exact (by exact_mod_cast hnat : ((conductorCell R).card : ℝ) ≤ ⌊2 * R⌋₊).trans
      (Nat.floor_le (by linarith))
  calc
    _ ≤ ∑ _q ∈ conductorCell R, E := by
      apply sum_le_sum
      intro q hq
      have hφ : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (hqpos q hq)
      have hχ : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ q.totient := by
        exact_mod_cast card_primitiveCharacter_le_totient q (hqpos q hq)
      simp only [sum_const, card_univ, nsmul_eq_mul]
      calc
        _ ≤ (q.totient : ℝ)⁻¹ * (q.totient * E) := by gcongr
        _ = E := by field_simp
    _ = ((conductorCell R).card : ℝ) * E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hE

theorem source_cell_le_integral_means {x y : ℕ} {R : ℝ}
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m A₁ A₂ k : ℕ)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hAy : A₂ ≤ y)
    (hR : 1 ≤ R) (hH : shortCutoff R ≤ x) :
    sourceCell f m y A₁ A₂ k R ≤
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖halfStepShortIntegral f m (shortCutoff R) y A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖) +
      (∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        ‖halfStepLongIntegral f m (shortCutoff R) y A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖) +
      2 * R * (388 / (x : ℝ) ^ 2) := by
  have hpoint (q : ℕ) (χ : PrimitiveCharacter q) :
      ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
        (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ‖ ≤
      ‖halfStepShortIntegral f m (shortCutoff R) y A₁ A₂ k χ (1 / 2) (panSourceHeight x)‖ +
      ‖halfStepLongIntegral f m (shortCutoff R) y A₁ A₂ k χ
        (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2 := by
    have h := source_cell_perron_shift f hf m (shortCutoff R) A₁ A₂ k χ
      hx hy hyx hAy hH
    have ht := norm_le_insert' (panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y
      (2 ^ k * A₁) (min (2 ^ (k + 1) * A₁) A₂) χ)
      (halfStepShortIntegral f m (shortCutoff R) y A₁ A₂ k χ (1 / 2) (panSourceHeight x) +
       halfStepLongIntegral f m (shortCutoff R) y A₁ A₂ k χ
         (panSourceSigma x) (panSourceHeight x))
    exact ht.trans (add_le_add (norm_add_le _ _) h)
  unfold sourceCell
  calc
    _ ≤ ∑ q ∈ conductorCell R, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
        (‖halfStepShortIntegral f m (shortCutoff R) y A₁ A₂ k χ
          (1 / 2) (panSourceHeight x)‖ +
        ‖halfStepLongIntegral f m (shortCutoff R) y A₁ A₂ k χ
          (panSourceSigma x) (panSourceHeight x)‖ + 388 / (x : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hpoint q χ) (by positivity)
    _ ≤ _ := by
      simp only [sum_add_distrib, mul_add]
      gcongr
      exact primitive_cell_constant_le hR (by positivity)

/-- A finite-height bound for the genuine cell. Both primitive means are
analytic inputs to this integration lemma and are discharged below. -/
theorem source_cell_bound_of_means {x y : ℕ} {R M₁ M₂ : ℝ}
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (m A₁ A₂ k : ℕ)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hAy : A₂ ≤ y)
    (hR : 1 ≤ R) (hH : shortCutoff R ≤ x) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs : ∀ s : ℂ, 1 / 2 ≤ s.re → shortMean f m A₁ A₂ k R s ≤ M₁)
    (hl : ∀ s : ℂ, 1 ≤ s.re →
      longMean f m A₁ A₂ k R (panSourceHeight x) s ≤ M₂) :
    sourceCell f m y A₁ A₂ k R ≤
      6 * liuPanPerronHalfStep y ^ (1 / 2 : ℝ) * M₁ * Real.log (1 + panSourceHeight x) +
      6 * liuPanPerronHalfStep y ^ panSourceSigma x * M₂ *
        Real.log (1 + panSourceHeight x) +
      2 * R * (388 / (x : ℝ) ^ 2) := by
  have hline (σ : ℝ) : Continuous (liuPanPerronLine σ) := by
    unfold liuPanPerronLine
    fun_prop
  have hshort := primitive_integral_mean_le (conductorCell R)
    (fun q χ t => panDyadicG f m A₁ A₂ k χ (liuPanPerronLine (1 / 2) t) *
      panShortF₁ m (shortCutoff R) χ (liuPanPerronLine (1 / 2) t))
    (le_refl (1 / 2 : ℝ)) (halfStep_pos y)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le) hM₁
    (fun q _ χ => ((panDyadicG_differentiable f m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((panShortF₁_differentiable m (shortCutoff R) χ).continuous.comp
        (hline _)))
    (fun t _ => hs _ (by simp [liuPanPerronLine]))
  have hσ : 1 ≤ panSourceSigma x := by
    unfold panSourceSigma
    have : 0 < Real.log (x : ℝ) := by linarith
    linarith [one_div_pos.mpr this]
  have hlong := primitive_integral_mean_le (conductorCell R)
    (fun q χ t => panDyadicG f m A₁ A₂ k χ (liuPanPerronLine (panSourceSigma x) t) *
      longF₂ m (shortCutoff R) (panSourceHeight x) χ (liuPanPerronLine (panSourceSigma x) t))
    (show 1 / 2 ≤ panSourceSigma x by linarith) (halfStep_pos y)
    (show 0 ≤ panSourceHeight x from (Real.exp_pos _).le) hM₂
    (fun q _ χ => ((panDyadicG_differentiable f m A₁ A₂ k χ).continuous.comp
      (hline _)).mul ((longF₂_differentiable m (shortCutoff R) (panSourceHeight x) χ).continuous.comp
        (hline _)))
    (fun t _ => hl _ (by simpa [liuPanPerronLine] using hσ))
  exact (source_cell_le_integral_means f hf m A₁ A₂ k hx hy hyx hAy hR hH).trans
    (add_le_add (add_le_add hshort hlong) le_rfl)

/-- The genuine source-cell bound with both polynomial means discharged.
The constants precede all source functions, parameters, and spectral heights. -/
theorem chosen_source_cell_uniform :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ B ε : ℝ, 0 ≤ B → 0 < ε → ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (y j m A₁ A₂ k : ℕ) (f : ℕ → ℂ),
      1 ≤ Real.log y → y ≤ x → A₂ ≤ y →
      conductorRadius x B j ≤ upperConductor x B →
      (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) → Real.log y ^ (2 * B) ≤ A₁ →
      (∀ n, ‖f n‖ ≤ 1) →
      sourceCell f m y A₁ A₂ k (conductorRadius x B j) ≤
        6 * liuPanPerronHalfStep y ^ (1 / 2 : ℝ) *
          (C₁ * Real.sqrt x * Real.log x ^ (1 - B)) * Real.log (1 + panSourceHeight x) +
        6 * liuPanPerronHalfStep y ^ panSourceSigma x *
          (C₂ * (Real.log x) ^ 2 / Real.log y ^ B) * Real.log (1 + panSourceHeight x) +
        776 / (x : ℝ) := by
  obtain ⟨C₁, hC₁, hs⟩ := chosen_short_mean_uniform
  obtain ⟨C₂, hC₂, hl⟩ := chosen_long_mean_uniform
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hs B ε hB hε
  have he : ∀ᶠ x : ℕ in atTop, 4 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp he
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx y j m A₁ A₂ k f hylog hyx hAy hRD hApower hAlow hf
  have hx1 := (le_max_left X₁ X₂).trans hx
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hy : 1 ≤ y := source_pos_of_log hylog
  have hxpos : (0 : ℝ) < x := by exact_mod_cast source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast source_pos_of_log hxlog1
  have hR := conductorRadius_ge_one j hxlog1 hB
  have hH := shortCutoff_le_x hxlog1 hB (by linarith : 0 ≤ conductorRadius x B j) hRD
  have hmain := source_cell_bound_of_means f hf m A₁ A₂ k hxlog hy hyx hAy hR hH
    (show 0 ≤ C₁ * Real.sqrt x * Real.log x ^ (1 - B) by positivity)
    (show 0 ≤ C₂ * (Real.log x) ^ 2 / Real.log y ^ B by positivity)
    (fun s hs' => hX₁ x hx1 j m A₁ A₂ k f s hRD hApower hf hs')
    (fun s hs' => hl B x y j m A₁ A₂ k f s hB hylog hyx hAlow hf hs')
  refine hmain.trans (add_le_add le_rfl ?_)
  have hRx : conductorRadius x B j ≤ (x : ℝ) := by
    refine (hRD.trans (upperConductor_le_sqrt hxlog1 hB)).trans ?_
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x : ℝ)]
  calc
    2 * conductorRadius x B j * (388 / (x : ℝ) ^ 2) ≤
        2 * (x : ℝ) * (388 / (x : ℝ) ^ 2) := by gcongr
    _ = _ := by field_simp; norm_num

theorem log_source_height_le {x : ℕ} (hx : 1 ≤ Real.log x) :
    Real.log (1 + panSourceHeight x) ≤ 3 * (Real.log x) ^ 2 := by
  have hT : 1 ≤ panSourceHeight x := by
    exact Real.one_le_exp_iff.mpr (by positivity)
  have htpos : 0 < panSourceHeight x := Real.exp_pos _
  have hlog := Real.log_le_log (by positivity : 0 < 1 + panSourceHeight x)
    (show 1 + panSourceHeight x ≤ 2 * panSourceHeight x by linarith)
  rw [Real.log_mul (by norm_num) htpos.ne', panSourceHeight, Real.log_exp] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  change Real.log (1 + Real.exp (2 * (Real.log (x : ℝ)) ^ 2)) ≤ _
  nlinarith

theorem halfStep_source_power_le_linear {x y : ℕ}
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    liuPanPerronHalfStep y ^ panSourceSigma x ≤ 2 * Real.exp 2 * y := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast source_pos_of_log (by linarith : 1 ≤ Real.log x)
  have hxlog : Real.log (x : ℝ) ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hyxR : (y : ℝ) ≤ x := by exact_mod_cast hyx
  have hY : liuPanPerronHalfStep y ≤ (x : ℝ) ^ 2 := by
    unfold liuPanPerronHalfStep
    nlinarith
  have hlog := Real.log_le_log (halfStep_pos y) hY
  rw [Real.log_pow] at hlog
  have he : liuPanPerronHalfStep y ^ (1 / Real.log x) ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos (halfStep_pos y)]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_iff₀ (by linarith : 0 < Real.log (x : ℝ))]
    simpa using hlog
  rw [panSourceSigma, Real.rpow_add (halfStep_pos y), Real.rpow_one]
  calc
    _ ≤ liuPanPerronHalfStep y * Real.exp 2 :=
      mul_le_mul_of_nonneg_left he (halfStep_pos y).le
    _ ≤ (2 * (y : ℝ)) * Real.exp 2 := by
      gcongr
      unfold liuPanPerronHalfStep
      linarith
    _ = _ := by ring

/-- At the full source endpoint, each real conductor/source cell has an
arbitrary logarithmic saving. This is an unconditional analytic producer,
not the weighted aggregate over induced conductors. -/
theorem chosen_source_cell_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (j m A₁ A₂ k : ℕ) (f : ℕ → ℂ),
      A₂ ≤ x → conductorRadius x B j ≤ upperConductor x B →
      (A₂ : ℝ) ≤ (x : ℝ) ^ (1 - ε) → Real.log x ^ (2 * B) ≤ A₁ →
      (∀ n, ‖f n‖ ≤ 1) →
      sourceCell f m x A₁ A₂ k (conductorRadius x B j) ≤
        C * (x : ℝ) * Real.log x ^ (4 - B) + 776 / (x : ℝ) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hcell⟩ := chosen_source_cell_uniform
  refine ⟨36 * C₁ + 36 * Real.exp 2 * C₂, by positivity, ?_⟩
  intro B ε hB hε
  obtain ⟨X₁, hX₁⟩ := hcell B ε hB hε
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max X₁ X₂, ?_⟩
  intro x hx j m A₁ A₂ k f hAx hRD hApower hAlow hf
  have hxlog : 4 ≤ Real.log (x : ℝ) := hX₂ x ((le_max_right X₁ X₂).trans hx)
  have hxlog1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hxpos := source_pos_of_log hxlog1
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hmain := hX₁ x ((le_max_left X₁ X₂).trans hx) x j m A₁ A₂ k f
    hxlog1 le_rfl hAx hRD hApower hAlow hf
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
  refine hmain.trans (add_le_add (add_le_add hshort hlong) le_rfl |>.trans ?_)
  exact le_of_eq (by ring)

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
