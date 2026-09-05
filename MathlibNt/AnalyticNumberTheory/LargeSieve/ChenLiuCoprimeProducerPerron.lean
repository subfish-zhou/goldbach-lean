import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerLong
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitivePerron

/-!
# Finite-height Perron truncation for the complete Pan source

The existing, proved Perron kernel estimate is used at Pan's actual abscissa
and exponential height. Reciprocal product weights are retained in the error:
an unweighted count up to the exponential height would lose the saving.
Only the truncation remainder is estimated coefficientwise.
-/

noncomputable section
open Classical Complex Finset Filter
open scoped BigOperators

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

open MathlibNt.SieveTheory MathlibNt.SieveTheory.LiuWeight

theorem source_pos_of_log {x : ℕ} (hx : 1 ≤ Real.log x) : 0 < x := by
  by_contra h
  have : x = 0 := by omega
  norm_num [this] at hx

/-- The numerator costs a fixed polynomial, while every positive coefficient
retains its reciprocal weight. -/
theorem halfStep_ratio_source_power_le {x y n : ℕ}
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hn : n ≠ 0) :
    (liuPanPerronHalfStep y / (n : ℝ)) ^ panSourceSigma x ≤
      4 * (x : ℝ) ^ 2 / n := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hy.trans hyx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < liuPanPerronHalfStep y := by unfold liuPanPerronHalfStep; positivity
  have hy1 : 1 ≤ liuPanPerronHalfStep y := by
    have : (1 : ℝ) ≤ y := by exact_mod_cast hy
    unfold liuPanPerronHalfStep
    linarith
  have hy2 : liuPanPerronHalfStep y ≤ 2 * (x : ℝ) := by
    have : (y : ℝ) ≤ x := by exact_mod_cast hyx
    unfold liuPanPerronHalfStep
    linarith
  have hs1 : 1 ≤ panSourceSigma x := by
    unfold panSourceSigma
    have : 0 < Real.log (x : ℝ) := by linarith
    linarith [one_div_pos.mpr this]
  have hnum : liuPanPerronHalfStep y ^ panSourceSigma x ≤ 4 * (x : ℝ) ^ 2 := by
    calc
      _ ≤ liuPanPerronHalfStep y ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy1 (panSourceSigma_bounds hx).2
      _ = liuPanPerronHalfStep y ^ 2 := Real.rpow_two _
      _ ≤ (2 * (x : ℝ)) ^ 2 := pow_le_pow_left₀ hy0.le hy2 2
      _ = _ := by ring
  have hden : (n : ℝ) ≤ (n : ℝ) ^ panSourceSigma x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hs1
  rw [Real.div_rpow hy0.le hn0.le]
  exact div_le_div₀ (by positivity) hnum hn0 hden

/-- A uniform, weighted kernel error on every positive integer, including
coordinates beyond the hyperbola. No kernel approximation is assumed. -/
theorem source_kernel_error_le {x y n : ℕ} {T : ℝ}
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hn : n ≠ 0) (hT : 0 < T) :
    ‖(if n ≤ y then 1 else 0 : ℂ) -
      liuPanTruncatedPerronKernel (panSourceSigma x) T
        (liuPanPerronHalfStep y / n)‖ ≤
      (108 * (x : ℝ) ^ 3 / T) / n := by
  have hxN : 1 ≤ x := hy.trans hyx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hxN
  have hx0 : (0 : ℝ) < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs := panSourceSigma_bounds hx
  have hs0 : 0 < panSourceSigma x := by linarith [hs.1]
  let z := liuPanPerronHalfStep y / (n : ℝ)
  have hz : 0 < z := liuPanPerronHalfStep_div_natCast_pos hn
  have hz1 : z ≠ 1 := by
    intro h
    exact natCast_ne_liuPanPerronHalfStep n y
      ((div_eq_one_iff_eq hn0.ne').mp h).symm
  have hcut : 1 < z ↔ n ≤ y := by
    dsimp [z]
    rw [one_lt_div₀ hn0]
    exact natCast_lt_liuPanPerronHalfStep_iff
  have hsep := one_div_eight_mul_le_abs_log_liuPanPerronHalfStep_div hn hxN hyx
  have hlog : 0 < |Real.log z| := lt_of_lt_of_le (by positivity) hsep
  have hinv : 1 / |Real.log z| ≤ 8 * (x : ℝ) := by
    rw [div_le_iff₀ hlog]
    rw [div_le_iff₀ (by positivity : 0 < 8 * (x : ℝ))] at hsep
    nlinarith
  have hkernel := norm_liuPanTruncatedPerronKernel_sub_indicator_le hs0 hT hz hz1
  simp only [hcut] at hkernel
  have hfactor : z ^ panSourceSigma x / Real.pi ≤ 4 * (x : ℝ) ^ 2 / n := by
    exact (div_le_self (by positivity) (by linarith [Real.pi_gt_three])).trans
      (halfStep_ratio_source_power_le hx hy hyx hn)
  have hfirst : 3 / (|Real.log z| * T) ≤ 24 * (x : ℝ) / T := by
    calc
      _ = 3 * (1 / |Real.log z|) / T := by ring
      _ ≤ 3 * (8 * (x : ℝ)) / T := by gcongr
      _ = _ := by ring
  have hsecond : 3 * panSourceSigma x / (2 * T) ≤ 3 * (x : ℝ) / T := by
    calc
      _ ≤ 3 * 2 / (2 * T) := by gcongr; exact hs.2
      _ = 3 / T := by ring
      _ ≤ _ := by gcongr; linarith
  calc
    _ ≤ (z ^ panSourceSigma x / Real.pi) *
        (3 / (|Real.log z| * T) + 3 * panSourceSigma x / (2 * T)) := hkernel
    _ ≤ (4 * (x : ℝ) ^ 2 / n) * (24 * (x : ℝ) / T + 3 * (x : ℝ) / T) := by
      gcongr
    _ = _ := by ring

/-- The full finite hyperbola has a harmonic-mass error, rather than the
unusable cardinality of the exponential prime cutoff. -/
theorem hyperbola_error_le_harmonic {q x y : ℕ} {T : ℝ}
    (U V : Finset ℕ) (A B : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hU : ∀ u ∈ U, 0 < u) (hV : ∀ v ∈ V, 0 < v)
    (hA : ∀ u ∈ U, ‖A u‖ ≤ 1) (hB : ∀ v ∈ V, ‖B v‖ ≤ 1)
    (hx : 1 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hT : 0 < T) :
    ‖liuPanTruncatedPerronError U V A B χ (panSourceSigma x) T y‖ ≤
      (108 * (x : ℝ) ^ 3 / T) *
        (∑ u ∈ U, (u : ℝ)⁻¹) * (∑ v ∈ V, (v : ℝ)⁻¹) := by
  have hs : 0 < panSourceSigma x := by linarith [(panSourceSigma_bounds hx).1]
  rw [liuPanTruncatedPerronError,
    liuPanTruncatedPerronIntegral_eq_kernelSum U V A B χ y hs,
    liuPanPerronHyperbolaSum, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  have hterm (u : ℕ) (hu : u ∈ U) (v : ℕ) (hv : v ∈ V) :
      ‖(if u * v ≤ y then liuPanPerronProductCoefficient A B χ u v else 0) -
        liuPanPerronProductCoefficient A B χ u v *
          liuPanTruncatedPerronKernel (panSourceSigma x) T
            (liuPanPerronHalfStep y / (u * v : ℕ))‖ ≤
        (108 * (x : ℝ) ^ 3 / T) * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := by
    have hu0 := (hU u hu).ne'
    have hv0 := (hV v hv).ne'
    have hcoeff : ‖liuPanPerronProductCoefficient A B χ u v‖ ≤ 1 := by
      simp only [liuPanPerronProductCoefficient, hu0, hv0, or_self, if_false, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (hA u hu) (norm_nonneg _) (hB v hv))
        (norm_nonneg _) (dirichletCharacter_norm_le_one q χ _)
    rw [show (if u * v ≤ y then liuPanPerronProductCoefficient A B χ u v else 0) -
        liuPanPerronProductCoefficient A B χ u v *
          liuPanTruncatedPerronKernel (panSourceSigma x) T
            (liuPanPerronHalfStep y / (u * v : ℕ)) =
      liuPanPerronProductCoefficient A B χ u v *
        ((if u * v ≤ y then 1 else 0 : ℂ) -
          liuPanTruncatedPerronKernel (panSourceSigma x) T
            (liuPanPerronHalfStep y / (u * v : ℕ))) by split_ifs <;> ring,
      norm_mul]
    calc
      _ ≤ 1 * ((108 * (x : ℝ) ^ 3 / T) / (u * v : ℕ)) :=
        mul_le_mul hcoeff (source_kernel_error_le hx hy hyx
          (Nat.mul_ne_zero hu0 hv0) hT) (norm_nonneg _) (by norm_num)
      _ = _ := by push_cast; simp only [div_eq_mul_inv, mul_inv_rev]; ring
  calc
    _ ≤ ∑ u ∈ U, ∑ v ∈ V,
        ‖(if u * v ≤ y then liuPanPerronProductCoefficient A B χ u v else 0) -
          liuPanPerronProductCoefficient A B χ u v *
            liuPanTruncatedPerronKernel (panSourceSigma x) T
              (liuPanPerronHalfStep y / (u * v : ℕ))‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun u _ => norm_sum_le _ _)
    _ ≤ ∑ u ∈ U, ∑ v ∈ V,
        (108 * (x : ℝ) ^ 3 / T) * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ :=
      sum_le_sum fun u hu => sum_le_sum fun v hv => hterm u hu v hv
    _ = _ := by simp only [← mul_sum, ← sum_mul]

/-- The literal exponential height pays every fixed polynomial loss. -/
theorem sourceHeight_ge_pow (K : ℕ) {x : ℕ}
    (hx : 1 ≤ Real.log x) (hK : (K : ℝ) ≤ 2 * Real.log x) :
    (x : ℝ) ^ K ≤ panSourceHeight x := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast source_pos_of_log hx
  have hlog : 0 ≤ Real.log (x : ℝ) := by linarith
  have h := Real.exp_le_exp.mpr (show (K : ℝ) * Real.log x ≤
      2 * (Real.log x) ^ 2 by nlinarith)
  rw [mul_comm (K : ℝ), Real.exp_mul, Real.exp_log hx0] at h
  simpa only [Real.rpow_natCast, panSourceHeight] using h

theorem sourceHeight_floor_ge {x : ℕ} (hx : 1 ≤ Real.log x) :
    x ≤ ⌊panSourceHeight x⌋₊ := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast source_pos_of_log hx
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  exact (show (x : ℝ) ≤ (x : ℝ) ^ 2 by nlinarith).trans
    (sourceHeight_ge_pow 2 hx (by norm_num; linarith))

/-- Uniform error at the actual height, even though the second polynomial
contains every coordinate through `floor T`. -/
theorem source_hyperbola_error_le {q x y : ℕ}
    (U V : Finset ℕ) (A B : ℕ → ℂ) (χ : DirichletCharacter ℂ q)
    (hU : U ⊆ Icc 1 x) (hV : V ⊆ Icc 1 ⌊panSourceHeight x⌋₊)
    (hA : ∀ u ∈ U, ‖A u‖ ≤ 1) (hB : ∀ v ∈ V, ‖B v‖ ≤ 1)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    ‖liuPanTruncatedPerronError U V A B χ
      (panSourceSigma x) (panSourceHeight x) y‖ ≤ 324 * ((x : ℝ) ^ 2)⁻¹ := by
  have hxlog : 1 ≤ Real.log (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast source_pos_of_log hxlog
  have hx0 : (0 : ℝ) < x := by linarith
  have hT : 0 < panSourceHeight x := Real.exp_pos _
  have hN : 0 < (⌊panSourceHeight x⌋₊ : ℝ) := by
    have := (source_pos_of_log hxlog).trans_le (sourceHeight_floor_ge hxlog)
    exact_mod_cast this
  have hlogx : Real.log (x : ℝ) ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hEU : (∑ u ∈ U, (u : ℝ)⁻¹) ≤ x :=
    (harmonic_energy_le_log U x hU).trans (by linarith)
  have hEV : (∑ v ∈ V, (v : ℝ)⁻¹) ≤ 3 * (x : ℝ) ^ 2 := by
    have hlogT := Real.log_le_log hN (Nat.floor_le hT.le)
    rw [show Real.log (panSourceHeight x) = 2 * (Real.log x) ^ 2 by
      simp only [panSourceHeight, Real.log_exp]] at hlogT
    have hsquare : (Real.log (x : ℝ)) ^ 2 ≤ (x : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    refine (harmonic_energy_le_log V _ hV).trans ?_
    nlinarith
  calc
    _ ≤ (108 * (x : ℝ) ^ 3 / panSourceHeight x) *
        (∑ u ∈ U, (u : ℝ)⁻¹) * (∑ v ∈ V, (v : ℝ)⁻¹) :=
      hyperbola_error_le_harmonic U V A B χ
        (fun u hu => (mem_Icc.mp (hU hu)).1)
        (fun v hv => (mem_Icc.mp (hV hv)).1) hA hB hxlog hy hyx hT
    _ ≤ (108 * (x : ℝ) ^ 3 / panSourceHeight x) * x * (3 * (x : ℝ) ^ 2) := by
      gcongr
    _ = 324 * (x : ℝ) ^ 6 / panSourceHeight x := by ring
    _ ≤ 324 * (x : ℝ) ^ 6 / (x : ℝ) ^ 8 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sourceHeight_ge_pow 8 hxlog (by norm_num; linarith))
    _ = _ := by field_simp

/-- Exact integer hyperbola, including equality at `a*n=y`. The common
half-step is applied to the product, not separately to each source row. -/
theorem source_amplitude_eq_hyperbola {q : ℕ}
    (A B : ℕ → ℂ) (y L U M : ℕ) (χ : PrimitiveCharacter q) (hyM : y ≤ M) :
    panSourceCharacterAmplitude A B y L U χ =
      liuPanPerronHyperbolaSum (Ioc L U) (Icc 1 M) A B χ.1 y := by
  unfold panSourceCharacterAmplitude liuPanPerronHyperbolaSum
  apply sum_congr rfl
  intro a ha
  have ha0 : 0 < a := (Nat.zero_le L).trans_lt (mem_Ioc.mp ha).1
  rw [mul_sum]
  have hsub : Icc 1 (y / a) ⊆ Icc 1 M := by
    intro n hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
      (mem_Icc.mp hn).2.trans ((Nat.div_le_self y a).trans hyM)⟩
  calc
    _ = ∑ n ∈ Icc 1 (y / a),
        if a * n ≤ y then liuPanPerronProductCoefficient A B χ.1 a n else 0 := by
      apply sum_congr rfl
      intro n hn
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have han : a * n ≤ y := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le ha0).mp (mem_Icc.mp hn).2
      simp only [if_pos han, liuPanPerronProductCoefficient, ha0.ne', hn0.ne',
        or_self, if_false, Nat.cast_mul, map_mul]
      ring
    _ = _ := sum_subset hsub (by
      intro n hn hnsmall
      have hn1 := (mem_Icc.mp hn).1
      have hnot : ¬ a * n ≤ y := by
        intro h
        apply hnsmall
        exact mem_Icc.mpr ⟨hn1, (Nat.le_div_iff_mul_le ha0).mpr
          (by simpa only [Nat.mul_comm] using h)⟩
      simp only [if_neg hnot])

/-- Perron's formula for the complete source/prime amplitude, at Pan's line
and height, with an unconditional error uniform in the source and character. -/
theorem source_amplitude_perron {q x y : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (m L U : ℕ) (χ : PrimitiveCharacter q)
    (hx : 4 ≤ Real.log x) (hy : 1 ≤ y) (hyx : y ≤ x) (hUx : U ≤ x) :
    ‖panSourceCharacterAmplitude (panSourceG f m) (panSourceD m) y L U χ -
      liuPanTruncatedPerronIntegral (Ioc L U) (Icc 1 ⌊panSourceHeight x⌋₊)
        (panSourceG f m) (panSourceD m) χ.1
        (panSourceSigma x) (panSourceHeight x) y‖ ≤
      324 * ((x : ℝ) ^ 2)⁻¹ := by
  rw [source_amplitude_eq_hyperbola _ _ _ _ _ _ χ
    (hyx.trans (sourceHeight_floor_ge (by linarith)))]
  exact source_hyperbola_error_le _ _ _ _ χ.1
    (by intro a ha; have := mem_Ioc.mp ha; exact mem_Icc.mpr ⟨by omega, this.2.trans hUx⟩)
    (fun _ h => h) (fun _ _ => panSourceG_norm_le f hf _ _)
    (fun _ _ => panSourceD_norm_le _ _) hx hy hyx

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
