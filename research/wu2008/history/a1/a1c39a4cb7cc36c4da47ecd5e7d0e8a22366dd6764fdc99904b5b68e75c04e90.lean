import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientSourceGeometry
import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientDivisors

/-!
# The actual normalized source prime sum reaches a continuous integral

The threshold precedes N0, N and every source box. PNT quadrature, both
half-open endpoint cells and deletion of p dividing N are all consumed,
with the original same-fibre Theta and convolution multiplicities.
The logarithmic substitution is a separate exact identity.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def reboxingContinuousMain {i : ℕ} (upper : Bool) (k N0 N : ℕ)
    (δ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W,
      ((convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∫ x in (wuLocalCutoff N δ d t)..(wuLocalCutoff N δ d s),
        wuPrimeRealWeight (wuEffectiveCoefficient upper (k + 1) δ N0)
          ((N : ℝ) ^ (1 / 2 - δ) / d) x / log x

/-- A genuine normalized analytic source consumer with a single epsilon
budget and no hypotheses about the moving effective coefficient. -/
theorem wu_reboxing_continuous_integral_relative (upper : Bool) (k : ℕ)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N0 : ℕ, T ≤ N0 → ∀ N : ℕ, N0 ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
          (fun d p => wuEffectiveCoefficient upper (k + 1) δ N0
            (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) -
        reboxingContinuousMain upper k N0 N δ s t (convolutionWuWindows N Δ V)| ≤
      ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨Q0, _, hprime⟩ := primeCoefficient_source_continuous_uniform
    (show (0 : ℝ) ≤ 11 by norm_num) (half_pos hε)
  have heffective : ∀ᶠ N0 : ℕ in atTop,
      MonotoneOn (wuEffectiveCoefficient upper (k + 1) δ N0) (Set.Icc 1 10) ∧
      ∀ u ∈ Set.Icc (1 : ℝ) 10, |wuEffectiveCoefficient upper (k + 1) δ N0 u| ≤ 11 := by
    filter_upwards [wu_effective_threshold_uniform_monotone upper (k + 1) (by omega) hδ hδhi,
      wuEffectiveCoefficient_uniform_abs_le_eleven upper (k + 1) (by omega) hδ hδhi]
      with N0 hm hb
    exact ⟨hm, hb⟩
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp heffective
  obtain ⟨T2, hdelete⟩ :=
    wuEffectiveCoefficient_source_N_divisor_deletion upper k hδ hδhi (half_pos hε)
  have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (wuLocalExponent k δ)) atTop atTop :=
    (tendsto_rpow_atTop (wuLocalExponent_pos k hδ hδhi)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp (hgrow.eventually (eventually_ge_atTop Q0))
  refine ⟨max 4 (max T1 (max T2 T3)), le_max_left _ _, ?_⟩
  intro N0 hN0 N hN i Δ V hb s t hs hst ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans (hN0.trans hN)
  have hT1N0 : T1 ≤ N0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN0)
  have hT2N0 : T2 ≤ N0 := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN0))
  have hT3N : T3 ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (hN0.trans hN)))
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let f := wuEffectiveCoefficient upper (k + 1) δ N0
  have hf := hT1 N0 hT1N0
  have hgeom := fun d hd => wu_buchstab_prime_window_bounds (show 2 ≤ N by omega)
    hδ hδhi hb hs hst ht (d := d) hd
  have hpoint (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      |(∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          wuPrimeCoefficientWeight f (Q / d) p) -
        ∫ x in (wuLocalCutoff N δ d t)..(wuLocalCutoff N δ d s),
          wuPrimeRealWeight f (Q / d) x / log x| ≤ ε := by
    have hsp := wuLocal_support_bounds (show 1 ≤ N by omega) hδ hδhi
      hb.2.2.2.2.1 ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
    have hq0 : Q0 ≤ Q / d := (hT3 N hT3N).trans hsp.2.2
    have hp := hprime (Q / d) hq0 f hf.1 hf.2 s t hs hst ht
    have hdif := hdelete N0 hT2N0 N hN i Δ V hb s t hs hst ht d hd
    rw [abs_sub_comm] at hdif
    have h := (abs_sub_le
      (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        wuPrimeCoefficientWeight f (Q / d) p)
      (∑ p ∈ primeWindow 1 (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        wuPrimeCoefficientWeight f (Q / d) p)
      (∫ x in (wuLocalCutoff N δ d t)..(wuLocalCutoff N δ d s),
        wuPrimeRealWeight f (Q / d) x / log x)).trans (add_le_add hdif hp)
    linarith
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower hN4))
  let w : ℕ → ℝ := fun d => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
      ((Nat.totient d : ℝ) * log (Q / d))
  have hw (d : ℕ) (hd : d ∈ boxConvolutionSupport W) : 0 ≤ w d := by
    have h := hgeom d hd
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (wuSingularSeries_pos _ (Nat.mul_pos h.1 (by omega))).le)
      (mul_nonneg (Nat.cast_nonneg _) (log_pos h.2.2.1).le)
  unfold reboxingPrimeSum reboxingContinuousMain boxTheta
  simp only [Bool.false_eq_true, if_false]
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hli,
    mul_left_comm ε]
  apply mul_le_mul_of_nonneg_left _ hli
  simp only [← mul_sub]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport W, |w d *
        ((∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
          wuPrimeCoefficientWeight f (Q / d) p) -
        ∫ x in (wuLocalCutoff N δ d t)..(wuLocalCutoff N δ d s),
          wuPrimeRealWeight f (Q / d) x / log x)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport W, w d * ε := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, abs_of_nonneg (hw d hd)]
      exact mul_le_mul_of_nonneg_left (hpoint d hd) (hw d hd)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end Wu2008DoubleSieve
