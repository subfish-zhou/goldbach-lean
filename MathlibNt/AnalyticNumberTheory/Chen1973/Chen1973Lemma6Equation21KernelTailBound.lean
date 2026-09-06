import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21LogTailMoments
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation17KernelBounds

noncomputable section
open MeasureTheory Set Complex Real
open scoped BigOperators Topology
namespace AnalyticNumberTheory.LargeSieve

/-- Imaginary-part bounds retain the full true high-tail exponent. -/
theorem chen1973Lemma6_eq21_complexKernel_tail_bound
    {a t σ : ℝ} (ha : 0 < a) (ht : 0 < t) (N : ℕ) :
    ‖(1 : ℂ) / (((σ : ℂ) + t * I) *
      (1 + ((σ : ℂ) + t * I) / (a : ℂ)) ^ N)‖ ≤
      a ^ N / t ^ (N + 1) := by
  have hs : t ≤ ‖(σ : ℂ) + t * I‖ := by
    simpa [abs_of_pos ht] using Complex.abs_im_le_norm ((σ : ℂ) + t * I)
  have hw : t / a ≤ ‖1 + ((σ : ℂ) + t * I) / (a : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (1 + ((σ : ℂ) + t * I) / (a : ℂ))
    simpa [abs_of_pos (div_pos ht ha)] using h
  rw [norm_div, norm_one, norm_mul, norm_pow]
  calc
    _ ≤ 1 / (t * (t / a) ^ N) := by
      apply one_div_le_one_div_of_le (mul_pos ht (pow_pos (div_pos ht ha) _))
      exact mul_le_mul hs (pow_le_pow_left₀ (by positivity) hw N) (by positivity) (norm_nonneg _)
    _ = a ^ N / t ^ (N + 1) := by
      rw [div_pow, pow_succ]
      field_simp

/-- The genuine production kernel inherits the lossless high-tail estimate. -/
theorem chen1973Lemma6_eq21_mellinKernel_tail_bound
    {x : ℕ} (hx : 1 < x) {t σ : ℝ} (ht : 0 < t) :
    ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ ≤
      chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) /
        t ^ (chen1973PerronOrder (x : ℝ) + 2) := by
  unfold chen1973MellinKernel
  exact chen1973Lemma6_eq21_complexKernel_tail_bound
    (chen1973Lemma6_eq17_perronScale_pos hx) ht _

private theorem eq21_logWeight_tail_le {a d t : ℝ}
    (ha : 0 < a) (hd : 1 ≤ d) (ht : a ≤ t) :
    0 ≤ 1 + Real.log (d * (1 + t)) ∧
      1 + Real.log (d * (1 + t)) ≤
        (1 + Real.log (d * (1 + a))) + Real.log (t / a) := by
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hbase : 1 ≤ d * (1 + t) := by nlinarith
  have hratio : 1 + t ≤ (1 + a) * (t / a) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hprod : d * (1 + t) ≤ (d * (1 + a)) * (t / a) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hratio hd0.le
  have hlog := Real.log_le_log (mul_pos hd0 (by positivity)) hprod
  rw [Real.log_mul (ne_of_gt (mul_pos hd0 (by positivity)))
    (ne_of_gt (div_pos ht0 ha))] at hlog
  exact ⟨by linarith [Real.log_nonneg hbase], by linarith⟩

/-- Polynomial logarithmic weight on the actual production kernel's high tail. -/
theorem chen1973Lemma6_eq21_weightedKernel_tail_bound
    {x : ℕ} (hx : 1 < x) {d t σ : ℝ} (hd : 1 ≤ d)
    (ht : chen1973PerronScale (x : ℝ) ≤ t) (r : ℕ) :
    ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r ≤
      chen1973PerronScale (x : ℝ) ^ (chen1973PerronOrder (x : ℝ) + 1) /
        t ^ (chen1973PerronOrder (x : ℝ) + 2) *
          ((1 + Real.log (d * (1 + chen1973PerronScale (x : ℝ)))) +
            Real.log (t / chen1973PerronScale (x : ℝ))) ^ r := by
  have ha := chen1973Lemma6_eq17_perronScale_pos hx
  have hw := eq21_logWeight_tail_le ha hd ht
  exact mul_le_mul (chen1973Lemma6_eq21_mellinKernel_tail_bound hx (ha.trans_le ht))
    (pow_le_pow_left₀ hw.1 hw.2 r) (pow_nonneg hw.1 _)
    (div_nonneg (pow_nonneg ha.le _) (pow_nonneg (ha.trans_le ht).le _))

/-- The actual weighted Mellin kernel is integrable on its high tail, with
an explicit budget from the exact logarithmic moments. No integrability input
or zero-free/logarithmic-derivative premise is used in this kernel theorem. -/
theorem chen1973Lemma6_eq21_weightedKernel_tail_integrable_and_bound
    {x : ℕ} (hx : 1 < x) {d σ : ℝ} (hd : 1 ≤ d) (r : ℕ) :
    let a := chen1973PerronScale (x : ℝ)
    let N := chen1973PerronOrder (x : ℝ) + 1
    let D := 1 + Real.log (d * (1 + a))
    let f := fun t : ℝ =>
      ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
        (1 + Real.log (d * (1 + t))) ^ r
    IntegrableOn f (Ioi a) ∧
      (∫ t in Ioi a, f t) ≤
        ∑ j ∈ Finset.range (r + 1),
          (Nat.choose r j : ℝ) * D ^ (r - j) *
            ((Nat.factorial j : ℝ) / (N : ℝ) ^ (j + 1)) := by
  let a := chen1973PerronScale (x : ℝ)
  let N := chen1973PerronOrder (x : ℝ) + 1
  let D := 1 + Real.log (d * (1 + a))
  let f := fun t : ℝ =>
    ‖chen1973MellinKernel (x : ℝ) ((σ : ℂ) + t * I)‖ *
      (1 + Real.log (d * (1 + t))) ^ r
  let g := fun t : ℝ => a ^ N / t ^ (N + 1) * (D + Real.log (t / a)) ^ r
  change IntegrableOn f (Ioi a) ∧ (∫ t in Ioi a, f t) ≤ _
  have ha : 0 < a := chen1973Lemma6_eq17_perronScale_pos hx
  have hN : 0 < N := Nat.succ_pos _
  have hg : IntegrableOn g (Ioi a) :=
    chen1973Lemma6_eq21_shiftedLogTail_integrable ha D N r hN
  have hm : Measurable f := by
    dsimp [f]
    unfold chen1973MellinKernel
    fun_prop
  have hpoint : ∀ t ∈ Ioi a, 0 ≤ f t ∧ f t ≤ g t := by
    intro t ht
    have hw := eq21_logWeight_tail_le ha hd ht.le
    constructor
    · exact mul_nonneg (norm_nonneg _) (pow_nonneg hw.1 _)
    · simpa only [f, g, a, N, D, Nat.add_assoc] using
        chen1973Lemma6_eq21_weightedKernel_tail_bound (σ := σ) hx hd ht.le r
  have hpoint_ae : ∀ᵐ t ∂volume.restrict (Ioi a), 0 ≤ f t ∧ f t ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpoint t ht
  have hf : IntegrableOn f (Ioi a) :=
    hg.mono' hm.aestronglyMeasurable (hpoint_ae.mono fun t ht => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2)
  refine ⟨hf, ?_⟩
  calc
    (∫ t in Ioi a, f t) ≤ ∫ t in Ioi a, g t :=
      integral_mono_ae hf hg (hpoint_ae.mono fun _ ht => ht.2)
    _ = _ := chen1973Lemma6_eq21_shiftedLogTail_integral ha D N r hN

end AnalyticNumberTheory.LargeSieve