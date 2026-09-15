import MathlibNt.Wu2008DoubleSieve.SingleUpperHIntegral

namespace Wu2008DoubleSieve.SingleUpperHDarboux
open Finset Set Real MeasureTheory SingleUpperHSource SingleUpperHIntegral
open scoped Classical Topology

/-- The weighted upper cell error uses only antitonicity of the effective
coefficient. In particular it makes no continuity assertion about H. -/
theorem antitone_weighted_cell {f w : ℝ → ℝ} {a b W : ℝ}
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hwW : ∀ t ∈ Icc a b, w t ≤ W) :
    0 ≤ f a * (∫ t in a..b, w t) - ∫ t in a..b, f t*w t ∧
    f a * (∫ t in a..b, w t) - ∫ t in a..b, f t*w t ≤
      W*(b-a)*(f a-f b) := by
  have hwi : IntervalIntegrable w volume a b :=
    (hw.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hfi : IntervalIntegrable f volume a b :=
    (hf.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  have hfwi := hfi.mul_continuousOn (hw.mono (by rw [uIcc_of_le hab]))
  have hei : IntervalIntegrable (fun t => (f a-f t)*w t) volume a b :=
    (intervalIntegrable_const.sub hfi).mul_continuousOn
      (hw.mono (by rw [uIcc_of_le hab]))
  have heq : f a * (∫ t in a..b, w t) - ∫ t in a..b, f t*w t =
      ∫ t in a..b, (f a-f t)*w t := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hwi.const_mul _) hfwi,
      intervalIntegral.integral_const_mul]
  rw [heq]
  have hm (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ f a-f t ∧ f a-f t ≤ f a-f b := by
    have h1 := hf ⟨le_rfl,hab⟩ ht ht.1
    have h2 := hf ht ⟨hab,le_rfl⟩ ht.2
    constructor <;> linarith
  refine ⟨intervalIntegral.integral_nonneg hab (fun t ht => mul_nonneg (hm t ht).1 (hw0 t ht)),?_⟩
  have h := intervalIntegral.integral_mono_on hab hei
    (intervalIntegrable_const (c := (f a-f b)*W)) (fun t ht =>
      mul_le_mul (hm t ht).2 (hwW t ht) (hw0 t ht)
        (sub_nonneg.mpr (hf ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab)))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  nlinarith only [h]

/-- A finite-partition Darboux error telescopes by variation, not by a
Lipschitz bound. The partition can be fixed before any arithmetic scale. -/
theorem antitone_weighted_partition {f w : ℝ → ℝ} {x : ℕ → ℝ} {n : ℕ} {W h : ℝ}
    (hx : Monotone x) (hf : AntitoneOn f (Icc (x 0) (x n)))
    (hw : ContinuousOn w (Icc (x 0) (x n)))
    (hw0 : ∀ t ∈ Icc (x 0) (x n), 0 ≤ w t)
    (hwW : ∀ t ∈ Icc (x 0) (x n), w t ≤ W)
    (hW : 0 ≤ W) (hmesh : ∀ i < n, x (i+1)-x i ≤ h) :
    (∑ i ∈ range n, f (x i) * ∫ t in x i..x (i+1), w t) -
      (∫ t in x 0..x n, f t*w t) ≤ W*h*(f (x 0)-f (x n)) := by
  have hsub (i : ℕ) (hi : i < n) : Icc (x i) (x (i+1)) ⊆ Icc (x 0) (x n) :=
    Icc_subset_Icc (hx (Nat.zero_le i)) (hx (by omega))
  have hwi (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun t => f t*w t) volume (x i) (x (i+1)) := by
    have hs : uIcc (x i) (x (i+1)) ⊆ Icc (x 0) (x n) := by
      rw [uIcc_of_le (hx (by omega))]
      exact hsub i hi
    exact ((hf.mono hs).intervalIntegrable).mul_continuousOn (hw.mono hs)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hwi, ← sum_sub_distrib]
  have hbound : (∑ i ∈ range n,
      (f (x i) * (∫ t in x i..x (i+1), w t) - (∫ t in x i..x (i+1), f t*w t))) ≤
      ∑ i ∈ range n, W*h*(f (x i)-f (x (i+1))) := by
    apply sum_le_sum
    intro i hi
    have hin := mem_range.mp hi
    have hc := (antitone_weighted_cell (hx (by omega)) (hf.mono (hsub i hin))
      (hw.mono (hsub i hin)) (fun t ht => hw0 t (hsub i hin ht))
      (fun t ht => hwW t (hsub i hin ht))).2
    have hd : 0 ≤ f (x i)-f (x (i+1)) := sub_nonneg.mpr
      (hf ⟨hx (Nat.zero_le i),hx (by omega)⟩
        ⟨hx (Nat.zero_le _),hx (by omega)⟩ (hx (by omega)))
    exact hc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmesh i hin) hW) hd)
  refine hbound.trans_eq ?_
  rw [← mul_sum, sum_range_sub']

/-- On the full legal coarse slab the original reciprocal kernel is positive
and bounded. This bound also covers the lower overhang. -/
theorem reciprocal_bounds {δ t : ℝ} (hδhi : δ ≤ 1/100)
    (ht : truncatedSixthLowerAlpha/2 ≤ t) (htHi : t ≤ (1/2-δ)/2) :
    0 ≤ (t*((1/2-δ)-t))⁻¹ ∧ (t*((1/2-δ)-t))⁻¹ ≤ 200 := by
  have ht0 : (1/30 : ℝ) ≤ t := by
    norm_num [truncatedSixthLowerAlpha] at ht ⊢
    linarith
  have hd : (1/5 : ℝ) ≤ (1/2-δ)-t := by linarith
  have hp : (1/150 : ℝ) ≤ t*((1/2-δ)-t) := by
    have hh := mul_le_mul ht0 hd (by norm_num : (0 : ℝ) ≤ 1/5) (by linarith : 0 ≤ t)
    norm_num at hh
    exact hh
  constructor
  · exact inv_nonneg.mpr (by linarith)
  · apply (inv_le_comm₀ (by linarith) (by norm_num : (0 : ℝ) < 200)).mpr
    norm_num
    linarith

/-- Genuine effective weighted Darboux bound; the source coefficient is
literal A-H and the reciprocal weight is the original t(c-t) kernel. -/
theorem effective_partition {δ : ℝ} {x : ℕ → ℝ} {n : ℕ} {h : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hx : Monotone x)
    (ha : truncatedSixthLowerAlpha/2 ≤ x 0) (hb : x n ≤ (1/2-δ)/2)
    (hmesh : ∀ i < n, x (i+1)-x i ≤ h) :
    (∑ i ∈ range n, effective δ (argument δ (x i)) *
      ∫ t in x i..x (i+1), (t*((1/2-δ)-t))⁻¹) -
      (∫ t in x 0..x n, effectiveKernel δ t) ≤
      200*h*(effective δ (argument δ (x 0))-effective δ (argument δ (x n))) := by
  have hs : Icc (x 0) (x n) ⊆ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2) :=
    Icc_subset_Icc ha hb
  have hc := reciprocal_continuous hδhi ha (hx (Nat.zero_le n)) hb
  rw [uIcc_of_le (hx (Nat.zero_le n))] at hc
  simpa only [effectiveKernel,div_eq_mul_inv] using
    antitone_weighted_partition hx ((effective_argument_antitone hδ hδhi).mono hs) hc
      (fun t ht => (reciprocal_bounds hδhi (hs ht).1 (hs ht).2).1)
      (fun t ht => (reciprocal_bounds hδhi (hs ht).1 (hs ht).2).2)
      (by norm_num : (0 : ℝ) ≤ 200) hmesh

end Wu2008DoubleSieve.SingleUpperHDarboux
