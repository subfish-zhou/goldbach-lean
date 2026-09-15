import MathlibNt.Wu2008DoubleSieve.SingleUpperHPrimeQuadrature
import MathlibNt.Wu2008DoubleSieve.TruncatedElevenHPackedCount

namespace Wu2008DoubleSieve.SingleUpperHCoarseEnvelope
open Finset Set Real MeasureTheory SingleUpperHSource SingleUpperHIntegral
open SingleUpperHPacking SingleUpperHDarboux
open scoped Classical Topology

/-- A member below a fine-cell left endpoint is below its actual selected
predecessor. This statement refers to the inherited sample, not a replacement. -/
theorem le_sample_of_mem {Q : Finset ℝ} {q a : ℝ} (hq : q ∈ Q) (hqa : q ≤ a) :
    q ≤ sample Q a := by
  have hm : q ∈ Q.filter (fun t => t ≤ a) := mem_filter.mpr ⟨hq,hqa⟩
  have hn : (Q.filter (fun t => t ≤ a)).Nonempty := ⟨q,hm⟩
  unfold sample
  rw [dif_pos hn]
  exact le_max' _ _ hm

noncomputable def point (a h : ℝ) (i : ℕ) : ℝ := a+(i : ℝ)*h

@[simp] theorem point_zero (a h : ℝ) : point a h 0 = a := by simp [point]

theorem point_succ (a h : ℝ) (i : ℕ) : point a h (i+1) = point a h i+h := by
  simp only [point,Nat.cast_add,Nat.cast_one]
  ring

theorem point_mono {a h : ℝ} (hh : 0 ≤ h) : Monotone (point a h) := by
  intro i j hij
  change a+(i : ℝ)*h ≤ a+(j : ℝ)*h
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh)

/-- Pure covering, including both endpoints. The finite coarse family does
not depend on the arithmetic fine-grid cardinality. -/
theorem point_cover {a h t : ℝ} {n : ℕ} (_hh : 0 < h) (hn : 0 < n)
    (ht : a ≤ t) (htn : t ≤ point a h n) :
    ∃ i ∈ range n, point a h i ≤ t ∧ t ≤ point a h (i+1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact ⟨0,by simp,by simpa using ht,htn⟩
    · by_cases htn' : t ≤ point a h n
      · obtain ⟨i,hi,hlo,hhi⟩ := ih (by omega) htn'
        exact ⟨i,mem_range.mpr (by have := mem_range.mp hi; omega),hlo,hhi⟩
      · exact ⟨n,mem_range.mpr (by omega),(le_of_not_ge htn'),htn⟩

/-- Crossing one coarse boundary costs one predecessor lag, not continuity
of H. The anchor treats the first bin, even when the fine cell starts below it. -/
theorem lagged_sample_le {δ h a t : ℝ} {n i : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hh : 0 < h)
    (hn : point (truncatedSixthLowerAlpha/2) h n ≤ (1/2-δ)/2)
    (hi : i < n) (ha : truncatedSixthLowerAlpha/2 ≤ a)
    (hat : a ≤ t) (hstep : t-a ≤ h)
    (hti : point (truncatedSixthLowerAlpha/2) h i ≤ t)
    (hti1 : t ≤ point (truncatedSixthLowerAlpha/2) h (i+1)) :
    effective δ (argument δ (sample
      ((range (n+1)).image (point (truncatedSixthLowerAlpha/2) h)) a)) ≤
      effective δ (argument δ (point (truncatedSixthLowerAlpha/2) h (i-1))) := by
  let Q := (range (n+1)).image (point (truncatedSixthLowerAlpha/2) h)
  have hm := point_mono (a := truncatedSixthLowerAlpha/2) hh.le
  have hmem (j : ℕ) (hj : j ≤ n) : point (truncatedSixthLowerAlpha/2) h j ∈ Q :=
    mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩
  have hanchor : truncatedSixthLowerAlpha/2 ∈ Q := by simpa using hmem 0 (Nat.zero_le n)
  have hs := sample_mem_le hanchor ha
  have hq : point (truncatedSixthLowerAlpha/2) h (i-1) ≤ a := by
    by_cases hi0 : i = 0
    · subst i
      simpa using ha
    · have he := point_succ (truncatedSixthLowerAlpha/2) h (i-1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at he
      linarith
  have hqs := le_sample_of_mem (hmem (i-1) (by omega)) hq
  have hl : truncatedSixthLowerAlpha/2 ≤ point (truncatedSixthLowerAlpha/2) h (i-1) := by
    simpa using hm (Nat.zero_le (i-1))
  have hu : point (truncatedSixthLowerAlpha/2) h (i-1) ≤ (1/2-δ)/2 :=
    (hm (by omega)).trans hn
  have hsl : truncatedSixthLowerAlpha/2 ≤ sample Q a :=
    le_sample_of_mem hanchor ha
  have hsu : sample Q a ≤ (1/2-δ)/2 :=
    hs.2.trans (hat.trans (hti1.trans ((hm (by omega)).trans hn)))
  exact effective_argument_antitone hδ hδhi ⟨hl,hu⟩ ⟨hsl,hsu⟩ hqs

/-- The two-step variation sum is at most twice the total variation. -/
theorem lag_variation_sum {v : ℕ → ℝ} {n : ℕ} (hv : v n ≤ v (n-1)) :
    (∑ i ∈ range n, (v (i-1)-v (i+1))) ≤ 2*(v 0-v n) := by
  have hs : (∑ i ∈ range n, (v (i-1)-v (i+1))) =
      (∑ i ∈ range n, (v (i-1)-v i)) + (v 0-v n) := by
    calc
      _ = (∑ i ∈ range n, ((v (i-1)-v i)+(v i-v (i+1)))) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [sum_add_distrib,sum_range_sub']
  rw [hs]
  have ht : (∑ i ∈ range n, (v (i-1)-v i)) = v 0-v (n-1) := by
    clear hs hv
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [Nat.add_sub_cancel]
      ring
  rw [ht]
  linarith only [hv]

/-- A sampled weighted cell is controlled by endpoint variation on a larger
interval. This permits a predecessor lying before the cell itself. -/
theorem sampled_weighted_cell {f w : ℝ → ℝ} {u a b v W : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hbv : b ≤ v)
    (hf : AntitoneOn f (Icc u v)) (hw : ContinuousOn w (Icc u v))
    (hw0 : ∀ t ∈ Icc u v, 0 ≤ w t) (hwW : ∀ t ∈ Icc u v, w t ≤ W) :
    f u*(∫ t in a..b, w t) - (∫ t in a..b, f t*w t) ≤
      W*(b-a)*(f u-f v) := by
  have huv := hua.trans (hab.trans hbv)
  have hs : uIcc a b ⊆ Icc u v := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc hua hbv
  have hwi := (hw.mono hs).intervalIntegrable (μ := volume)
  have hfi := (hf.mono hs).intervalIntegrable (μ := volume)
  have hei := ((intervalIntegrable_const (c := f u)).sub hfi).mul_continuousOn (hw.mono hs)
  have heq : f u*(∫ t in a..b, w t) - (∫ t in a..b, f t*w t) =
      ∫ t in a..b, (f u-f t)*w t := by
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub (hwi.const_mul _) (hfi.mul_continuousOn (hw.mono hs)),
      intervalIntegral.integral_const_mul]
  rw [heq]
  have hd := sub_nonneg.mpr (hf ⟨le_rfl,huv⟩ ⟨huv,le_rfl⟩ huv)
  have hm := intervalIntegral.integral_mono_on hab hei
    (intervalIntegrable_const (c := (f u-f v)*W)) (fun t ht => by
      have ht' : t ∈ Icc u v := ⟨hua.trans ht.1,ht.2.trans hbv⟩
      have hfuv := hf ht' ⟨huv,le_rfl⟩ ht'.2
      exact mul_le_mul (by linarith : f u-f t ≤ f u-f v) (hwW t ht') (hw0 t ht') hd)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hm
  nlinarith only [hm]

/-- Clipping the partition below a fixed overhang endpoint does not destroy
the two-step variation estimate. Zero-width bins remain present. -/
theorem clipped_lag_darboux {f w : ℝ → ℝ} {x : ℕ → ℝ} {n : ℕ} {d W h : ℝ}
    (hx : Monotone x) (hd : x 0 ≤ d) (hdn : d ≤ x n)
    (hf : AntitoneOn f (Icc (x 0) (x n)))
    (hw : ContinuousOn w (Icc (x 0) (x n)))
    (hw0 : ∀ t ∈ Icc (x 0) (x n), 0 ≤ w t)
    (hwW : ∀ t ∈ Icc (x 0) (x n), w t ≤ W)
    (hW : 0 ≤ W) (hh : 0 ≤ h) (hmesh : ∀ i < n, x (i+1)-x i ≤ h) :
    (∑ i ∈ range n, f (x (i-1)) * ∫ t in max d (x i)..max d (x (i+1)), w t) -
      (∫ t in d..x n, f t*w t) ≤ 2*W*h*(f (x 0)-f (x n)) := by
  let z := fun i => max d (x i)
  have hz : Monotone z := fun i j hij => max_le_max le_rfl (hx hij)
  have hz0 : z 0 = d := max_eq_left hd
  have hzn : z n = x n := max_eq_right hdn
  have hzi (i : ℕ) (hi : i ≤ n) : z i ∈ Icc (x 0) (x n) :=
    ⟨hd.trans (le_max_left _ _),max_le hdn (hx hi)⟩
  have hxi (i : ℕ) (hi : i ≤ n) : x i ∈ Icc (x 0) (x n) :=
    ⟨hx (Nat.zero_le _),hx hi⟩
  have hwi (i : ℕ) (hi : i < n) : IntervalIntegrable (fun t => f t*w t) volume (z i) (z (i+1)) := by
    have hs : uIcc (z i) (z (i+1)) ⊆ Icc (x 0) (x n) := by
      rw [uIcc_of_le (hz (by omega))]
      exact Icc_subset_Icc (hzi i (by omega)).1 (hzi (i+1) (by omega)).2
    exact ((hf.mono hs).intervalIntegrable).mul_continuousOn (hw.mono hs)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hwi
  rw [hz0,hzn] at hsplit
  change (∑ i ∈ range n, f (x (i-1)) * ∫ t in z i..z (i+1), w t) - _ ≤ _
  rw [← hsplit,← sum_sub_distrib]
  have hb : (∑ i ∈ range n, (f (x (i-1)) * (∫ t in z i..z (i+1), w t) -
      (∫ t in z i..z (i+1), f t*w t))) ≤
      ∑ i ∈ range n, W*h*(f (x (i-1))-f (x (i+1))) := by
    apply sum_le_sum
    intro i hi
    have hin := mem_range.mp hi
    have hdiff : 0 ≤ f (x (i-1))-f (x (i+1)) := sub_nonneg.mpr
      (hf (hxi (i-1) (by omega)) (hxi (i+1) (by omega)) (hx (by omega)))
    by_cases hdi : x (i+1) ≤ d
    · have hzj : z (i+1) = d := max_eq_left hdi
      have hzi' : z i = d := max_eq_left ((hx (by omega)).trans hdi)
      rw [hzi',hzj]
      simp only [intervalIntegral.integral_same,mul_zero,sub_self]
      exact mul_nonneg (mul_nonneg hW hh) hdiff
    · have hdj : d ≤ x (i+1) := (lt_of_not_ge hdi).le
      have hsub : Icc (x (i-1)) (x (i+1)) ⊆ Icc (x 0) (x n) :=
        Icc_subset_Icc (hx (Nat.zero_le _)) (hx (by omega))
      have hc := sampled_weighted_cell ((hx (by omega : i-1 ≤ i)).trans (le_max_right d (x i)))
        (hz (by omega : i ≤ i+1)) (max_le hdj le_rfl)
        (hf.mono hsub) (hw.mono hsub) (fun t ht => hw0 t (hsub ht))
        (fun t ht => hwW t (hsub ht))
      have hwidth : z (i+1)-z i ≤ h := by
        have hzj : z (i+1) = x (i+1) := max_eq_right hdj
        rw [hzj]
        have hzlo : x i ≤ z i := le_max_right _ _
        linarith [hmesh i hin]
      exact hc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hW) hdiff)
  apply hb.trans
  rw [← mul_sum]
  have hl := lag_variation_sum (v := fun i => f (x i))
    (hf (hxi (n-1) (by omega)) (hxi n le_rfl) (hx (by omega)))
  have hp := mul_le_mul_of_nonneg_left hl (mul_nonneg hW hh)
  nlinarith only [hp]

end Wu2008DoubleSieve.SingleUpperHCoarseEnvelope
