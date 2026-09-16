import Wu18938Campaign.M1.Confirmed.ReverseErrors

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical

def lowerMain {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, f (reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i (j + 1)) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ
      (Fin.cons (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V))

theorem geometric_raw_to_unselected {m i N r : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hs : 0 < s)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    reboxingGeometricRaw N δ Δ V t r ≤
      reboxingRawPrimeSum false N δ s t (convolutionWuWindows N Δ V) +
        reboxingR1 N δ Δ V t t 0 := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos hL (-4 : ℝ)
    linarith [hb.ratio_lower]
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower l)
  have hQ : 0 < Q := rpow_pos_of_pos hN0 _
  have hq : 0 < q := div_pos hQ (prod_pos (fun l _ => hV l))
  have hpart := reboxingAlpha_convolution_sum_partition (t := t) hq hΔ N r W
    (fun d p => (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ))
  change _ = reboxingGeometricRaw N δ Δ V t r at hpart
  rw [← hpart]
  unfold reboxingRawPrimeSum reboxingR1 reboxingBoundaryCount
  simp only [Bool.false_eq_true,if_false,W,Nat.cast_zero,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t)
  let S := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F := fun p => (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ)
  have hupper := (reboxing_support_cutoff_bounds hQ.le (by linarith : 0 < Δ) hV hs hd).1
  have hsub : A ⊆ S ∪ B := by
    intro p hp
    obtain ⟨hpp,hpc,hpl,hpu⟩ := mem_primeWindow.mp hp
    by_cases hc : (p : ℝ) < wuLocalCutoff N δ d t
    · exact mem_union_right _ (mem_primeWindow.mpr ⟨hpp,hpc,hpl,hc⟩)
    · exact mem_union_left _ (mem_primeWindow.mpr
        ⟨hpp,hpc,le_of_not_gt hc,hpu.trans_le (hr.trans hupper)⟩)
  have hdis : Disjoint S B := Finset.disjoint_left.mpr (fun p hp hp' =>
    (not_lt_of_ge (mem_primeWindow.mp hp).2.2.1) (mem_primeWindow.mp hp').2.2.2)
  have hsum : (∑ p ∈ A, F p) ≤ (∑ p ∈ S, F p) + ∑ p ∈ B, F p := by
    rw [← sum_union hdis]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    simp only [F,sourceSieveCount,Int.cast_natCast]
    positivity
  have hBsum : (∑ p ∈ B, F p) =
      ∑ p ∈ B, (sourceSieveCount N (d * p) (d * N) p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    dsimp [F]
    rw [reboxing_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1]
  rwa [hBsum] at hsum

theorem lower_node_to_raw (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ,
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
        f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ U) v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        lowerMain f N δ Δ V t r -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) := by
  have he3 : 0 < ε / 3 := by positivity
  obtain ⟨T0,hT04,h0⟩ := reverse_cutoff_relative m hη hδ he3
  obtain ⟨T1,_,h1⟩ := boundary_relative m hη hδ he3
  obtain ⟨T2,_,h2⟩ := raw_modulus_relative m hη hδ he3
  obtain ⟨T3,_,h3⟩ := scale m hη hδ
  refine ⟨max T0 (max T1 (max T2 T3)),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f hn s t hs hst ht
  dsimp only
  obtain ⟨hΔ,_,hqlo,hq,hqN,hmesh⟩ := h3 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hq0 : 0 < q := by dsimp [q]; linarith
  obtain ⟨r,hrlo,hrhi⟩ := reboxingAlpha_exists_terminal hq.le hΔ (by linarith : 0 < s) hst
  refine ⟨r,hrlo,hrhi,?_⟩
  have hu (j : ℕ) (hj : j ∈ range r) :
      1 ≤ reboxingS2 q Δ t i (j + 1) ∧ reboxingS2 q Δ t i (j + 1) ≤ 10 := by
    have htop := ((reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hrlo
    exact (reboxing_parameter_domain hq hΔ hs hst ht
      (show (1 : ℝ) ≤ j + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]) htop hmesh).2.2
  have hcut := block_lower hb (by omega) hη hΔ hqlo hqN hs hst ht f
    (fun j => reboxingS2 q Δ t i (j + 1)) r hrlo hn hu
  have herror := h0 N (by omega) heven i Δ V hb s t hs hst ht r hrlo
  have hfinite := geometric_raw_to_unselected hb (by omega) (by linarith : 0 < s) hrlo
  have hzero : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq0 (1 / t))
  have hleft := h1 N (by omega) heven i Δ V hb t t (hs.trans hst) le_rfl ht 0 hzero
  have hrepeat := h2 N (by omega) heven i Δ V hb s t hs hst ht
  rw [reboxingGeometricRaw_eq_s2_sub_R2Reverse] at hfinite
  change lowerMain f N δ Δ V t r ≤ _ at hcut
  linarith only [hcut,herror,hfinite,hleft,hrepeat]

end Wu18938Campaign.M1.Confirmed.Rebox
