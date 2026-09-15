import Wu18938Campaign.M1.Confirmed.Omega2Errors

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical

def nodeMain {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, f (omega2ParameterTransform t
      (reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i (j + 1))) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ
      (Fin.cons (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V))

theorem raw_to_actual {m i N r : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hs : 0 < s)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    omega2GeometricRaw N δ Δ V t r ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) + reboxingR1 N δ Δ V t t 0 := by
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
    (fun d p => (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ))
  change _ = omega2GeometricRaw N δ Δ V t r at hpart
  rw [← hpart]
  unfold wuOmega2Sum wuOmega2 reboxingR1 reboxingBoundaryCount
  simp only [W,Nat.cast_zero,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t)
  let S := primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F := fun p => (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ)
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
  have hSsum : (∑ p ∈ S, F p) =
      ∑ p ∈ S, (sourceSieveCount N (d * p) (d * N) (wuLocalCutoff N δ d t) : ℝ) := by
    apply sum_congr rfl
    intro p hp
    dsimp [F]
    rw [omega2_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1
      (mem_primeWindow.mp hp).2.2.1]
  have hBsum : (∑ p ∈ B, F p) ≤
      ∑ p ∈ B, (sourceSieveCount N (d * p) (d * N) p : ℝ) := by
    apply sum_le_sum
    intro p hp
    have hwin := mem_primeWindow.mp hp
    rw [← reboxing_source_count_prime_modulus_eq N d hwin.1]
    exact gamma5Classical_source_count_antitone N (d * p) ((d * p) * N) hwin.2.2.2.le
  rw [hSsum] at hsum
  exact hsum.trans (add_le_add le_rfl hBsum)

theorem node_to_omega2 (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ,
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
        f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ U) v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        nodeMain f N δ Δ V t r -
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
          wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := cutoff_relative m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := boundary_relative m hη hδ (half_pos he)
  obtain ⟨T2,_,h2⟩ := scale m hη hδ
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f hnode s t hs hst ht ht5
  dsimp only
  obtain ⟨hΔ,_,hqlo,hq,hqN,hmesh⟩ := h2 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨r,hrlo,hrhi⟩ := reboxingAlpha_exists_terminal hq.le hΔ hs0 hst
  refine ⟨r,hrlo,hrhi,?_⟩
  let u := fun j : ℕ => omega2ParameterTransform t (reboxingS2 q Δ t i (j + 1))
  have hu : ∀ j ∈ range r, 1 ≤ u j ∧ u j ≤ 10 := by
    intro j hj
    have htop := ((reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hrlo
    have hd := reboxing_parameter_domain hq hΔ hs hst (by linarith : t ≤ 10)
      (show (1 : ℝ) ≤ j + 1 by have := Nat.cast_nonneg (α := ℝ) j; linarith) htop hmesh
    exact omega2ParameterTransform_domain ht ht5 hd.2.2.1
  have hblocks := block_lower hb (by omega) hη hΔ hqlo hqN hs hst (by linarith)
    f u r hrlo hnode hu
  change nodeMain f N δ Δ V t r ≤ reboxingGeometricCutoff N δ Δ V t r u at hblocks
  have hcut := (h0 N (by omega) heven i Δ V hb s t hs hst ht ht5 r hrlo).2
  have hr0 : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq0 (1 / t))
  have hboundary := h1 N (by omega) heven i Δ V hb t t (by linarith) le_rfl
    (by linarith) 0 hr0
  have hraw := raw_to_actual hb (by omega) hs0 hrlo
  rw [omega2GeometricRaw_eq_cutoff_sub_error] at hraw
  change reboxingGeometricCutoff N δ Δ V t r u - omega2CutoffError N δ Δ V t r ≤ _ at hraw
  linarith only [hblocks,hcut,hboundary,hraw]

end Wu18938Campaign.M1.Confirmed.Rebox
