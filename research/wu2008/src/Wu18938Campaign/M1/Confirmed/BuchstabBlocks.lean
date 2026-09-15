import Wu18938Campaign.M1.Confirmed.BuchstabCutoff

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical

def upperMain {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  ∑ j ∈ range r, f (reboxingS1 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) *
    boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ
      (Fin.cons (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V))

theorem s1_le_t_sub_one {q Δ t j : ℝ} (hq : 1 < q) (hΔ : 1 < Δ)
    (ht : 0 < t) (hj : 0 ≤ j) : reboxingS1 q Δ t j ≤ t - 1 := by
  have hq0 : 0 < q := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have ha : q ^ (1 / t) ≤ reboxingAlpha q Δ t j := by
    simpa only [reboxingAlpha_zero] using (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone hj
  have ha1 := (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le ha
  rw [reboxingS1_formula hq0 hΔ0 ha1]
  apply sub_le_sub_right
  apply (div_le_iff₀ (log_pos ha1)).mpr
  have hh := log_le_log (rpow_pos_of_pos hq0 (1 / t)) ha
  rw [log_rpow hq0] at hh
  have hh' : log q / t ≤ log (reboxingAlpha q Δ t j) := by convert hh using 1; ring
  have hmul := (div_le_iff₀ ht).mp hh'
  nlinarith only [hmul]

theorem actual_to_raw {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (ht : 0 < t) (r : ℕ) :
    reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
      reboxingGeometricRaw N δ Δ V t r + reboxingR1 N δ Δ V s t r := by
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNr) (-4 : ℝ)
    linarith [hb.ratio_lower]
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) η).trans_le (hb.endpoint_lower l)
  have hQ : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hq : 0 < q := div_pos hQ (prod_pos (fun l _ => hV l))
  have hpart := reboxingAlpha_convolution_sum_partition (t := t) hq hΔ N r W
    (fun d p => (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ))
  change _ = reboxingGeometricRaw N δ Δ V t r at hpart
  rw [← hpart]
  unfold reboxingRawPrimeSum reboxingR1 reboxingBoundaryCount
  simp only [if_true,W,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  let A := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let B := primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s)
  let S := primeWindow (d * N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let F := fun p => (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ)
  have hlo := (reboxing_support_cutoff_bounds hQ.le (by linarith : 0 < Δ) hV ht hd).1
  have hsub : S ⊆ A ∪ B := by
    intro p hp
    obtain ⟨hpp,hpc,hpl,hpu⟩ := mem_primeWindow.mp hp
    have hpN := (Nat.coprime_mul_iff_right.mp hpc).2
    have hlow : reboxingAlpha q Δ t 0 ≤ (p : ℝ) := by
      rw [reboxingAlpha_zero]
      exact hlo.trans hpl
    by_cases hc : (p : ℝ) < reboxingAlpha q Δ t r
    · exact mem_union_left _ (mem_primeWindow.mpr ⟨hpp,hpN,hlow,hc⟩)
    · exact mem_union_right _ (mem_primeWindow.mpr ⟨hpp,hpN,le_of_not_gt hc,hpu⟩)
  have hdis : Disjoint A B := disjoint_left.mpr (fun p hp hp' =>
    (not_lt_of_ge (mem_primeWindow.mp hp').2.2.1) (mem_primeWindow.mp hp).2.2.2)
  have hsum : (∑ p ∈ S, F p) ≤ (∑ p ∈ A, F p) + ∑ p ∈ B, F p := by
    rw [← sum_union hdis]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    simp only [F,sourceSieveCount,Int.cast_natCast]
    positivity
  have hB : (∑ p ∈ B, F p) =
      ∑ p ∈ B, (sourceSieveCount N (d * p) (d * N) p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    dsimp [F]
    rw [reboxing_source_count_prime_modulus_eq N d (mem_primeWindow.mp hp).1]
  rwa [hB] at hsum

theorem upper_node_to_raw (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ (f : ℝ → ℝ) (vmax : ℝ),
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ vmax →
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v ≤
          f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → t - 1 ≤ vmax →
      let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
      ∃ r : ℕ, reboxingAlpha q Δ t r ≤ q ^ (1 / s) ∧
        q ^ (1 / s) < reboxingAlpha q Δ t (r + 1) ∧
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) ≤
          upperMain f N δ Δ V t r +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := buchstab_cutoff_relative m hη hδ (half_pos he)
  obtain ⟨T1,_,h1⟩ := boundary_relative m hη hδ (half_pos he)
  obtain ⟨T2,_,h2⟩ := scale m hη hδ
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f vmax hn s t hs hst ht htv
  dsimp only
  obtain ⟨hΔ,_,hqlo,hq,hqN,hmesh⟩ := h2 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hq0 : 0 < q := by dsimp [q]; linarith
  obtain ⟨r,hrlo,hrhi⟩ := reboxingAlpha_exists_terminal hq.le hΔ (by linarith : 0 < s) hst
  refine ⟨r,hrlo,hrhi,?_⟩
  have hcut : reboxingGeometricCutoff N δ Δ V t r (fun j => reboxingS1 q Δ t (j + 1)) ≤
      upperMain f N δ Δ V t r := by
    unfold reboxingGeometricCutoff upperMain
    apply sum_le_sum
    intro j hj
    have htop := ((reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hrlo
    have hdom := reboxing_parameter_domain hq hΔ hs hst ht
      (show (1 : ℝ) ≤ j + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]) htop hmesh
    have hchild := child hb (by omega) hη hΔ hqlo hqN hs hst ht j htop
    have hbound := hn (i + 1) (Fin.cons (reboxingAlpha q Δ t (j + 1)) V) hchild
      (reboxingS1 q Δ t (j + 1)) hdom.1
      ((s1_le_t_sub_one hq hΔ (by linarith) (by positivity)).trans htv)
    change (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ
        (Fin.cons (reboxingAlpha q Δ t (j + 1)) V)),
      (convolutionCoeff (convolutionWuWindows N Δ (Fin.cons (reboxingAlpha q Δ t (j + 1)) V)) d : ℝ) *
        (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d (reboxingS1 q Δ t (j + 1))) : ℝ)) ≤ _ at hbound
    rw [single_sum] at hbound
    simpa only [reboxingAlpha_previous (by linarith : 0 < Δ),add_sub_cancel_right] using hbound
  have hR2 := h0 N (by omega) heven i Δ V hb s t hs hst ht r hrlo
  have hR1 := h1 N (by omega) heven i Δ V hb s t hs hst ht r ⟨hrlo,hrhi⟩
  have hraw := actual_to_raw (s := s) hb (by omega) (by linarith : 0 < t) r
  rw [reboxingGeometricRaw_eq_s1_add_R2] at hraw
  linarith only [hcut,hR2,hR1,hraw]

end Wu18938Campaign.M1.Confirmed.Rebox
