import InsertedO2Local

namespace InsertedO2
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2 HighO2Terminal
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- The nonnegative absolute AP kernel regroups over one labelled product.
For the actual Fin3 base, this carrier has four labels, with all multiplicities. -/
theorem selected_ap {i N Q : ℕ} {δ s t : ℝ} (W : Fin i → Finset ℕ)
    (hN : 2 ≤ N) (hδ : 0 ≤ δ)
    (hW : ∀ j p, p ∈ W j → p.Prime)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta))
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)*
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), apAtom N Q (d*p)) ≤
    convolutionAPError N Q (Fin.cons (apPrimeCover N) W) := by
  rw [convolutionAPError_eq_support_sum]
  change _ ≤ ∑ m ∈ boxConvolutionSupport (Fin.cons (apPrimeCover N) W),
    (convolutionCoeff (Fin.cons (apPrimeCover N) W) m : ℝ)*apAtom N Q m
  rw [boxConvolution_sum_cons]
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpN := selected_subset_original N d _ _ hp
    have hd0 := boxConvolutionSupport_pos (fun j q hq => (hW j q hq).pos) hd
    have hg := full_prime_half_gap hN hδ hd0 (hsize d hd) hs ht ht5 hpN
    have hh := mem_primeWindow.mp hpN
    exact mem_primeWindow.mpr ⟨hh.1,hh.2.1,hg.1,by linarith [hg.2.1]⟩
  · intro p _ _
    exact apAtom_nonneg _ _ _

/-- Complete prime lower under genuine total-product slack; no subwindow,
grid, cover hypothesis or source-Uk admission appears. -/
theorem prime_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ i : ℕ,
      ∀ W : Fin i → Finset ℕ, (∀ j p, p ∈ W j → p.Prime) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*highEta)) →
      ∀ s t : ℝ, 2 ≤ s → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      reboxingPrimeSum true N δ s t W (fun d p => logCoefficient ε (ratio N d p δ t)) -
        convolutionAPError N (convolutionModulusCutoff N δ) (Fin.cons (apPrimeCover N) W) ≤
      wuOmega2Sum N δ s t W := by
  obtain ⟨T,hT4,hcount⟩ := selected_atom hδ hε hε1
  refine ⟨T,hT4,?_⟩
  intro N hN he i W hW hsize s t hs ht ht5 hc
  let P := fun d => primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let A := fun d p : ℕ => (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
    log ((N : ℝ)^(1/2-δ)/d)))*(logCoefficient ε (ratio N d p δ t)/
    (((p : ℝ)-2)*(1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d))))
  let E := fun d p : ℕ => apAtom N (convolutionModulusCutoff N δ) (d*p)
  have ha : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P d,
      A d p-E d p ≤ (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) := by
    intro d hd
    exact hcount N hN he d (boxConvolutionSupport_pos (fun j q hq => (hW j q hq).pos) hd)
      (hsize d hd) s t hs ht ht5 hc
  have hsum : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)*
      ∑ p ∈ P d, (A d p-E d p)) ≤ wuOmega2Sum N δ s t W := by
    apply sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply le_trans (sum_le_sum (ha d hd))
    apply sum_le_sum_of_subset_of_nonneg (selected_subset_original N d _ _)
    intro p _ _
    exact Nat.cast_nonneg _
  have hmain : reboxingPrimeSum true N δ s t W (fun d p => logCoefficient ε (ratio N d p δ t)) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ)*∑ p ∈ P d, A d p := by
    unfold reboxingPrimeSum
    simp only [if_true,mul_sum]
    apply sum_congr rfl
    intro d hd
    apply sum_congr rfl
    intro p hp
    dsimp [A]
    ring
  have hap := selected_ap (Q := convolutionModulusCutoff N δ) W
    (show 2 ≤ N by have := hT4.trans hN; omega) hδ hW hsize hs ht ht5
  rw [hmain]
  apply le_trans (sub_le_sub_left hap _)
  simpa only [sum_sub_distrib,mul_sub] using hsum

/-- Four-label BV, paid once, uniformly over every ActualInsertion. -/
theorem inserted_AP_paid {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ U : ℝ, ActualInsertion N δ Δ U V →
      convolutionAPError N (convolutionModulusCutoff N δ)
        (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ (Fin.cons U V))) ≤
        C*N/log (N : ℝ)^(18 : ℝ) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨C,hC,T0,hBV⟩ := convolution_bombieri_vinogradov 4 hη hδ (show (0 : ℝ) < 18 by norm_num)
  obtain ⟨T1,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN Δ hlo hhi V hV hr U hU
  have hN4 : 4 ≤ N := by omega
  have hN0 : T0 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  obtain ⟨hΔ,hΔhi⟩ := hsmall N hN1 Δ hlo hhi
  have hg := inserted_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr hU
  apply hBV N hN0 4 le_rfl
  intro j p hp
  revert hp
  refine Fin.cases ?_ (fun j => ?_) j
  · intro hp
    have hh := mem_primeWindow.mp hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  · intro hp
    exact ⟨(hg.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hg.1 j p hp).2⟩

end
end InsertedO2
