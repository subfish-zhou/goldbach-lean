import HighO2TerminalLocal

namespace HighO2Terminal
open Finset Real Filter Wu2008DoubleSieve HighTheta HighBoxRecovery HighOmega2
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
noncomputable section

/-- A single complete large-prime carrier for the absolute AP error.
It is not an Omega2 approximation or a new splitting point. -/
def apPrimeCover (N : ℕ) : Finset ℕ := primeWindow N ((N : ℝ)^highEta) ((N : ℝ)+1)

theorem selected_subset_original (N d : ℕ) (z w : ℝ) :
    primeWindow (d*N) z w ⊆ primeWindow N z w := by
  intro p hp
  obtain ⟨hpp,hpc,hlo,hhi⟩ := mem_primeWindow.mp hp
  exact mem_primeWindow.mpr ⟨hpp,(Nat.coprime_mul_iff_right.mp hpc).2,hlo,hhi⟩

/-- Exact AP fibre regrouping, then restriction only of its nonnegative
absolute kernel. No signed Rosser remainder is restricted. -/
theorem selected_ap_le {N Q : ℕ} {δ Δ s t : ℝ} {V : Fin 2 → ℝ}
    (hN : 2 ≤ N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hΔ : 0 < Δ)
    (hV : ∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) (hr : OriginalRectangles N V)
    (hs : 2 ≤ s) (ht : 3 ≤ t) (ht5 : t ≤ 5) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ)*
      ∑ p ∈ primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), apAtom N Q (d*p)) ≤
    convolutionAPError N Q (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ V)) := by
  rw [convolutionAPError_eq_support_sum]
  change _ ≤ ∑ m ∈ boxConvolutionSupport (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ V)),
    (convolutionCoeff (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ V)) m : ℝ)*apAtom N Q m
  rw [boxConvolution_sum_cons]
  apply sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpN := selected_subset_original N d _ _ hp
    have hg := full_prime_geometry hN hδ hδhi hΔ hV hr hd hs ht ht5 hpN
    have hh := mem_primeWindow.mp hpN
    exact mem_primeWindow.mpr ⟨hh.1,hh.2.1,hg.1,by linarith [hg.2.1]⟩
  · intro p _ _
    exact apAtom_nonneg _ _ _

/-- Complete actual Omega2 lower after normalization, with precisely one
large three-label AP error. All nonselected primes remain in Omega2. -/
theorem original_prime_lower {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 50*highEta) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ Δ : ℝ, 0 < Δ →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → 2 ≤ t-t/s →
      reboxingPrimeSum true N δ s t (convolutionWuWindows N Δ V)
        (fun d p => logCoefficient ε (ratio N d p δ t)) -
      convolutionAPError N (convolutionModulusCutoff N δ)
        (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ V)) ≤
      wuOmega2Sum N δ s t (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,hT⟩ := original_atom_lower hδ hδhi hε hε1
  refine ⟨T,hT4,?_⟩
  intro N hN he Δ hΔ V hV hr s t hs hst ht ht5 hc
  let W := convolutionWuWindows N Δ V
  let P := fun d => primeWindow (d*N) (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)
  let A := fun d p : ℕ => (4*logarithmicIntegral N)*(wuSingularSeries (d*N)/((Nat.totient d : ℝ)*
    log ((N : ℝ)^(1/2-δ)/d)))*(logCoefficient ε (ratio N d p δ t)/
    (((p : ℝ)-2)*(1-log (p : ℝ)/log ((N : ℝ)^(1/2-δ)/d))))
  let E := fun d p : ℕ => apAtom N (convolutionModulusCutoff N δ) (d*p)
  have ha : ∀ d ∈ boxConvolutionSupport W, ∀ p ∈ P d,
      A d p-E d p ≤ (sourceSieveCount N (d*p) (d*N) (wuLocalCutoff N δ d t) : ℝ) :=
    hT N hN he Δ hΔ V hV hr s t hs hst ht ht5 hc
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
  have hap := selected_ap_le (Q := convolutionModulusCutoff N δ) (hT4.trans hN |>.trans' (by norm_num : 2 ≤ 4))
    hδ hδhi hΔ hV hr hs ht ht5
  rw [hmain]
  apply le_trans (sub_le_sub_left hap _)
  simpa only [sum_sub_distrib,mul_sub] using hsum

/-- One actual three-prime BV payment, not one payment per grid cell. -/
theorem original_AP_paid {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 50*highEta) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ,
      1+log (N : ℝ)^(-4 : ℝ) ≤ Δ → Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ V : Fin 2 → ℝ, (∀ j, (N : ℝ)^(100/1327 : ℝ) ≤ V j) → OriginalRectangles N V →
      convolutionAPError N (convolutionModulusCutoff N δ)
        (Fin.cons (apPrimeCover N) (convolutionWuWindows N Δ V)) ≤ C*N/log (N : ℝ)^(18 : ℝ) := by
  have hη : 0 < highEta := by norm_num [highEta]
  obtain ⟨C,hC,T0,hBV⟩ := convolution_bombieri_vinogradov 3 hη hδ (show (0 : ℝ) < 18 by norm_num)
  obtain ⟨T1,hsmall⟩ := eventually_atTop.mp delta_eventually_small
  refine ⟨C,hC,max 4 (max T0 T1),le_max_left _ _,?_⟩
  intro N hN Δ hlo hhi V hV hr
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hΔ,hΔhi⟩ := hsmall N ((le_max_right T0 T1).trans ((le_max_right _ _).trans hN)) Δ hlo hhi
  have hg := original_box_geometry (show 2 ≤ N by omega) hδhi hΔ hΔhi hV hr
  apply hBV N ((le_max_left T0 T1).trans ((le_max_right _ _).trans hN)) 3 le_rfl
  intro j p hp
  revert hp
  refine Fin.cases ?_ (fun j => ?_) j
  · intro hp
    have hh := mem_primeWindow.mp hp
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  · intro hp
    exact ⟨(hg.1 j p hp).1,(mem_convolutionWuWindows.mp hp).2.1,(hg.1 j p hp).2⟩

end
end HighO2Terminal
