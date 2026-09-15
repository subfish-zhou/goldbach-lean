import HighBoxRecoveryProfiles

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve
open scoped Classical
noncomputable section

/-- Balanced distribution actually consumed on the original labelled sequence.
Only prime-window and total-product geometry are input; no balanced hypothesis. -/
theorem R1_total_slack (k : ℕ) {δ η A : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ W : Fin i → Finset ℕ,
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ Z : ℝ,
      omega3SieveR1 N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) δ s t Z W ≤
        C * N / log (N : ℝ)^A := by
  let F : ℝ := (max 1 (1/η))^(k+2)
  let B : ℕ := ⌈F⌉₊
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨C,hC,T,hT4,hT⟩ := omega3_balanced_interval_distribution A η F hA hη hF hδ
  refine ⟨((B : ℝ)+1)*C,by positivity,T,hT4,?_⟩
  intro N hN i hik W hW hsize s t hs hst ht Z
  have hN4 := hT4.trans hN
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t := by
    intro d hd
    exact cutoff_lower (by omega)
      (boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd)
      hη (by linarith) ht (hsize d hd)
  let L := omega3CofactorLabels N δ s t W
  have hweight : ∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ F :=
    actual_fibre_weight W hik (by omega) hη hW hcut
  have hcard : ∀ e, (omega3LayerFibre L e).card ≤ B := by
    intro e
    exact_mod_cast (omega3_cofactor_fibre_card_le_weight N δ s t W e).trans
      ((hweight e).trans (Nat.le_ceil F))
  have hgeom := fun {c : Omega3CofactorIndex} (hc : c ∈ L) =>
    actual_profile W (show 2 ≤ N by omega) (fun j p hp => (hW j p hp).1) hcut hc
  have hbound : ∀ j : ℕ,
      (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z,
        (3 : ℝ)^q.primeFactors.card *
          |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
            omega3LayerCoefficient W L j e * omega3ProfileError N q e
              (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e)|) ≤
        C*N/log (N : ℝ)^A := by
    intro j
    apply hT N hN (omega3LayerSupport L j) (omega3LayerCoefficient W L j)
      (omega3LayerLower L j) (omega3LayerUpper N δ s L j)
    · intro e he
      have hl := omega3LayerLabel_mem he
      have hg := hgeom hl.1
      exact hl.2 ▸ ⟨hg.2.2.1,hg.2.2.2.1⟩
    · intro e _
      rw [abs_of_nonneg (omega3LayerCoefficient_nonneg W L j e)]
      exact omega3LayerCoefficient_le W L j e hF (hweight e)
    · intro e he
      have hl := omega3LayerLabel_mem he
      have hg := hgeom hl.1
      change 2 ≤ ((omega3LayerLabel L j e).2.1 : ℝ) ∧
        ((omega3LayerLabel L j e).2.1 : ℝ) ≤
          min ((N : ℝ)/e) (wuLocalCutoff N δ (omega3LayerLabel L j e).1 s) ∧
        (e : ℝ)*min ((N : ℝ)/e) (wuLocalCutoff N δ (omega3LayerLabel L j e).1 s) ≤ N
      simpa only [hl.2] using hg.2.2.2.2
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ ∑ j ∈ range B, ∑ q ∈ omega3SieveModuli N (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z,
        (3 : ℝ)^q.primeFactors.card *
          |∑ e ∈ (omega3LayerSupport L j).filter (fun e => e.Coprime q),
            omega3LayerCoefficient W L j e * omega3ProfileError N q e
              (omega3LayerLower L j e) (omega3LayerUpper N δ s L j e)| :=
      omega3SieveR1_le_layers W hcard (fun c hc => (hgeom hc).1)
    _ ≤ ∑ _j ∈ range B, C*N/log (N : ℝ)^A := sum_le_sum (fun j _ => hbound j)
    _ = (B : ℝ)*(C*N/log (N : ℝ)^A) := by simp
    _ ≤ ((B : ℝ)+1)*C*N/log (N : ℝ)^A := by
      calc
        _ ≤ ((B : ℝ)+1)*(C*N/log (N : ℝ)^A) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

/-- Actual full-cofactor R2 with an explicit positive-power saving. -/
theorem R2_total_slack (k : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ W : Fin i → Finset ℕ,
      (∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p) →
      (∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      let Q := (N : ℝ)^(1/2-δ)
      omega3SieveR2 N (⌊Q⌋₊+1) δ s t (sqrt Q) W ≤
        C * (max 1 (1/η))^(k+2) * N *
          ((1+log N)*log N^4 / ((N : ℝ)^η * log 2)) := by
  obtain ⟨C,hC,hEuler⟩ := omega3_non_coprime_euler_bound
  refine ⟨C,hC,?_⟩
  intro N hN i hik W hW hsize s t hs hst ht Q
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t := by
    intro d hd
    exact cutoff_lower (by omega)
      (boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd)
      hη (by linarith) ht (hsize d hd)
  have hg := omega3_source_sieve_geometry (show 2 ≤ N by omega) hδ hδhi
  apply hEuler N (by omega) i δ s t (sqrt Q) ((N : ℝ)^η)
    ((max 1 (1/η))^(k+2)) W _ hg.2.2.2.1 (by positivity) (by positivity)
    (filter_subset _ _)
  · intro q hq
    have hqd := (omega3SieveModuli_properties hq).2.2.2
    have hDN := hg.2.2.2.2.2.2.1
    dsimp [Q] at hqd
    omega
  · intro c hc
    have hp := actual_profile W (show 2 ≤ N by omega) (fun j p hp => (hW j p hp).1) hcut hc
    exact ⟨hp.1,hp.2.1,fun p hprime hpc => actual_prime_lower W hW hcut hc hprime hpc⟩
  · exact actual_fibre_weight W hik (by omega) hη hW hcut

end
end HighBoxRecovery
