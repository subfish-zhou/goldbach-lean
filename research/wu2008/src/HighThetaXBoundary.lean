import HighThetaPhiEndpoint

namespace HighTheta
open Finset Real Wu2008DoubleSieve HighBoxRecovery
open scoped Classical
noncomputable section

/-- Full strict prime-count centre with the original coprime-to-N restriction. -/
def strictX {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ c ∈ omega3CofactorLabels N δ s t W,
    (convolutionCoeff W c.1 : ℝ)*(omega3CofactorPrimeFibre N δ s c).card

/-- All lost primes are either genuine divisors of N or the upper endpoint. -/
theorem prime_fibre_boundary_subset {N : ℕ} {δ s : ℝ} {c : Omega3CofactorIndex}
    (hN : 0 < N) :
    omega3CofactorPrimeFibreLE N δ s c \ omega3CofactorPrimeFibre N δ s c ⊆
      N.primeFactors ∪ {⌈wuLocalCutoff N δ c.1 s⌉₊} := by
  intro p hp
  obtain ⟨hclosed,hnot⟩ := mem_sdiff.mp hp
  obtain ⟨_,hprime,hlow,hupper,hsize⟩ := mem_filter.mp hclosed
  by_cases hcop : p.Coprime N
  · apply mem_union_right
    have hnotlt : ¬ (p : ℝ) < wuLocalCutoff N δ c.1 s := by
      intro hlt
      apply hnot
      exact mem_filter.mpr ⟨mem_primeWindow.mpr ⟨hprime,hcop,by exact_mod_cast hlow.le,hlt⟩,hlow,hsize⟩
    have heq : wuLocalCutoff N δ c.1 s = (p : ℝ) := le_antisymm (le_of_not_gt hnotlt) hupper
    simp only [heq, Nat.ceil_natCast, mem_singleton]
  · apply mem_union_left
    exact Nat.mem_primeFactors.mpr ⟨hprime, (Classical.not_not.mp (hprime.coprime_iff_not_dvd.not.mp hcop)), hN.ne'⟩

/-- Both endpoints and coprimality corrections are retained, with one
convolution weight per label. -/
theorem prime_fibre_boundary_card {N : ℕ} {δ s : ℝ} {c : Omega3CofactorIndex}
    (hN : 0 < N) (he : 0 < omega3CofactorValue c) :
    0 ≤ ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) -
      (omega3CofactorPrimeFibre N δ s c).card ∧
    ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) -
      (omega3CofactorPrimeFibre N δ s c).card ≤ (N.primeFactors.card : ℝ)+1 := by
  have hsub := omega3_prime_fibre_subset_closed (N := N) (δ := δ) (s := s) he
  have hc := card_le_card (prime_fibre_boundary_subset (δ := δ) (s := s) (c := c) hN)
  have hu := card_union_le N.primeFactors {⌈wuLocalCutoff N δ c.1 s⌉₊}
  rw [card_sdiff_of_subset hsub] at hc
  simp only [card_singleton] at hu
  have hle := card_le_card hsub
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast hle)
  · have hnat : (omega3CofactorPrimeFibreLE N δ s c).card ≤
        (omega3CofactorPrimeFibre N δ s c).card + N.primeFactors.card + 1 := by omega
    have hr : ((omega3CofactorPrimeFibreLE N δ s c).card : ℝ) ≤
        (omega3CofactorPrimeFibre N δ s c).card + N.primeFactors.card + 1 := by exact_mod_cast hnat
    linarith

/-- Weighted label count, using the full-cofactor fibre and actual size gap.
This does not collapse equal cofactor labels to unit weight. -/
theorem cofactor_label_weight_bound {i k N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hik : i ≤ k) (hN : 2 ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (ht : 0 < t) (htop : t ≤ 10) :
    (∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ)) ≤
      (max 1 (1/η))^(k+2)*(N : ℝ)^(1-η) := by
  let L := omega3CofactorLabels N δ s t W
  let E := L.image omega3CofactorValue
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t :=
    fun d hd => cutoff_lower hN (boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd)
      hη ht htop (hsize d hd)
  have hfibre := actual_fibre_weight (s := s) W hik hN hη hW hcut
  have hE : E ⊆ Icc 1 ⌊(N : ℝ)^(1-η)⌋₊ := by
    intro e he
    obtain ⟨c,hc,rfl⟩ := mem_image.mp he
    have hg := actual_profile W hN (fun j p hp => (hW j p hp).1) hcut hc
    exact mem_Icc.mpr ⟨hg.1, (Nat.le_floor_iff (by positivity)).mpr hg.2.2.2.1⟩
  have hcard : (E.card : ℝ) ≤ (N : ℝ)^(1-η) := by
    have hc : E.card ≤ ⌊(N : ℝ)^(1-η)⌋₊ := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hE
    exact (show (E.card : ℝ) ≤ (⌊(N : ℝ)^(1-η)⌋₊ : ℕ) by exact_mod_cast hc).trans (Nat.floor_le (by positivity))
  have hsplit := omega3_cofactor_label_fibres N δ s t W (fun _ => 1)
  simp only [mul_one] at hsplit
  calc
    _ = ∑ e ∈ E, ∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
        (convolutionCoeff W c.1 : ℝ) := hsplit
    _ ≤ ∑ _e ∈ E, (max 1 (1/η))^(k+2) := sum_le_sum (fun e _ => hfibre e)
    _ = (E.card : ℝ)*(max 1 (1/η))^(k+2) := by simp [mul_comm]
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ (max 1 (1/η))^(k+2))

/-- A genuine strict/closed main-mass estimate, with a positive-power saving.
X remains a prime-count centre, not a true-li expression. -/
theorem X_boundary_power {i k N : ℕ} {δ η s t : ℝ} (W : Fin i → Finset ℕ)
    (hik : i ≤ k) (hN : 2 ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ)^η ≤ p)
    (hsize : ∀ d ∈ boxConvolutionSupport W, (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (ht : 0 < t) (htop : t ≤ 10) :
    0 ≤ omega3SieveX N δ s t W - strictX N δ s t W ∧
      omega3SieveX N δ s t W - strictX N δ s t W ≤
        ((N.primeFactors.card : ℝ)+1)*(max 1 (1/η))^(k+2)*(N : ℝ)^(1-η) := by
  have hcut : ∀ d ∈ boxConvolutionSupport W, (N : ℝ)^η ≤ wuLocalCutoff N δ d t :=
    fun d hd => cutoff_lower hN (boxConvolutionSupport_pos (fun j p hp => (hW j p hp).1.pos) hd)
      hη ht htop (hsize d hd)
  have hc : ∀ c ∈ omega3CofactorLabels N δ s t W,
      0 < omega3CofactorValue c :=
    fun c hc => (actual_profile W hN (fun j p hp => (hW j p hp).1) hcut hc).1
  have heq : omega3SieveX N δ s t W - strictX N δ s t W =
      ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ)*
        (((omega3CofactorPrimeFibreLE N δ s c).card : ℝ)-(omega3CofactorPrimeFibre N δ s c).card) := by
    simp only [omega3SieveX, strictX, mul_sub, sum_sub_distrib]
  rw [heq]
  constructor
  · exact sum_nonneg (fun c hcm => mul_nonneg (Nat.cast_nonneg _) (prime_fibre_boundary_card (by omega) (hc c hcm)).1)
  · calc
      _ ≤ ∑ c ∈ omega3CofactorLabels N δ s t W,
          (convolutionCoeff W c.1 : ℝ)*((N.primeFactors.card : ℝ)+1) :=
        sum_le_sum (fun c hcm => mul_le_mul_of_nonneg_left
          (prime_fibre_boundary_card (by omega) (hc c hcm)).2 (Nat.cast_nonneg _))
      _ = ((N.primeFactors.card : ℝ)+1)*
          ∑ c ∈ omega3CofactorLabels N δ s t W, (convolutionCoeff W c.1 : ℝ) := by rw [← sum_mul]; ring
      _ ≤ ((N.primeFactors.card : ℝ)+1)*((max 1 (1/η))^(k+2)*(N : ℝ)^(1-η)) :=
        mul_le_mul_of_nonneg_left (cofactor_label_weight_bound W hik hN hη hW hsize ht htop) (by positivity)
      _ = _ := by ring

end
end HighTheta
