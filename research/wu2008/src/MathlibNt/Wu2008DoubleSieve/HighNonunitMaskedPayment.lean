import MathlibNt.Wu2008DoubleSieve.HighNonunitMaskedSample

open scoped BigOperators Classical Topology
namespace Wu2008DoubleSieve.HighNonunitMasked
open Set MeasureTheory Filter HighNonunitLegal
open SecondFunctionalUnitMasked (jumpDensity jumpDensity_integrable jumpDensity_integral)

variable {m r : ℕ}

noncomputable def budget (C : Fin r → Fin (m+1) → ℝ) (Phi a h e : ℝ) : ℝ :=
  slope m Phi*h*a^(m+1) + 10*(a^m*(20*((m+2 : ℝ)*h)+e)) +
  ∑ q, 10*(a^m*(20*((∑ i, |C q i|)*h)+e))

theorem prime_envelope_identity (j : Fin (m+1)) (R Phi h phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) :
    (∑ f : Fin (m+1) → primeSlabPrimes R,
      primeSlabWeight R f * envelope j Phi h phi C gamma (gridCoordinates R f)) =
    slope m Phi*h*(∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f) +
    10*primeSlabMass R (coefficients j) phi ((m+2 : ℝ)*h) +
    ∑ q, 10*primeSlabMass R (C q) (gamma q) ((∑ i, |C q i|)*h) := by
  simp only [envelope, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · rw [← Finset.sum_mul, mul_comm, Finset.mul_sum]
    · simp only [primeSlabMass, Finset.mul_sum, gridCoordinates, mul_ite, zero_mul, mul_comm]
  · rw [Finset.sum_comm]
    simp only [primeSlabMass, Finset.mul_sum, gridCoordinates, mul_ite, zero_mul, mul_comm]

theorem prime_sampling_eventually (j : Fin (m+1)) (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (C : Fin r → Fin (m+1) → ℝ) (hC : ∀ q, ∃ i, 1 ≤ |C q i|) :
    ∀ᶠ R : ℝ in atTop, ∀ (k : ℕ) (phi : ℝ), phi ∈ Icc 2 Phi → ∀ (gamma : Fin r → ℝ),
      |primeSum j R phi C gamma - gridPrimeSum R (sample j k phi C gamma)| ≤
        budget C Phi 5 (gridWidth k) (primeOrderedDiscrepancy R) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), SecondFunctionalUnitFiniteKernel.mass_eventually,
    primeSlab_eventually_uniform] with R hR hm hs
  intro k phi hphi gamma
  have hh := (gridWidth_pos k).le
  have hl : primeSlabMass R (coefficients j) phi ((m+2 : ℝ)*gridWidth k) ≤
      5^m*(20*((m+2 : ℝ)*gridWidth k)+primeOrderedDiscrepancy R) := by
    simpa only [Nat.add_sub_cancel] using
      hs (m+1) (coefficients j) phi ((m+2 : ℝ)*gridWidth k) (by positivity) j (coefficients_selected j)
  have hq (q : Fin r) : primeSlabMass R (C q) (gamma q) ((∑ i, |C q i|)*gridWidth k) ≤
      5^m*(20*((∑ i, |C q i|)*gridWidth k)+primeOrderedDiscrepancy R) := by
    obtain ⟨i,hi⟩ := hC q
    simpa only [Nat.add_sub_cancel] using
      hs (m+1) (C q) (gamma q) ((∑ i, |C q i|)*gridWidth k) (by positivity) i hi
  calc
    _ ≤ ∑ f : Fin (m+1) → primeSlabPrimes R,
        primeSlabWeight R f * envelope j Phi (gridWidth k) phi C gamma (gridCoordinates R f) := by
      unfold primeSum gridPrimeSum
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro f _
      rw [← mul_sub, abs_mul, abs_of_nonneg (gridWeight_nonneg R f)]
      exact mul_le_mul_of_nonneg_left
        (sampling_pointwise j k hPhi hphi C gamma (gridCoordinates_mem hR f)) (gridWeight_nonneg R f)
    _ ≤ _ := by
      rw [prime_envelope_identity]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hm (m+1) Finset.univ) (by unfold slope; positivity))
        (mul_le_mul_of_nonneg_left hl (by norm_num)))
        (Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hq q) (by norm_num)))

theorem envelope_density_identity (j : Fin (m+1)) (Phi h phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) :
    envelope j Phi h phi C gamma t * continuousDensity t =
    slope m Phi*h*continuousDensity t +
    jumpDensity (continuousBand (coefficients j) phi ((m+2 : ℝ)*h)) t +
    ∑ q, jumpDensity (continuousBand (C q) (gamma q) ((∑ i, |C q i|)*h)) t := by
  simp only [envelope, add_mul, Finset.sum_mul, jumpDensity, continuousBand, Set.mem_ofPred_eq]

theorem envelope_integrable (j : Fin (m+1)) (Phi h phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) :
    IntegrableOn (fun t => envelope j Phi h phi C gamma t * continuousDensity t)
      (continuousCube (m+1)) := by
  simp_rw [envelope_density_identity]
  exact (((continuousDensity_integrable (m+1)).const_mul _).add
    (jumpDensity_integrable (continuousBand_measurable _ _ _))).add
    (integrable_finsetSum _ (fun q _ => jumpDensity_integrable (continuousBand_measurable _ _ _)))

theorem continuous_envelope_bound (j : Fin (m+1)) (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (C : Fin r → Fin (m+1) → ℝ) (hC : ∀ q, ∃ i, 1 ≤ |C q i|)
    (h phi : ℝ) (hh : 0 ≤ h) (gamma : Fin r → ℝ) :
    (∫ t in continuousCube (m+1), envelope j Phi h phi C gamma t * continuousDensity t) ≤
      budget C Phi 4 h 0 := by
  have hL := continuousBand_measurable (coefficients j) phi ((m+2 : ℝ)*h)
  have hQ (q : Fin r) := continuousBand_measurable (C q) (gamma q) ((∑ i, |C q i|)*h)
  have h0 : IntegrableOn (fun t : Fin (m+1) → ℝ => slope m Phi*h*continuousDensity t)
      (continuousCube (m+1)) := (continuousDensity_integrable (m+1)).const_mul _
  have h1 := jumpDensity_integrable hL
  have h2 : IntegrableOn
      (fun t => ∑ q, jumpDensity (continuousBand (C q) (gamma q) ((∑ i, |C q i|)*h)) t)
      (continuousCube (m+1)) :=
    integrable_finsetSum _ (fun q _ => jumpDensity_integrable (hQ q))
  simp_rw [envelope_density_identity]
  have hi2 := integral_add (h0.add h1) h2
  have hi1 := integral_add h0 h1
  simp only [Pi.add_apply] at hi2 hi1
  rw [hi2, hi1, integral_const_mul, jumpDensity_integral hL,
    integral_finsetSum Finset.univ (fun q _ => jumpDensity_integrable (hQ q))]
  simp_rw [jumpDensity_integral (hQ _)]
  unfold budget
  simp only [add_zero]
  apply add_le_add
  · exact add_le_add
      (mul_le_mul_of_nonneg_left (continuousCube_integral_bounds (m+1)).2 (by unfold slope; positivity))
      (mul_le_mul_of_nonneg_left
        (by simpa only [Nat.add_sub_cancel] using (legal_slab_bounds j phi _ (by positivity)).2) (by norm_num))
  · apply Finset.sum_le_sum
    intro q _
    obtain ⟨i,hi⟩ := hC q
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Nat.add_sub_cancel] using
        (continuousSlab_bounds i (C q) (gamma q) _ hi (by positivity)).2) (by norm_num)

theorem continuous_sampling_bound (j : Fin (m+1)) {Phi phi : ℝ}
    (hPhi : 2 ≤ Phi) (hphi : phi ∈ Icc 2 Phi)
    (C : Fin r → Fin (m+1) → ℝ) (hC : ∀ q, ∃ i, 1 ≤ |C q i|)
    (k : ℕ) (gamma : Fin r → ℝ) :
    |integral j phi C gamma - gridIntegral (sample j k phi C gamma)| ≤
      budget C Phi 4 (gridWidth k) 0 := by
  have hG := F_integrable j phi C gamma
  have hS := gridStep_integrable (sample j k phi C gamma)
  have hE := envelope_integrable j Phi (gridWidth k) phi C gamma
  unfold integral gridIntegral
  rw [← integral_sub hG hS]
  apply (abs_integral_le_integral_abs).trans
  apply le_trans _ (continuous_envelope_bound j Phi hPhi C hC (gridWidth k) phi (gridWidth_pos k).le gamma)
  apply integral_mono_ae (hG.sub hS).abs hE
  filter_upwards [ae_restrict_mem (continuousCube_measurable (m+1))] with t ht
  dsimp only [Pi.sub_apply]
  rw [← sub_mul, abs_mul, abs_of_nonneg (continuousDensity_nonneg ht)]
  exact mul_le_mul_of_nonneg_right (sampling_pointwise j k hPhi hphi C gamma ht)
    (continuousDensity_nonneg ht)

theorem integral_bounds (j : Fin (m+1)) (phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) :
    0 ≤ integral j phi C gamma ∧ integral j phi C gamma ≤ 10*4^(m+1) := by
  constructor
  · apply setIntegral_nonneg (continuousCube_measurable _)
    intro t ht
    exact mul_nonneg (F_bounds j phi C gamma ht).1 (continuousDensity_nonneg ht)
  · calc
      _ ≤ ∫ t in continuousCube (m+1), 10*continuousDensity t := by
        apply setIntegral_mono_on (F_integrable j phi C gamma)
          ((continuousDensity_integrable _).const_mul 10) (continuousCube_measurable _)
        intro t ht
        exact mul_le_mul_of_nonneg_right (F_bounds j phi C gamma ht).2 (continuousDensity_nonneg ht)
      _ = 10*(∫ t in continuousCube (m+1), continuousDensity t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (continuousCube_integral_bounds _).2 (by norm_num)

theorem primeSum_bounds (j : Fin (m+1)) (R phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (hR : 1 < R) :
    0 ≤ primeSum j R phi C gamma ∧ primeSum j R phi C gamma ≤
      10*(∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f) := by
  constructor
  · exact Finset.sum_nonneg (fun f _ => mul_nonneg (gridWeight_nonneg R f)
      (F_bounds j phi C gamma (gridCoordinates_mem hR f)).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun f _ => (mul_le_mul_of_nonneg_left
      (F_bounds j phi C gamma (gridCoordinates_mem hR f)).2 (gridWeight_nonneg R f)).trans_eq (mul_comm _ _))

end Wu2008DoubleSieve.HighNonunitMasked
