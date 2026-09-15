import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitMaskedSample

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitMasked
open Set MeasureTheory Filter Wu2008DoubleSieve SecondFunctionalUnitKernel

/-- One discrepancy payment for each of the two gates and every extra row. -/
noncomputable def budget {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ) (a h e : ℝ) : ℝ :=
  100*(m+1 : ℝ)*h*a^(m+1) +
  10*(a^m*(20*((m+2 : ℝ)*h)+e)) +
  10*(a^m*(20*((m+1 : ℝ)*h)+e)) +
  ∑ q, 10*(a^m*(20*((∑ i, |C q i|)*h)+e))

theorem prime_envelope_identity {m r : ℕ} (R h phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) :
    (∑ f : Fin (m+1) → primeSlabPrimes R,
      primeSlabWeight R f * envelope h phi b C gamma (gridCoordinates R f)) =
    100*(m+1 : ℝ)*h*(∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f) +
    10*primeSlabUnitLowerMass m R phi ((m+2 : ℝ)*h) +
    10*primeSlabUnitCapMass m R phi b ((m+1 : ℝ)*h) +
    ∑ q, 10*primeSlabMass R (C q) (gamma q) ((∑ i, |C q i|)*h) := by
  simp only [envelope, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · congr 1
      · rw [← Finset.sum_mul, mul_comm, Finset.mul_sum]
      · simp only [primeSlabUnitLowerMass, Finset.mul_sum, gridCoordinates, mul_ite,
          zero_mul, mul_comm]
    · simp only [primeSlabUnitCapMass, Finset.mul_sum, gridCoordinates, mul_ite,
        zero_mul, mul_comm]
  · rw [Finset.sum_comm]
    simp only [primeSlabMass, Finset.mul_sum, dot, gridCoordinates, mul_ite,
      zero_mul, mul_comm]

/-- All finite masses are produced before the moving parameters are supplied. -/
theorem prime_sampling_eventually {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) :
    ∀ᶠ R : ℝ in atTop, ∀ (k : ℕ) (phi b : ℝ) (gamma : Fin r → ℝ)
      (strict : Fin r → Bool),
      |primeSum R phi b C gamma strict - gridPrimeSum R (sample k phi b C gamma strict)| ≤
        budget C 5 (gridWidth k) (primeOrderedDiscrepancy R) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), SecondFunctionalUnitFiniteKernel.mass_eventually,
    primeSlab_unit_eventually_uniform, primeSlab_eventually_uniform] with R hR hm hu hs
  intro k phi b gamma strict
  have hh := (gridWidth_pos k).le
  have hl := (hu m phi b ((m+2 : ℝ)*gridWidth k) (by positivity)).1
  have hb := (hu m phi b ((m+1 : ℝ)*gridWidth k) (by positivity)).2
  have hq (q : Fin r) : primeSlabMass R (C q) (gamma q) ((∑ i, |C q i|)*gridWidth k) ≤
      5^m*(20*((∑ i, |C q i|)*gridWidth k)+primeOrderedDiscrepancy R) := by
    obtain ⟨j,hj⟩ := hC q
    simpa only [Nat.add_sub_cancel] using
      hs (m+1) (C q) (gamma q) ((∑ i, |C q i|)*gridWidth k) (by positivity) j hj
  calc
    _ ≤ ∑ f : Fin (m+1) → primeSlabPrimes R,
        primeSlabWeight R f * envelope (gridWidth k) phi b C gamma (gridCoordinates R f) := by
      unfold primeSum gridPrimeSum
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro f _
      rw [← mul_sub, abs_mul, abs_of_nonneg (gridWeight_nonneg R f)]
      exact mul_le_mul_of_nonneg_left
        (sampling_pointwise k phi b C gamma strict (gridCoordinates_mem hR f)) (gridWeight_nonneg R f)
    _ ≤ _ := by
      rw [prime_envelope_identity]
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hm (m+1) Finset.univ) (by positivity))
        (mul_le_mul_of_nonneg_left hl (by norm_num)))
        (mul_le_mul_of_nonneg_left hb (by norm_num)))
        (Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hq q) (by norm_num)))

/-- Weighted closed-band term; this is not an almost-everywhere deletion. -/
noncomputable def jumpDensity {n : ℕ} (s : Set (Fin n → ℝ)) (t : Fin n → ℝ) : ℝ :=
  (if t ∈ s then 10 else 0) * continuousDensity t

theorem jumpDensity_eq {n : ℕ} (s : Set (Fin n → ℝ)) (t : Fin n → ℝ) :
    jumpDensity s t = 10 * s.indicator continuousDensity t := by
  simp only [jumpDensity, Set.indicator_apply]
  split_ifs <;> ring

theorem jumpDensity_integrable {n : ℕ} {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    IntegrableOn (jumpDensity s) (continuousCube n) := by
  change IntegrableOn (fun t => jumpDensity s t) (continuousCube n)
  simp_rw [jumpDensity_eq]
  exact ((continuousDensity_integrable n).indicator hs).const_mul 10

theorem jumpDensity_integral {n : ℕ} {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    (∫ t in continuousCube n, jumpDensity s t) =
      10*(∫ t in continuousCube n ∩ s, continuousDensity t) := by
  simp_rw [jumpDensity_eq]
  rw [integral_const_mul, setIntegral_indicator hs]

theorem envelope_density_identity {m r : ℕ} (h phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) :
    envelope h phi b C gamma t * continuousDensity t =
    100*(m+1 : ℝ)*h*continuousDensity t +
    jumpDensity (continuousLowerFace phi ((m+2 : ℝ)*h)) t +
    jumpDensity (continuousCapFace phi b ((m+1 : ℝ)*h)) t +
    ∑ q, jumpDensity (continuousBand (C q) (gamma q) ((∑ i, |C q i|)*h)) t := by
  simp only [envelope, add_mul, Finset.sum_mul, jumpDensity,
    continuousLowerFace, continuousCapFace, continuousBand, Set.mem_ofPred_eq, dot]

theorem envelope_integrable {m r : ℕ} (h phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) :
    IntegrableOn (fun t => envelope h phi b C gamma t * continuousDensity t)
      (continuousCube (m+1)) := by
  simp_rw [envelope_density_identity]
  apply Integrable.add
  · apply Integrable.add
    · exact ((continuousDensity_integrable (m+1)).const_mul _).add
        (jumpDensity_integrable (by rw [continuousLowerFace_eq]; apply continuousBand_measurable))
    · exact jumpDensity_integrable (by rw [continuousCapFace_eq]; apply continuousBand_measurable)
  · exact integrable_finsetSum _ (fun q _ => jumpDensity_integrable (continuousBand_measurable _ _ _))

theorem continuous_envelope_bound {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (h phi b : ℝ) (hh : 0 ≤ h) (gamma : Fin r → ℝ) :
    (∫ t in continuousCube (m+1), envelope h phi b C gamma t * continuousDensity t) ≤
      budget C 4 h 0 := by
  have hL : MeasurableSet (continuousLowerFace (n := m) phi ((m+2 : ℝ)*h)) := by
    rw [continuousLowerFace_eq]; apply continuousBand_measurable
  have hB : MeasurableSet (continuousCapFace (n := m+1) phi b ((m+1 : ℝ)*h)) := by
    rw [continuousCapFace_eq]; apply continuousBand_measurable
  have hQ (q : Fin r) := continuousBand_measurable (C q) (gamma q) ((∑ i, |C q i|)*h)
  have h0 : IntegrableOn (fun t : Fin (m+1) → ℝ => 100*(m+1 : ℝ)*h*continuousDensity t)
      (continuousCube (m+1)) := (continuousDensity_integrable (m+1)).const_mul _
  have h1 := jumpDensity_integrable hL
  have h2 := jumpDensity_integrable hB
  have h3 : IntegrableOn
      (fun t => ∑ q, jumpDensity (continuousBand (C q) (gamma q) ((∑ i, |C q i|)*h)) t)
      (continuousCube (m+1)) :=
    integrable_finsetSum _ (fun q _ => jumpDensity_integrable (hQ q))
  simp_rw [envelope_density_identity]
  have hi3 := integral_add ((h0.add h1).add h2) h3
  have hi2 := integral_add (h0.add h1) h2
  have hi1 := integral_add h0 h1
  simp only [Pi.add_apply] at hi3 hi2 hi1
  rw [hi3, hi2, hi1, integral_const_mul, jumpDensity_integral hL, jumpDensity_integral hB,
    integral_finsetSum Finset.univ (fun q _ => jumpDensity_integrable (hQ q))]
  simp_rw [jumpDensity_integral (hQ _)]
  unfold budget
  simp only [add_zero]
  apply add_le_add
  · apply add_le_add
    · exact add_le_add
        (mul_le_mul_of_nonneg_left (continuousCube_integral_bounds (m+1)).2 (by positivity))
        (mul_le_mul_of_nonneg_left (continuousLowerFace_bounds phi _ (by positivity)).2 (by norm_num))
    · exact mul_le_mul_of_nonneg_left
        (by simpa only [Nat.add_sub_cancel] using
          (continuousCapFace_bounds (Fin.last m) phi b _ (by positivity)).2) (by norm_num)
  · apply Finset.sum_le_sum
    intro q _
    obtain ⟨j,hj⟩ := hC q
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Nat.add_sub_cancel] using
        (continuousSlab_bounds j (C q) (gamma q) _ hj (by positivity)).2) (by norm_num)

theorem continuous_sampling_bound {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (k : ℕ) (phi b : ℝ) (gamma : Fin r → ℝ)
    (strict : Fin r → Bool) :
    |integral phi b C gamma strict - gridIntegral (sample k phi b C gamma strict)| ≤
      budget C 4 (gridWidth k) 0 := by
  have hG := G_weighted_integrable phi b C gamma strict
  have hS := gridStep_integrable (sample k phi b C gamma strict)
  have hE := envelope_integrable (gridWidth k) phi b C gamma
  unfold integral gridIntegral
  rw [← integral_sub hG hS]
  apply (abs_integral_le_integral_abs).trans
  apply le_trans _ (continuous_envelope_bound C hC (gridWidth k) phi b (gridWidth_pos k).le gamma)
  apply integral_mono_ae (hG.sub hS).abs hE
  filter_upwards [ae_restrict_mem (continuousCube_measurable (m+1))] with t ht
  dsimp only [Pi.sub_apply]
  rw [← sub_mul, abs_mul, abs_of_nonneg (continuousDensity_nonneg ht)]
  exact mul_le_mul_of_nonneg_right (sampling_pointwise k phi b C gamma strict ht)
    (continuousDensity_nonneg ht)

end SecondFunctionalUnitMasked
