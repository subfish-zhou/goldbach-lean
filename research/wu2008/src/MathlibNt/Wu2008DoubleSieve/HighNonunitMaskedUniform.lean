import MathlibNt.Wu2008DoubleSieve.HighNonunitMaskedPayment

open scoped BigOperators Classical Topology
namespace Wu2008DoubleSieve.HighNonunitMasked
open Set MeasureTheory Filter HighNonunitLegal

variable {m r : ℕ}

noncomputable def widthCost (C : Fin r → Fin (m+1) → ℝ) (Phi a : ℝ) : ℝ :=
  slope m Phi*a^(m+1) + 200*a^m*(m+2 : ℝ) + ∑ q, 200*a^m*(∑ i, |C q i|)

noncomputable def atomCost (m r : ℕ) (a : ℝ) : ℝ := 10*a^m*(1+r : ℝ)

theorem budget_linear (C : Fin r → Fin (m+1) → ℝ) (Phi a h e : ℝ) :
    budget C Phi a h e = widthCost C Phi a*h + atomCost m r a*e := by
  have hq : (∑ q, 10*(a^m*(20*((∑ i, |C q i|)*h)+e))) =
      (∑ q, 200*a^m*(∑ i, |C q i|))*h + (r : ℝ)*(10*a^m*e) := by
    have hc : (r : ℝ)*(10*a^m*e) = ∑ _q : Fin r, 10*a^m*e := by simp
    rw [Finset.sum_mul, hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold budget widthCost atomCost
  rw [hq]
  ring

theorem widthCost_nonneg (C : Fin r → Fin (m+1) → ℝ) {Phi a : ℝ}
    (hPhi : 2 ≤ Phi) (ha : 0 ≤ a) : 0 ≤ widthCost C Phi a := by
  unfold widthCost slope
  positivity

/-- Fixed dimension, matrix, parameter cap and tolerance precede the scale threshold;
all closed-face intercepts and the actual Buchstab parameter are supplied afterwards. -/
theorem uniform (m r : ℕ) (j : Fin (m+1)) (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ i, 1 ≤ |C q i|) (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ gamma : Fin r → ℝ, |primeSum j R phi C gamma - integral j phi C gamma| < epsilon := by
  let D := widthCost C Phi 5 + widthCost C Phi 4
  let E := atomCost m r 5
  have hD : 0 ≤ D := add_nonneg (widthCost_nonneg C hPhi (by norm_num))
    (widthCost_nonneg C hPhi (by norm_num))
  obtain ⟨k,hk⟩ := gridWidth_arbitrarily_small (div_pos he (show 0 < 4*(D+1) by positivity))
  have hmesh : D*gridWidth k < epsilon/4 := by
    have hh := (lt_div_iff₀ (show 0 < 4*(D+1) by positivity)).mp hk
    have hw := gridWidth_pos k
    nlinarith
  obtain ⟨Tg,_hTg,hgrid⟩ := gridStep_uniform_epsilon (m+1) k 10 (epsilon/2) (by norm_num) (by positivity)
  have hlim : Tendsto (fun R : ℝ => E*primeOrderedDiscrepancy R) atTop (nhds 0) := by
    simpa only [mul_zero] using primeOrderedDiscrepancy_tendsto.const_mul E
  have hall : ∀ᶠ R : ℝ in atTop, ∀ phi : ℝ, phi ∈ Icc 2 Phi → ∀ gamma : Fin r → ℝ,
      |primeSum j R phi C gamma - integral j phi C gamma| < epsilon := by
    filter_upwards [prime_sampling_eventually j Phi hPhi C hC,
      hlim.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon/4 by positivity)),
      eventually_ge_atTop Tg] with R hp ha hR
    intro phi hphi gamma
    have h1 := hp k phi hphi gamma
    have h2 := hgrid R hR (sample j k phi C gamma) (sample_bound j k phi C gamma)
    have h3 := continuous_sampling_bound j hPhi hphi C hC k gamma
    rw [budget_linear] at h1 h3
    simp only [mul_zero, add_zero] at h3
    have ht := abs_sub_le (primeSum j R phi C gamma)
      (gridPrimeSum R (sample j k phi C gamma)) (integral j phi C gamma)
    have ht' := abs_sub_le (gridPrimeSum R (sample j k phi C gamma))
      (gridIntegral (sample j k phi C gamma)) (integral j phi C gamma)
    rw [abs_sub_comm (gridIntegral _)] at ht'
    dsimp only [D, E] at hmesh ha
    nlinarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro R hR
  exact hT R ((le_max_left _ _).trans hR)

/-- Literal interface: neither a sampling premise nor a quadrature premise is accepted. -/
theorem uniform_literal (m r : ℕ) (j : Fin (m+1)) (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ i, 1 ≤ |C q i|) (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ gamma : Fin r → ℝ,
      |(∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f *
          (if ∀ q, (∑ i, C q i*gridCoordinates R f i) ≤ gamma q
            then HighNonunitLegal.G j phi (gridCoordinates R f) else 0)) -
        (∫ t in continuousCube (m+1),
          (if ∀ q, (∑ i, C q i*t i) ≤ gamma q then HighNonunitLegal.G j phi t else 0) *
            continuousDensity t)| < epsilon := by
  obtain ⟨T,hT,h⟩ := uniform m r j C hC Phi hPhi epsilon he
  refine ⟨T,hT,fun R hR phi hphi gamma => ?_⟩
  have hF (t : Fin (m+1) → ℝ) : F j phi C gamma t =
      (if ∀ q, (∑ i, C q i*t i) ≤ gamma q then HighNonunitLegal.G j phi t else 0) := by
    unfold F mask
    split_ifs <;> rfl
  simpa only [primeSum, integral, hF] using h R hR phi hphi gamma

end Wu2008DoubleSieve.HighNonunitMasked
