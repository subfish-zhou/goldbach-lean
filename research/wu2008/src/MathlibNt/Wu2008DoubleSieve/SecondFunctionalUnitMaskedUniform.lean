import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitMaskedPayment

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitMasked
open Set MeasureTheory Filter Wu2008DoubleSieve SecondFunctionalUnitKernel

/-- Fixed geometric coefficient, independent of all moving intercepts. -/
noncomputable def widthCost {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ) (a : ℝ) : ℝ :=
  100*(m+1 : ℝ)*a^(m+1) + 200*a^m*(m+2 : ℝ) + 200*a^m*(m+1 : ℝ) +
    ∑ q, 200*a^m*(∑ i, |C q i|)

noncomputable def atomCost (m r : ℕ) (a : ℝ) : ℝ := 10*a^m*(2+r : ℝ)

theorem budget_linear {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ) (a h e : ℝ) :
    budget C a h e = widthCost C a*h + atomCost m r a*e := by
  have hq : (∑ q, 10*(a^m*(20*((∑ i, |C q i|)*h)+e))) =
      (∑ q, 200*a^m*(∑ i, |C q i|))*h + (r : ℝ)*(10*a^m*e) := by
    have hc : (r : ℝ)*(10*a^m*e) = ∑ _q : Fin r, 10*a^m*e := by simp
    rw [Finset.sum_mul, hc]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  unfold budget widthCost atomCost
  rw [hq]
  ring

theorem widthCost_nonneg {m r : ℕ} (C : Fin r → Fin (m+1) → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ widthCost C a := by
  unfold widthCost
  positivity

/-- The mesh is chosen after the fixed matrix and tolerance, before the scale. -/
theorem uniform (m r : ℕ) (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |primeSum R phi b C gamma strict - integral phi b C gamma strict| < epsilon := by
  let D := widthCost C 5 + widthCost C 4
  let E := atomCost m r 5
  have hD : 0 ≤ D := add_nonneg (widthCost_nonneg C (by norm_num)) (widthCost_nonneg C (by norm_num))
  obtain ⟨k,hk⟩ := gridWidth_arbitrarily_small (div_pos he (show 0 < 4*(D+1) by positivity))
  have hmesh : D*gridWidth k < epsilon/4 := by
    have hh := (lt_div_iff₀ (show 0 < 4*(D+1) by positivity)).mp hk
    have hw := gridWidth_pos k
    nlinarith
  obtain ⟨Tg,hTg,hgrid⟩ := gridStep_uniform_epsilon (m+1) k 10 (epsilon/2) (by norm_num) (by positivity)
  have hlim : Tendsto (fun R : ℝ => E*primeOrderedDiscrepancy R) atTop (nhds 0) := by
    simpa only [mul_zero] using primeOrderedDiscrepancy_tendsto.const_mul E
  have hall : ∀ᶠ R : ℝ in atTop, ∀ (phi b : ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |primeSum R phi b C gamma strict - integral phi b C gamma strict| < epsilon := by
    filter_upwards [prime_sampling_eventually C hC,
      hlim.eventually (gt_mem_nhds (show (0 : ℝ) < epsilon/4 by positivity)),
      eventually_ge_atTop Tg] with R hp ha hR
    intro phi b gamma strict
    have h1 := hp k phi b gamma strict
    have h2 := hgrid R hR (sample k phi b C gamma strict) (sample_bound k phi b C gamma strict)
    have h3 := continuous_sampling_bound C hC k phi b gamma strict
    rw [budget_linear] at h1 h3
    simp only [mul_zero, add_zero] at h3
    have ht := abs_sub_le (primeSum R phi b C gamma strict)
      (gridPrimeSum R (sample k phi b C gamma strict)) (integral phi b C gamma strict)
    have ht' := abs_sub_le (gridPrimeSum R (sample k phi b C gamma strict))
      (gridIntegral (sample k phi b C gamma strict)) (integral phi b C gamma strict)
    rw [abs_sub_comm (gridIntegral _)] at ht'
    dsimp only [D, E] at hmesh ha
    nlinarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro R hR
  exact hT R ((le_max_left _ _).trans hR)

theorem uniform_fin4 (r : ℕ) (C : Fin r → Fin 4 → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |primeSum R phi b C gamma strict - integral phi b C gamma strict| < epsilon :=
  uniform 3 r C hC epsilon he

theorem uniform_fin5 (r : ℕ) (C : Fin r → Fin 5 → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |primeSum R phi b C gamma strict - integral phi b C gamma strict| < epsilon :=
  uniform 4 r C hC epsilon he

/-- The empty extra mask does not remove either intrinsic strict gate. -/
theorem uniform_empty (m : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ),
      |(∑ f : Fin (m+1) → primeSlabPrimes R,
          primeSlabWeight R f * U phi b (gridCoordinates R f)) -
        (∫ t in continuousCube (m+1), U phi b t * continuousDensity t)| < epsilon := by
  obtain ⟨T,hT,h⟩ := uniform m 0 Fin.elim0 (fun q => Fin.elim0 q) epsilon he
  refine ⟨T,hT,fun R hR phi b => ?_⟩
  simpa only [primeSum, integral, G_empty] using h R hR phi b Fin.elim0 Fin.elim0

end SecondFunctionalUnitMasked
