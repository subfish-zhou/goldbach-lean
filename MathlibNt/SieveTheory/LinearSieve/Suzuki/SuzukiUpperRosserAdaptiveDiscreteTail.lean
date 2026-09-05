import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserFiniteToContinuousProducer

/-!
# Adaptive finite-carrier bridge for the upper Rosser tail

This file keeps three different facts separate:

* a finite boundary carrier has an exact support depth;
* the already proved fixed-terminal geometric estimate controls every finite
  block beginning at one cutoff, uniformly in the carrier size;
* passing from that absolute block estimate to the Euler-product-preserving
  recursive state still needs a one-step relative Lyapunov contraction.

In particular, the continuous `45 * (4 / 5) ^ L` volume tail is not used as a
bound for a discrete prime sum.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Filter Topology

noncomputable section

/-- The first pair depth which is forced to vanish solely by the cardinality of
its finite ambient carrier. -/
def upperRosserBoundaryCarrierSupportDepth (P : Finset ℕ) : ℕ :=
  P.card / 2 + 1

/-- Exact carrier-support cutoff.  This is a finite combinatorial statement; it
contains no continuous-volume comparison. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_eq_zero_at_carrierSupportDepth
    (w : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity w D q P
      (upperRosserBoundaryCarrierSupportDepth P) = 0 := by
  apply LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
  unfold upperRosserBoundaryCarrierSupportDepth
  omega

/-- Every depth after the adaptive support cutoff vanishes as well. -/
theorem upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_carrierSupportDepth_le
    (w : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) {k : ℕ}
    (hk : upperRosserBoundaryCarrierSupportDepth P ≤ k) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity w D q P k = 0 := by
  apply LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_card_lt
  unfold upperRosserBoundaryCarrierSupportDepth at hk
  omega

/-- The first honest uniform-in-carrier completion bridge.

The complete adaptive finite sum is bounded by a fixed prefix plus the existing
**discrete** geometric block tail.  The carrier cardinality occurs only as the
length of the finite remainder block; the cutoff `N + L` and the error `τ L`
are selected before the sieve and carrier.  No continuous tail is substituted
for the discrete remainder. -/
theorem
    exists_upperRosserBoundaryChains_completeAdaptiveDepth_le_prefix_add_uniformTail
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ τ : ℕ → ℝ,
      Tendsto τ atTop (nhds 0) ∧
      (∀ L, 0 ≤ τ L) ∧
      ∀ (S : BoundingSieve) (L q : ℕ) (z Δ s : ℝ),
        2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
        (∑ k ∈ Finset.range (P.card + 1),
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q P k) ≤
          (∑ k ∈ Finset.range (L + N),
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p))
              (Nat.floor Δ + 1) q P k) + τ L := by
  obtain ⟨N, τ₀, hτ₀, hblock⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthDensity_uniform_tail K hK
  let τ : ℕ → ℝ := fun L => |τ₀ L|
  have hτ : Tendsto τ atTop (nhds 0) := by
    simpa [τ] using hτ₀.abs
  have hτnonneg : ∀ L, 0 ≤ τ L := fun L => abs_nonneg _
  refine ⟨N, τ, hτ, hτnonneg, ?_⟩
  intro S L q z Δ s hz hΔ hs hlocal hcut hq
  dsimp
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  let f : ℕ → ℝ := fun k =>
    LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
      (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q P k
  have hfnonneg : ∀ k, 0 ≤ f k := by
    intro k
    apply LinearSieve.upperRosserBoundaryChainsFixedDepthDensity_nonneg
    intro p hp
    exact nu_div_one_sub_nonneg_of_mem (Finset.mem_filter.mp hp).1
  by_cases hlen : L + N ≤ P.card + 1
  · have hsplit := Finset.sum_range_add f (L + N) (P.card + 1 - (L + N))
    have hadd : L + N + (P.card + 1 - (L + N)) = P.card + 1 :=
      Nat.add_sub_of_le hlen
    rw [hadd] at hsplit
    rw [hsplit]
    change (∑ k ∈ Finset.range (L + N), f k) +
        (∑ j ∈ Finset.range (P.card + 1 - (L + N)), f (L + N + j)) ≤
      (∑ k ∈ Finset.range (L + N), f k) + τ L
    have htail := hblock S L (P.card + 1 - (L + N)) q z Δ s
      hz hΔ hs hlocal hcut hq
    have htail' := htail.trans (le_abs_self (τ₀ L))
    have htail'' :
        (∑ j ∈ Finset.range (P.card + 1 - (L + N)), f (L + N + j)) ≤
          τ L := by
      simpa [f, P, τ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail'
    linarith
  · have hcard : P.card + 1 ≤ L + N := Nat.le_of_not_ge hlen
    have hprefix :
        (∑ k ∈ Finset.range (P.card + 1), f k) ≤
          ∑ k ∈ Finset.range (L + N), f k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono hcard
      · intro k hk hnot
        exact hfnonneg k
    exact hprefix.trans (le_add_of_nonneg_right (hτnonneg L))

/-- The absolute reverse-pair operator has spare room below `9/10`.
This quantitative strengthening is what absorbs the two local-product error
factors in the relative transition. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_le_seventeen_twentieth
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
          p₁ < p₀ ∧
            2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) ≤
          (17 / 20 : ℝ) * r ^ 2 := by
  let ε : ℝ := 1 / 80
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨m, hfar⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_far_lt_uniform
      K ε (by linarith) hε
  let M : ℕ := m + 2
  let R : ℝ := (2 : ℝ) ^ M
  have hR : 3 ≤ R := by
    have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    dsimp [R, M]
    rw [pow_add]
    norm_num
    linarith
  have hpowm : (2 : ℝ) ^ m ≤ R := by
    dsimp [R, M]
    rw [pow_add]
    norm_num
  obtain ⟨Q, hQ, hnear⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_near_le
      K ε R hK hε hR
  refine ⟨Q, hQ, ?_⟩
  intro S q r P hq hqPrime hlocal hr hP hqP
  let near : ℕ → Prop := fun p =>
    Real.log p / Real.log q < R
  let f : ℕ → ℝ := fun p₀ =>
    ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2
  let T : Finset ℕ := P.filter (fun p => ¬near p)
  have hT : T ⊆ P := Finset.filter_subset _ _
  have hfarCoord : ∀ p ∈ T,
      (2 : ℝ) ^ m ≤ Real.log p / Real.log q := by
    intro p hp
    have hpNot := (Finset.mem_filter.mp hp).2
    exact hpowm.trans (le_of_not_gt hpNot)
  have hfarBound : (∑ p₀ ∈ T, f p₀) < ε * r ^ 2 := by
    exact hfar S q r P T hlocal hr hqPrime hP hqP hT hfarCoord
  have hnearBound :
      (∑ p₀ ∈ P.filter near, f p₀) ≤
        ((4 / 5 : ℝ) + ε) * r ^ 2 := by
    simpa [near, f] using
      hnear S q r P hq hqPrime hlocal hr hP hqP
  have hsplit := Finset.sum_filter_add_sum_filter_not P near f
  change (∑ p₀ ∈ P, f p₀) ≤ (17 / 20 : ℝ) * r ^ 2
  rw [← hsplit]
  apply le_of_lt
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  calc
    (∑ p₀ ∈ P.filter near, f p₀) +
        ∑ p₀ ∈ P.filter (fun p => ¬near p), f p₀ <
      ((4 / 5 : ℝ) + ε) * r ^ 2 + ε * r ^ 2 :=
        add_lt_add_of_le_of_lt hnearBound (by simpa [T] using hfarBound)
    _ < (17 / 20 : ℝ) * r ^ 2 := by
      dsimp [ε]
      nlinarith

/-- Uniform smallness of the local-product error once the terminal prime is
large.  The explicit `1/100` is chosen only to leave ample room between the
absolute coefficient `17/20` and the requested relative coefficient `9/10`. -/
theorem exists_localProductError_le_one_hundredth (K : ℝ) (_hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧ ∀ x : ℝ, Q ≤ x →
      K / Real.log (x + 1) ≤ (1 / 100 : ℝ) := by
  let Q : ℝ := max 2 (Real.exp (100 * K))
  refine ⟨Q, le_max_left _ _, ?_⟩
  intro x hx
  have hexp : Real.exp (100 * K) ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 < x + 1 := by
    have : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      ((le_max_left _ _).trans hx)
    linarith
  have hlog : 100 * K ≤ Real.log (x + 1) := by
    rw [← Real.log_exp (100 * K)]
    apply Real.strictMonoOn_log.monotoneOn (Real.exp_pos _)
      (zero_lt_one.trans hx1)
    linarith
  have hlogpos : 0 < Real.log (x + 1) := Real.log_pos hx1
  apply (div_le_iff₀ hlogpos).2
  nlinarith

/-- One reverse pair contracts the Euler-product-preserving Lyapunov envelope.

The proof needs the spare `17/20` absolute contraction: the two local-product
errors are positive, so the already rounded `9/10` estimate alone cannot imply a
`9/10` relative estimate.  Above a larger cutoff each error is at most `1/100`,
and `(17/20) * (101/100)^2 < 9/10`. -/
theorem UpperRosserRelativeLyapunovOneStepContraction :
  ∀ K : ℝ, 1 ≤ K →
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
          p₁ < p₀ ∧
            2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
          (upperRosserAlternatingPairDiscreteRelativeTransition
              S.nu P p₀ p₁ *
            (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q)) ^ 2) ≤
          (9 / 10 : ℝ) * r ^ 2 := by
  intro K hK
  obtain ⟨Q₀, hQ₀, habs⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_le_seventeen_twentieth K hK
  obtain ⟨Q₁, hQ₁, herr⟩ := exists_localProductError_le_one_hundredth K hK
  let Q := max Q₀ Q₁
  refine ⟨Q, hQ₀.trans (le_max_left _ _), ?_⟩
  intro S q r P hQq hqPrime hlocal hr hP hqP
  have hQ₀q : Q₀ ≤ (q : ℝ) := (le_max_left _ _).trans hQq
  have hQ₁q : Q₁ ≤ (q : ℝ) := (le_max_right _ _).trans hQq
  have hK0 : 0 ≤ K := by linarith
  have hqerr : K / Real.log ((q : ℝ) + 1) ≤ (1 / 100 : ℝ) :=
    herr q hQ₁q
  have habs' := habs S q r P hQ₀q hqPrime hlocal hr hP hqP
  let rel : ℕ → ℕ → Prop := fun p₀ p₁ =>
    p₁ < p₀ ∧
      2 * (Real.log p₀ / Real.log q) < Real.log p₁ / Real.log q + r
  let a : ℕ → ℕ → ℝ := fun p₀ p₁ =>
    (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
      ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
        (Real.log p₀ / Real.log q)) ^ 2
  have hterm : ∀ p₀ ∈ P, ∀ p₁ ∈ P.filter (rel p₀),
      (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
          (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
        ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
          (Real.log p₀ / Real.log q)) ^ 2 ≤
        ((101 / 100 : ℝ) ^ 2) * a p₀ p₁ := by
    intro p₀ hp₀ p₁ hp₁
    have hp₁data := Finset.mem_filter.mp hp₁
    have hp₁P : p₁ ∈ P := hp₁data.1
    have hp₁Prime : p₁.Prime := Nat.prime_of_mem_primeFactors (hP hp₁P)
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
    have hlogq1 : 0 < Real.log ((q : ℝ) + 1) :=
      Real.log_pos (by exact_mod_cast (Nat.lt_add_one_iff.mpr hqPrime.pos))
    have hlogp₁1 : 0 < Real.log ((p₁ : ℝ) + 1) :=
      Real.log_pos (by exact_mod_cast (Nat.lt_add_one_iff.mpr hp₁Prime.pos))
    have hp₁err : K / Real.log ((p₁ : ℝ) + 1) ≤ (1 / 100 : ℝ) := by
      apply herr p₁
      exact hQ₁q.trans (by exact_mod_cast (hqP p₁ hp₁P).le)
    have hE0 : 0 ≤ 1 + K / Real.log ((q : ℝ) + 1) := by positivity
    have hE1 : 0 ≤ 1 + K / Real.log ((p₁ : ℝ) + 1) := by positivity
    have hE0b : 1 + K / Real.log ((q : ℝ) + 1) ≤ (101 / 100 : ℝ) := by
      linarith
    have hE1b : 1 + K / Real.log ((p₁ : ℝ) + 1) ≤ (101 / 100 : ℝ) := by
      linarith
    have hweight :
        0 ≤ (S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) :=
      mul_nonneg (nu_div_one_sub_nonneg_of_mem (hP hp₀))
        (nu_div_one_sub_nonneg_of_mem (hP hp₁P))
    have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
      intro p hp
      have hpS := hP hp
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
      have hpDvd : p ∣ S.prodPrimes :=
        (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
      exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd))
    have hgaps := upperRosserRelativeSkippedGaps_le_logCocycle
      hlocal hK0 hqPrime hP hqP hp₀ hp₁P hp₁data.2.1
    have htransitionRaw :
        upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ ≤
          ((S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁))) *
          ((Real.log p₀ / Real.log ((q : ℝ) + 1)) *
            (1 + K / Real.log ((q : ℝ) + 1)) *
              (1 + K / Real.log ((p₁ : ℝ) + 1))) := by
      rw [upperRosserAlternatingPairDiscreteRelativeTransition_eq_normalized_twoGapProducts
        S.nu hp₀ hp₁P hp₁data.2.1 hfactor]
      calc
        ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
            ∏ p ∈ P.filter (fun p => p < p₁), (1 - S.nu p)⁻¹) *
              ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
                (1 - S.nu p)⁻¹ =
          ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁))) *
            ((∏ p ∈ P.filter (fun p => p < p₁), (1 - S.nu p)⁻¹) *
              ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
                (1 - S.nu p)⁻¹) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgaps hweight
    have hp₀Prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
    have hlogp₀ : 0 < Real.log p₀ :=
      Real.log_pos (by exact_mod_cast hp₀Prime.one_lt)
    have hscale : 0 ≤ Real.log ((q : ℝ) + 1) / Real.log p₀ :=
      div_nonneg hlogq1.le hlogp₀.le
    have htransition :
        upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
            (Real.log ((q : ℝ) + 1) / Real.log p₀) ≤
          ((S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁))) *
            ((1 + K / Real.log ((q : ℝ) + 1)) *
              (1 + K / Real.log ((p₁ : ℝ) + 1))) := by
      calc
        _ ≤ (((S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁))) *
            ((Real.log p₀ / Real.log ((q : ℝ) + 1)) *
              (1 + K / Real.log ((q : ℝ) + 1)) *
                (1 + K / Real.log ((p₁ : ℝ) + 1)))) *
              (Real.log ((q : ℝ) + 1) / Real.log p₀) :=
          mul_le_mul_of_nonneg_right htransitionRaw hscale
        _ = _ := by field_simp [hlogq1.ne', hlogp₀.ne']
    have hratioSq : 0 ≤
        ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
          (Real.log p₀ / Real.log q)) ^ 2 := sq_nonneg _
    calc
      _ ≤ (((S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁))) *
          ((1 + K / Real.log ((q : ℝ) + 1)) *
            (1 + K / Real.log ((p₁ : ℝ) + 1)))) * _ :=
        mul_le_mul_of_nonneg_right htransition hratioSq
      _ ≤ (((101 / 100 : ℝ) ^ 2) *
          ((S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)))) * _ := by
        apply mul_le_mul_of_nonneg_right _ hratioSq
        calc
          ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁))) *
              ((1 + K / Real.log ((q : ℝ) + 1)) *
                (1 + K / Real.log ((p₁ : ℝ) + 1))) ≤
            ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁))) *
              ((101 / 100 : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hweight
          _ = ((101 / 100 : ℝ) ^ 2) *
              ((S.nu p₀ / (1 - S.nu p₀)) *
                (S.nu p₁ / (1 - S.nu p₁))) := by ring
      _ = ((101 / 100 : ℝ) ^ 2) * a p₀ p₁ := by
        dsimp [a]
        ring
  calc
    (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (rel p₀),
        (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
          (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
          ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (rel p₀),
        ((101 / 100 : ℝ) ^ 2) * a p₀ p₁ := by
          apply Finset.sum_le_sum
          intro p₀ hp₀
          apply Finset.sum_le_sum
          intro p₁ hp₁
          exact hterm p₀ hp₀ p₁ hp₁
    _ = ((101 / 100 : ℝ) ^ 2) *
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (rel p₀), a p₀ p₁) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      rw [Finset.mul_sum]
    _ ≤ ((101 / 100 : ℝ) ^ 2) * ((17 / 20 : ℝ) * r ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa [rel, a] using habs') (by positivity)
    _ ≤ (9 / 10 : ℝ) * r ^ 2 := by
      nlinarith [sq_nonneg r]

/-- Exact finite-boundary relative tail.  Once the pair depth reaches the
carrier support cutoff, division by the residual Euler product cannot revive a
vanishing boundary density.  This is the honest finite endpoint to which a
future recursive relative-iterate estimate can be attached. -/
theorem upperRosserBoundaryChainsFixedDepthRelativeDensity_eq_zero_of_carrierSupportDepth_le
    (nu : ℕ → ℝ) (D q : ℕ) (P : Finset ℕ) {k : ℕ}
    (hk : upperRosserBoundaryCarrierSupportDepth P ≤ k) :
    LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
      nu D q P k = 0 := by
  unfold LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
  rw [upperRosserBoundaryChainsFixedDepthDensity_eq_zero_of_carrierSupportDepth_le
    nu D q P hk]
  simp

/-- Every finite block beginning at the adaptive support cutoff is identically
zero on the relative Euler-product scale. -/
theorem upperRosserBoundaryChains_finiteRelativeTail_eq_zero
    (nu : ℕ → ℝ) (D q n : ℕ) (P : Finset ℕ) :
    (∑ j ∈ Finset.range n,
      LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
        nu D q P (upperRosserBoundaryCarrierSupportDepth P + j)) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply upperRosserBoundaryChainsFixedDepthRelativeDensity_eq_zero_of_carrierSupportDepth_le
  omega

end



end MathlibNt.SieveTheory.SwitchingPrinciple
