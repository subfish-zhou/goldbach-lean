import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserAdaptiveDiscreteTail

/-!
# Finite-depth geometric control of the relative upper Rosser iterate

The depth-zero state is kept as the exact quotient by the ambient Euler product.
The dimension-one local-product estimate is used once, at initialization; later
reverse-pair steps are paid by the relative Lyapunov contraction.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

/-- Depth-zero initialization, with the Euler-product denominator displayed
before it is paid by the existing local-product bound. -/
theorem upperRosserAlternatingPairDiscreteRelativeIterate_zero_eq_and_le_localProduct
    {S : BoundingSieve} {K z r : ℝ} {q : ℕ} {P : Finset ℕ}
    (hq : q.Prime) (hlocal : HasDimensionOneLocalProductBound S K)
    (hqz : (q : ℝ) ≤ z) (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hzP : ∀ p ∈ P, (p : ℝ) ≤ z) :
    upperRosserAlternatingPairDiscreteRelativeIterate S.nu 0 q r P =
        r ^ 2 / ∏ p ∈ P, (1 - S.nu p) ∧
      upperRosserAlternatingPairDiscreteRelativeIterate S.nu 0 q r P ≤
        r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) := by
  have hz₁ : (2 : ℝ) ≤ (q : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hq.one_le
  have hz₁₂ : (q : ℝ) + 1 ≤ z + 1 := by linarith
  have hinterval : ∀ p ∈ P,
      (q : ℝ) + 1 ≤ (p : ℝ) ∧ (p : ℝ) < z + 1 := by
    intro p hp
    constructor
    · exact_mod_cast Nat.succ_le_of_lt (hqP p hp)
    · linarith [hzP p hp]
  have hprod := prod_inv_one_sub_nu_le_of_subset_interval
    hlocal hz₁ hz₁₂ hP hinterval
  constructor
  · exact upperRosserAlternatingPairDiscreteRelativeIterate_zero S.nu q r P
  · rw [upperRosserAlternatingPairDiscreteRelativeIterate_zero]
    calc
      r ^ 2 / ∏ p ∈ P, (1 - S.nu p) =
          r ^ 2 * ∏ p ∈ P, (1 - S.nu p)⁻¹ := by
            rw [div_eq_mul_inv, Finset.prod_inv_distrib]
      _ ≤ r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg r)

/-- Finite-depth geometric estimate for the relative reverse-pair state.

The prefactor is exactly the one-time initialization cost of the depth-zero
Euler-product denominator.  It is not charged again at recursive depths. -/
theorem exists_upperRosserAlternatingPairDiscreteRelativeIterate_finiteDepth_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k q : ℕ) (r z : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → (q : ℝ) ≤ z →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        upperRosserAlternatingPairDiscreteRelativeIterate S.nu k q r P ≤
          (101 / 100 : ℝ) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
              (9 / 10 : ℝ) ^ k * r ^ 2 := by
  obtain ⟨Q₀, hQ₀, hstep⟩ := UpperRosserRelativeLyapunovOneStepContraction K hK
  obtain ⟨Q₁, hQ₁, herr⟩ := exists_localProductError_le_one_hundredth K hK
  let Q := max Q₀ Q₁
  refine ⟨Q, hQ₀.trans (le_max_left _ _), ?_⟩
  intro S k
  induction k with
  | zero =>
      intro q r z P hQq hqPrime hlocal hr hqz hP hqP hzP
      have hQ₁q : Q₁ ≤ (q : ℝ) := (le_max_right _ _).trans hQq
      have hinit :=
        (upperRosserAlternatingPairDiscreteRelativeIterate_zero_eq_and_le_localProduct
          (r := r) hqPrime hlocal hqz hP hqP hzP).2
      have herrq : K / Real.log ((q : ℝ) + 1) ≤ (1 / 100 : ℝ) :=
        herr q hQ₁q
      have hlogq : 0 < Real.log ((q : ℝ) + 1) :=
        Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hqPrime.pos)
      have hlogz : 0 ≤ Real.log (z + 1) := by
        have : (1 : ℝ) ≤ z + 1 := by
          have hq0 : (0 : ℝ) ≤ q := by positivity
          linarith
        exact Real.log_nonneg this
      have hratio : 0 ≤ Real.log (z + 1) / Real.log ((q : ℝ) + 1) :=
        div_nonneg hlogz hlogq.le
      rw [pow_zero, mul_one]
      calc
        upperRosserAlternatingPairDiscreteRelativeIterate S.nu 0 q r P ≤
            r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
              (1 + K / Real.log ((q : ℝ) + 1))) := hinit
        _ ≤ (101 / 100 : ℝ) *
              (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) * r ^ 2 := by
          calc
            r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
                (1 + K / Real.log ((q : ℝ) + 1))) =
              (r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1))) *
                (1 + K / Real.log ((q : ℝ) + 1)) := by ring
            _ ≤ (r ^ 2 * (Real.log (z + 1) / Real.log ((q : ℝ) + 1))) *
                (101 / 100 : ℝ) :=
              mul_le_mul_of_nonneg_left (by linarith)
                (mul_nonneg (sq_nonneg r) hratio)
            _ = _ := by ring
  | succ k ih =>
      intro q r z P hQq hqPrime hlocal hr hqz hP hqP hzP
      have hQ₀q : Q₀ ≤ (q : ℝ) := (le_max_left _ _).trans hQq
      have hfactor_pos : ∀ p ∈ P, 0 < 1 - S.nu p := by
        intro p hp
        have hpS := hP hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
        have hpDvd : p ∣ S.prodPrimes :=
          (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
        exact sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd)
      have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 :=
        fun p hp => ne_of_gt (hfactor_pos p hp)
      rw [show k + 1 = k.succ by rfl,
        upperRosserAlternatingPairDiscreteRelativeIterate_succ S.nu hfactor]
      let A : ℝ := (101 / 100 : ℝ) *
        (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) * (9 / 10 : ℝ) ^ k
      have hA : 0 ≤ A := by
        have hlogq : 0 < Real.log ((q : ℝ) + 1) :=
          Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hqPrime.pos)
        have hlogz : 0 ≤ Real.log (z + 1) := by
          apply Real.log_nonneg
          have hq0 : (0 : ℝ) ≤ q := by positivity
          linarith
        dsimp [A]
        positivity
      have hterms :
          (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
              upperRosserAlternatingPairDiscreteRelativeIterate S.nu k p₀
                ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q))
                (P.filter (fun p => p₀ < p))) ≤
          A * (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
              (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
                ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p₀ hp₀
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p₁ hp₁
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₀Prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
        have hp₁Prime : p₁.Prime := Nat.prime_of_mem_primeFactors (hP hp₁'.1)
        have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
        have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀Prime.pos
        have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
        have hlogq : 0 < Real.log q :=
          Real.log_pos (by exact_mod_cast hqPrime.one_lt)
        have hlogp₀ : 0 < Real.log p₀ :=
          Real.log_pos (by exact_mod_cast hp₀Prime.one_lt)
        have hlogp₀one : 0 < Real.log ((p₀ : ℝ) + 1) :=
          Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hp₀Prime.pos)
        have hy : Real.log p₁ / Real.log q ∈ Set.Ioo (1 : ℝ) r := by
          have hqy : Real.log q < Real.log p₁ :=
            (Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
              (by exact_mod_cast hqP p₁ hp₁'.1)
          have hyx : Real.log p₁ / Real.log q < Real.log p₀ / Real.log q := by
            apply (div_lt_div_iff_of_pos_right hlogq).2
            exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
              (by exact_mod_cast hp₁'.2.1)
          exact ⟨(lt_div_iff₀ hlogq).2 (by simpa using hqy), by linarith [hp₁'.2.2, hyx]⟩
        have hx : Real.log p₀ / Real.log q ∈
            Set.Ioo (Real.log p₁ / Real.log q)
              ((Real.log p₁ / Real.log q + r) / 2) := by
          constructor
          · apply (div_lt_div_iff_of_pos_right hlogq).2
            exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
              (by exact_mod_cast hp₁'.2.1)
          · linarith [hp₁'.2.2]
        have hnext : 3 ≤
            (r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q) :=
          (LinearSieve.upperRosserAlternatingPair_nextRatio_gt_three hy hx).le
        have hQp₀ : Q ≤ (p₀ : ℝ) :=
          hQq.trans (by exact_mod_cast (hqP p₀ hp₀).le)
        have hqz₀ : (p₀ : ℝ) ≤ z := hzP p₀ hp₀
        have hiter := ih p₀
          ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) z (P.filter (fun p => p₀ < p))
          hQp₀ hp₀Prime hlocal hnext hqz₀
          (fun p hp => hP (Finset.mem_filter.mp hp).1)
          (fun p hp => (Finset.mem_filter.mp hp).2)
          (fun p hp => hzP p (Finset.mem_filter.mp hp).1)
        have hp₀addpos : (0 : ℝ) < (p₀ : ℝ) + 1 := by linarith
        have hlogmono : Real.log p₀ ≤ Real.log ((p₀ : ℝ) + 1) :=
          Real.strictMonoOn_log.monotoneOn hp₀pos hp₀addpos (by linarith)
        have hscale :
            (101 / 100 : ℝ) *
                (Real.log (z + 1) / Real.log ((p₀ : ℝ) + 1)) *
                  (9 / 10 : ℝ) ^ k ≤
              A * (Real.log ((q : ℝ) + 1) / Real.log p₀) := by
          have hlogqone : 0 < Real.log ((q : ℝ) + 1) :=
            Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hqPrime.pos)
          have hlogz : 0 ≤ Real.log (z + 1) := by
            apply Real.log_nonneg
            have hq0 : (0 : ℝ) ≤ q := by positivity
            linarith
          dsimp [A]
          have : Real.log p₀ / Real.log ((p₀ : ℝ) + 1) ≤ 1 :=
            (div_le_one hlogp₀one).2 hlogmono
          field_simp [hlogqone.ne', hlogp₀.ne', hlogp₀one.ne']
          nlinarith [show 0 ≤ (9 / 10 : ℝ) ^ k by positivity]
        have htransition : 0 ≤
            upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ := by
          unfold upperRosserAlternatingPairDiscreteRelativeTransition
          have hnu₀ : 0 ≤ S.nu p₀ := by
            have hpDvd : p₀ ∣ S.prodPrimes :=
              (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp (hP hp₀) |>.2
            exact (S.nu_pos_of_prime p₀ hp₀Prime hpDvd).le
          have hnu₁ : 0 ≤ S.nu p₁ := by
            have hpDvd : p₁ ∣ S.prodPrimes :=
              (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp (hP hp₁'.1) |>.2
            exact (S.nu_pos_of_prime p₁ hp₁Prime hpDvd).le
          have hres : 0 ≤ ∏ p ∈ P.filter (fun p => p₀ < p), (1 - S.nu p) := by
            apply Finset.prod_nonneg
            intro p hp
            exact (hfactor_pos p (Finset.mem_filter.mp hp).1).le
          have hamb : 0 ≤ ∏ p ∈ P, (1 - S.nu p) := by
            apply Finset.prod_nonneg
            intro p hp
            exact (hfactor_pos p hp).le
          exact div_nonneg (mul_nonneg (mul_nonneg hnu₀ hnu₁) hres) hamb
        calc
          upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
              upperRosserAlternatingPairDiscreteRelativeIterate S.nu k p₀
                ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) (P.filter (fun p => p₀ < p)) ≤
            upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
              (((101 / 100 : ℝ) *
                (Real.log (z + 1) / Real.log ((p₀ : ℝ) + 1)) *
                  (9 / 10 : ℝ) ^ k) *
                ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2) :=
            mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hiter) htransition
          _ ≤ A * ((upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
                (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
              ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) := by
            have hrsq : 0 ≤ ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2 := sq_nonneg _
            calc
              upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
                    (((101 / 100 : ℝ) *
                      (Real.log (z + 1) / Real.log ((p₀ : ℝ) + 1)) *
                        (9 / 10 : ℝ) ^ k) *
                      ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                        (Real.log p₀ / Real.log q)) ^ 2) =
                  (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
                    ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                      (Real.log p₀ / Real.log q)) ^ 2) *
                    ((101 / 100 : ℝ) *
                      (Real.log (z + 1) / Real.log ((p₀ : ℝ) + 1)) *
                        (9 / 10 : ℝ) ^ k) := by ring
              _ ≤ (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
                    ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                      (Real.log p₀ / Real.log q)) ^ 2) *
                    (A * (Real.log ((q : ℝ) + 1) / Real.log p₀)) :=
                mul_le_mul_of_nonneg_left hscale (mul_nonneg htransition hrsq)
              _ = A * ((upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
                    (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
                  ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q)) ^ 2) := by ring
      have hone := hstep S q r P hQ₀q hqPrime hlocal hr hP hqP
      calc
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧ 2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
          upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
            upperRosserAlternatingPairDiscreteRelativeIterate S.nu k p₀
              ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) (P.filter (fun p => p₀ < p))) ≤
          A * (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧ 2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
          (upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
            (Real.log ((q : ℝ) + 1) / Real.log p₀)) *
              ((r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) := hterms
        _ ≤ A * ((9 / 10 : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_left hone hA
        _ = (101 / 100 : ℝ) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
              (9 / 10 : ℝ) ^ (k + 1) * r ^ 2 := by
          dsimp [A]
          rw [pow_succ]
          ring

/-- Consumer for the actual fixed-depth boundary-chain relative density. -/
theorem exists_upperRosserBoundaryChainsFixedDepthRelativeDensity_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k q : ℕ) (z Δ s : ℝ),
        Q ≤ q → 2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          9 * (101 / 100 : ℝ) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
              (9 / 10 : ℝ) ^ k := by
  obtain ⟨Q, hQ, hiterate⟩ :=
    exists_upperRosserAlternatingPairDiscreteRelativeIterate_finiteDepth_geometric K hK
  refine ⟨Q, hQ, ?_⟩
  intro S k q z Δ s hQq hz hΔ hs hlocal hcut hq
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqz : (q : ℝ) ≤ z := hcut q hq
  have hembed :=
    upperRosserBoundaryChainsFixedDepthRelativeDensity_le_alternatingPairDiscreteRelativeIterate
      (k := k) hz hΔ hs hcut hq
  have hbound := hiterate S k q 3 z P hQq hqPrime hlocal (by norm_num) hqz
    (fun p hp => (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hcut p (Finset.mem_filter.mp hp).1)
  calc
    LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
        S.nu (Nat.floor Δ + 1) q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
      upperRosserAlternatingPairDiscreteRelativeIterate S.nu k q 3 P := by
        simpa [P] using hembed
    _ ≤ (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ k * 3 ^ 2 := hbound
    _ = 9 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ k := by ring

/-- Every finite block of relative boundary layers has a geometric tail bound.
The remaining logarithmic prefactor is precisely the one-time depth-zero
initialization cost; this statement does not mislabel it as carrier-uniform. -/
theorem exists_upperRosserBoundaryChains_finiteRelativeBlock_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (L n q : ℕ) (z Δ s : ℝ),
        Q ≤ q → 2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        (∑ j ∈ Finset.range n,
          LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
          90 * (101 / 100 : ℝ) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
              (9 / 10 : ℝ) ^ L := by
  obtain ⟨Q, hQ, hdepth⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthRelativeDensity_geometric K hK
  refine ⟨Q, hQ, ?_⟩
  intro S L n q z Δ s hQq hz hΔ hs hlocal hcut hq
  have hterms :
      (∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
        ∑ j ∈ Finset.range n,
          9 * (101 / 100 : ℝ) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
              (9 / 10 : ℝ) ^ (L + j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hdepth S (L + j) q z Δ s hQq hz hΔ hs hlocal hcut hq
  have hgeom : (∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j) ≤ 10 := by
    calc
      (∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j) ≤
          ∑' j : ℕ, (9 / 10 : ℝ) ^ j :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum
          (Finset.range n) (by intro j hj; positivity)
      _ = (1 - (9 / 10 : ℝ))⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)
      _ = 10 := by norm_num
  have hlogq : 0 < Real.log ((q : ℝ) + 1) := by
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
    exact Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hqPrime.pos)
  have hlogz : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
  have hcoef : 0 ≤ 9 * (101 / 100 : ℝ) *
      (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
        (9 / 10 : ℝ) ^ L := by positivity
  calc
    (∑ j ∈ Finset.range n,
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
          S.nu (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) (L + j)) ≤
      ∑ j ∈ Finset.range n,
        9 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ (L + j) := hterms
    _ = (9 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ L) *
          ∑ j ∈ Finset.range n, (9 / 10 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ ≤ (9 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ L) * 10 :=
      mul_le_mul_of_nonneg_left hgeom hcoef
    _ = 90 * (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ L := by ring


end

end MathlibNt.SieveTheory.SwitchingPrinciple
