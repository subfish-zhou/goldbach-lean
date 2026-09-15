import U8TwoLinearInterval

noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct

/-- Signed, actual count-minus-CRT-main-term remainder, not a supplied error hypothesis. -/
def quadraticRemainder (N : ℕ) (e : ℝ) (t : ℕ × ℕ) (D : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ f ∈ D, w d*w f * ((divisibilityCount N e t d f : ℝ) -
    (interval N e t).card * (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ)/(Nat.lcm d f))

/-- Exact decomposition for arbitrary real weights, including signed cross terms. -/
theorem quadratic_eq_main_add_remainder (N : ℕ) (e : ℝ) (t : ℕ × ℕ)
    (D : Finset ℕ) (w : ℕ → ℝ) :
    quadratic N e t D w = (interval N e t).card *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f *
        (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ)/(Nat.lcm d f)) +
      quadraticRemainder N e t D w := by
  unfold quadratic quadraticRemainder
  simp_rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro f _
  ring

/-- Triangle inequality is applied before any comparison; no sign assumption on weights. -/
theorem quadraticRemainder_abs_le (N : ℕ) (e : ℝ) (t : ℕ × ℕ)
    (D : Finset ℕ) (w : ℕ → ℝ) (hD : ∀ d ∈ D, d ≠ 0) :
    |quadraticRemainder N e t D w| ≤
      2 * ∑ d ∈ D, ∑ f ∈ D, |w d| *|w f| *
        (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ) := by
  unfold quadraticRemainder
  calc
    _ ≤ ∑ d ∈ D, |∑ f ∈ D, w d*w f * ((divisibilityCount N e t d f : ℝ) -
        (interval N e t).card * (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ)/(Nat.lcm d f))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ f ∈ D, |w d| *|w f| *
        (2*(residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ)) := by
      apply sum_le_sum
      intro d hd
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro f hf
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (divisibilityCount_error N d f (hD d hd) (hD f hf) e t)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro f _
      ring

/-- On actual small-prime-supported sieve divisors, the main kernel is the canonical nu_N. -/
theorem quadratic_eq_nuN_add_remainder {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hZ : Z ≤ (N : ℝ)^originalAlpha)
    (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id) :
    quadratic N e t D w = (interval N e t).card *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f * (nuN N (Nat.lcm d f) : ℝ)/(Nat.lcm d f)) +
      quadraticRemainder N e t D w := by
  rw [quadratic_eq_main_add_remainder]
  congr 2
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro f hf
  rw [small_sieve_rootCount ht (Nat.lcm_dvd (hD d hd) (hD f hf)) hZ]

/-- The same genuine remainder has a pair-independent small-support bound. -/
theorem quadraticRemainder_abs_le_nuN {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (hZ : Z ≤ (N : ℝ)^originalAlpha)
    (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id) :
    |quadraticRemainder N e t D w| ≤
      2*∑ d ∈ D, ∑ f ∈ D, |w d| *|w f| *(nuN N (Nat.lcm d f) : ℝ) := by
  apply (quadraticRemainder_abs_le N e t D w
    (fun d hd => ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) (hD d hd))).trans_eq
  congr 1
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro f hf
  rw [small_sieve_rootCount ht (Nat.lcm_dvd (hD d hd) (hD f hf)) hZ]

/-- A useful height contract, proved without selecting or optimizing weights. -/
theorem quadraticRemainder_abs_le_height (N : ℕ) (e : ℝ) (t : ℕ × ℕ)
    (D : Finset ℕ) (w : ℕ → ℝ) (hD : ∀ d ∈ D, d ≠ 0) :
    |quadraticRemainder N e t D w| ≤ 2*(∑ d ∈ D, |w d| *(d : ℝ))^2 := by
  apply (quadraticRemainder_abs_le N e t D w hD).trans
  rw [pow_two, sum_mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply sum_le_sum
  intro d hd
  apply sum_le_sum
  intro f hf
  have : NeZero (Nat.lcm d f) := ⟨Nat.lcm_ne_zero (hD d hd) (hD f hf)⟩
  have hl : Nat.lcm d f ≤ d*f := Nat.le_of_dvd
    (Nat.mul_pos (Nat.pos_of_ne_zero (hD d hd)) (Nat.pos_of_ne_zero (hD f hf)))
    (Nat.lcm_dvd (dvd_mul_right d f) (dvd_mul_left f d))
  have hroot : (residueRootCount (Nat.lcm d f) N (t.1*t.2) : ℝ) ≤ (d : ℝ)*f := by
    exact_mod_cast (residueRootCount_le (Nat.lcm d f) N (t.1*t.2)).trans hl
  calc
    _ ≤ |w d| *|w f| *((d : ℝ)*f) := mul_le_mul_of_nonneg_left hroot
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

/-- A coarse explicit polynomial error under the stated (not asserted) weight-height contract. -/
theorem quadraticRemainder_abs_le_polynomial (N R : ℕ) (e : ℝ) (t : ℕ × ℕ)
    (D : Finset ℕ) (w : ℕ → ℝ) (hD : ∀ d ∈ D, d ≠ 0)
    (hR : ∀ d ∈ D, d ≤ R) (hw : ∀ d ∈ D, |w d| ≤ d) :
    |quadraticRemainder N e t D w| ≤ 2*((R : ℝ)+1)^2*(R : ℝ)^4 := by
  have hcard : D.card ≤ R+1 := by
    apply (card_le_card (show D ⊆ range (R+1) from fun d hd => mem_range.mpr (by
      have := hR d hd; omega))).trans_eq
    exact card_range _
  have hsum : (∑ d ∈ D, |w d| *(d : ℝ)) ≤ ((R : ℝ)+1)*(R : ℝ)^2 := by
    calc
      _ ≤ ∑ _d ∈ D, (R : ℝ)^2 := by
        apply sum_le_sum
        intro d hd
        have hdR : (d : ℝ) ≤ R := by exact_mod_cast hR d hd
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith [hw d hd, abs_nonneg (w d)]
      _ = (D.card : ℝ)*(R : ℝ)^2 := by simp
      _ ≤ ((R : ℝ)+1)*(R : ℝ)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast hcard
  have hsum0 : 0 ≤ ∑ d ∈ D, |w d| *(d : ℝ) := sum_nonneg fun d _ =>
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg d)
  have hb := quadraticRemainder_abs_le_height N e t D w hD
  nlinarith [sq_le_sq₀ hsum0 (by positivity : 0 ≤ ((R : ℝ)+1)*(R : ℝ)^2) |>.mpr hsum]

/-- The CRT product is the actual main term on every legal finite sieve support. -/
theorem quadratic_eq_CRT_product_add_remainder {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id) :
    quadratic N e t D w = (interval N e t).card *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f *
        ((∏ p ∈ (Nat.lcm d f).primeFactors, if p ∣ (t.1*t.2)*N then 1 else 2 : ℕ) : ℝ) /
        (Nat.lcm d f)) + quadraticRemainder N e t D w := by
  rw [quadratic_eq_main_add_remainder]
  congr 2
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro f hf
  rw [residueRootCount_original ht (sieve_lcm_squarefree (hD d hd) (hD f hf))]

/-- Pair-independent kernel without changing the original sieve cutoff. -/
theorem quadratic_eq_nuN_of_small_support {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id)
    (hs : ∀ d ∈ D, ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha) :
    quadratic N e t D w = (interval N e t).card *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f * (nuN N (Nat.lcm d f) : ℝ)/(Nat.lcm d f)) +
      quadraticRemainder N e t D w := by
  rw [quadratic_eq_main_add_remainder]
  congr 2
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro f hf
  rw [lcm_rootCount_small_support ht (hD d hd) (hD f hf) (hs d hd) (hs f hf)]

/-- The inherited finite prime windows place every original pair in a genuine box. -/
theorem pairs_subset_box (N : ℕ) (e : ℝ) :
    pairs N e ⊆ (range (N+1)) ×ˢ (range (N+1)) := by
  intro t ht
  obtain ⟨ht,_⟩ := mem_filter.mp ht
  obtain ⟨ht,_⟩ := mem_filter.mp ht
  obtain ⟨ht,_⟩ := mem_filter.mp ht
  obtain ⟨ha,hb⟩ := mem_product.mp ht
  have ha' := (Wu2008DoubleSieve.mem_primeWindow.mp ha).2.2.2
  have hb' := (Wu2008DoubleSieve.mem_primeWindow.mp hb).2.2.2
  exact mem_product.mpr ⟨mem_range.mpr (by exact_mod_cast ha'),
    mem_range.mpr (by exact_mod_cast hb')⟩

/-- Deliberately coarse, but a proved bound for the full original pair range. -/
theorem pairs_card_le_box (N : ℕ) (e : ℝ) : (pairs N e).card ≤ (N+1)^2 := by
  exact (card_le_card (pairs_subset_box N e)).trans_eq (by rw [card_product, card_range, pow_two])

/-- Total genuine remainder over all original pairs, with explicit polynomial R dependence. -/
theorem sum_quadraticRemainder_abs_le_polynomial (N R : ℕ) (e : ℝ)
    (D : Finset ℕ) (w : ℕ → ℝ) (hD : ∀ d ∈ D, d ≠ 0)
    (hR : ∀ d ∈ D, d ≤ R) (hw : ∀ d ∈ D, |w d| ≤ d) :
    |∑ t ∈ pairs N e, quadraticRemainder N e t D w| ≤
      2*((N : ℝ)+1)^2*((R : ℝ)+1)^2*(R : ℝ)^4 := by
  calc
    _ ≤ ∑ t ∈ pairs N e, |quadraticRemainder N e t D w| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ pairs N e, 2*((R : ℝ)+1)^2*(R : ℝ)^4 :=
      sum_le_sum fun t _ => quadraticRemainder_abs_le_polynomial N R e t D w hD hR hw
    _ = (pairs N e).card * (2*((R : ℝ)+1)^2*(R : ℝ)^4) := by simp
    _ ≤ ((N : ℝ)+1)^2 * (2*((R : ℝ)+1)^2*(R : ℝ)^4) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast pairs_card_le_box N e
    _ = _ := by ring

/-- Exact sum over original pairs, with the canonical common kernel factored out. -/
theorem sum_quadratic_eq_nuN_of_small_support {N : ℕ} {e Z : ℝ}
    (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id)
    (hs : ∀ d ∈ D, ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha) :
    (∑ t ∈ pairs N e, quadratic N e t D w) =
      (∑ t ∈ pairs N e, ((interval N e t).card : ℝ)) *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f * (nuN N (Nat.lcm d f) : ℝ)/(Nat.lcm d f)) +
      ∑ t ∈ pairs N e, quadraticRemainder N e t D w := by
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  exact quadratic_eq_nuN_of_small_support ht D w hD hs

/-- An actual finite smallPrefix bound, not a normalized sigma-payment theorem.
The cube-root sieve and alpha remain unchanged. The weight contract is an explicit input. -/
theorem smallPrefix_card_le_CRT_nuN_polynomial (N R : ℕ) (e : ℝ)
    (hN : 4 ≤ N) (he : e ≤ 1/2) (D : Finset ℕ) (w : ℕ → ℝ) (h1 : 1 ∈ D)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes ((N : ℝ)^(1/3 : ℝ))).prod id) (hw1 : w 1 = 1)
    (hs : ∀ d ∈ D, ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha)
    (hR : ∀ d ∈ D, d ≤ R) (hw : ∀ d ∈ D, |w d| ≤ d) :
    ((smallPrefix N e).card : ℝ) ≤
      (∑ t ∈ pairs N e, ((interval N e t).card : ℝ)) *
      (∑ d ∈ D, ∑ f ∈ D, w d*w f * (nuN N (Nat.lcm d f) : ℝ)/(Nat.lcm d f)) +
      2*((N : ℝ)+1)^2*((R : ℝ)+1)^2*(R : ℝ)^4 := by
  have hbase := smallPrefix_card_le_cubeRootQuadratic N e hN he D w h1 hD hw1
  rw [sum_quadratic_eq_nuN_of_small_support D w hD hs] at hbase
  have hnonzero : ∀ d ∈ D, d ≠ 0 := fun d hd =>
    ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero _) (hD d hd)
  have herr := sum_quadraticRemainder_abs_le_polynomial N R e D w hnonzero hR hw
  exact hbase.trans (add_le_add le_rfl ((le_abs_self _).trans herr))

/-- The absolute CRT error also has the common numerator on independently small support. -/
theorem quadraticRemainder_abs_le_nuN_of_small_support {N : ℕ} {e Z : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ pairs N e) (D : Finset ℕ) (w : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ∣ (sievePrimes Z).prod id)
    (hs : ∀ d ∈ D, ∀ p ∈ d.primeFactors, (p : ℝ) < (N : ℝ)^originalAlpha) :
    |quadraticRemainder N e t D w| ≤
      2 * ∑ d ∈ D, ∑ f ∈ D, |w d| * |w f| * (nuN N (Nat.lcm d f) : ℝ) := by
  apply (quadraticRemainder_abs_le N e t D w
    (fun d hd => ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) (hD d hd))).trans_eq
  congr 1
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro f hf
  rw [lcm_rootCount_small_support ht (hD d hd) (hD f hf) (hs d hd) (hs f hf)]

end U8Literal.SmallProduct
