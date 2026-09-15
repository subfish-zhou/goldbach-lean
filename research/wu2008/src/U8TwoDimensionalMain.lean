import U8TruncatedSelberg

/-! Concrete weights and actual dimension-two main matrix. The CRT count-to-main
replacement is not assumed here. All constants and cutoffs are universal variables. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct.TwoDimensional
open TruncatedSelberg

def rootCount (N d : ℕ) : ℝ := ∏ p ∈ d.primeFactors, roots N p

def optimalWeight (N : ℕ) (hN : Even N) (Z R : ℝ) : ℕ → ℝ :=
  weight (model N hN Z) R

def mainMatrix (N : ℕ) (Z R : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ carrier Z R, ∑ f ∈ carrier Z R,
    w d * w f * rootCount N (Nat.lcm d f) / Nat.lcm d f

theorem density_eq (N : ℕ) {d : ℕ} (hd : Squarefree d) :
    density N d = rootCount N d / d := by
  rw [density, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    Finset.prod_div_distrib]
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]
  rfl

theorem rootCount_one_le (N d : ℕ) : 1 ≤ rootCount N d := by
  apply Finset.one_le_prod
  intro p _
  exact roots_le N p

theorem denominator_eq (N : ℕ) (hN : Even N) (Z R : ℝ) :
    G (model N hN Z) R = denominator N Z R := by
  apply sum_congr rfl
  intro d hd
  exact term_eq N hN Z (Nat.mem_divisors.mp (mem_filter.mp hd).1).1

theorem optimalWeight_one (N : ℕ) (hN : Even N) (Z : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    optimalWeight N hN Z R 1 = 1 := weight_one _ hR

theorem optimalWeight_support (N : ℕ) (hN : Even N) (Z R : ℝ) {d : ℕ}
    (hd : optimalWeight N hN Z R d ≠ 0) :
    d ∣ (sievePrimes Z).prod id ∧ (d : ℝ) ≤ R := by
  have h := weight_support (model N hN Z) hd
  exact ⟨(Nat.mem_divisors.mp (mem_filter.mp h).1).1, (mem_filter.mp h).2⟩

/-- Uniform elementary bound suitable for a polynomial CRT remainder. -/
theorem optimalWeight_abs_le (N : ℕ) (hN : Even N) (Z : ℝ) {R : ℝ}
    (hR : 1 ≤ R) (d : ℕ) : |optimalWeight N hN Z R d| ≤ d := by
  by_cases hw : optimalWeight N hN Z R d = 0
  · rw [hw, abs_zero]
    exact Nat.cast_nonneg d
  have hd := (optimalWeight_support N hN Z R hw).1
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (sievePrimes_prod_ne_zero Z) hd
  have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hs := (primorial_squarefree Z).squarefree_of_dvd hd
  have hc := rootCount_one_le N d
  calc
    _ ≤ 1 / density N d := abs_weight_le_inv (model N hN Z) hR hd
    _ = (d : ℝ) / rootCount N d := by rw [density_eq N hs]; field_simp
    _ ≤ d := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)).mpr (by nlinarith)

theorem mainMatrix_eq_mainSum (N : ℕ) (hN : Even N) (Z R : ℝ) :
    mainMatrix N Z R (optimalWeight N hN Z R) =
      (model N hN Z).mainSum (BoundingSieve.lambdaSquared (optimalWeight N hN Z R)) := by
  let S := model N hN Z
  let w := optimalWeight N hN Z R
  have hloc (d f : ℕ) (hd : d ∈ S.prodPrimes.divisors) (hf : f ∈ S.prodPrimes.divisors) :
      w d * w f * rootCount N (Nat.lcm d f) / Nat.lcm d f =
      S.nu d * w d * S.nu f * w f * (S.nu (Nat.gcd d f))⁻¹ := by
    have hl := Nat.lcm_dvd (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp hf).1
    have hg := (Nat.gcd_dvd_left d f).trans (Nat.mem_divisors.mp hd).1
    rw [mul_div_assoc]
    rw [show rootCount N (Nat.lcm d f) / (Nat.lcm d f : ℝ) = S.nu (Nat.lcm d f) from
      (density_eq N (S.squarefree_of_dvd_prodPrimes hl)).symm] at ⊢
    rw [S.nu_mult.map_lcm (S.nu_ne_zero hg)]
    ring
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_sum_mul]
  unfold mainMatrix carrier
  simp only [sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hdR : (d : ℝ) ≤ R
  · rw [if_pos hdR]
    apply sum_congr rfl
    intro f hf
    by_cases hfR : (f : ℝ) ≤ R
    · rw [if_pos hfR]
      exact hloc d f hd hf
    · have hf0 : w f = 0 := weight_zero S (Or.inr (lt_of_not_ge hfR))
      simp [hfR, show optimalWeight N hN Z R f = 0 from hf0]
  · have hd0 : w d = 0 := weight_zero S (Or.inr (lt_of_not_ge hdR))
    simp [hdR, show optimalWeight N hN Z R d = 0 from hd0]

/-- The optimizer attains the reciprocal of the true two-dimensional denominator. -/
theorem mainMatrix_optimal (N : ℕ) (hN : Even N) (Z : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    mainMatrix N Z R (optimalWeight N hN Z R) = 1 / denominator N Z R := by
  rw [mainMatrix_eq_mainSum]
  change (model N hN Z).mainSum (BoundingSieve.lambdaSquared (weight (model N hN Z) R)) = _
  rw [main_eq _ hR, denominator_eq]

theorem carrier_eq_squarefree {Z R : ℝ} (hRZ : R < Z) :
    carrier Z R = (Finset.Icc 1 ⌊R⌋₊).filter Squarefree := by
  classical
  ext d
  simp only [carrier, mem_filter, Nat.mem_divisors, mem_Icc]
  constructor
  · rintro ⟨⟨hd,_⟩,hdR⟩
    have hs := (primorial_squarefree Z).squarefree_of_dvd hd
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hs.ne_zero, Nat.le_floor hdR⟩,hs⟩
  · rintro ⟨⟨_,hdR⟩,hs⟩
    have hdR' : (d : ℝ) ≤ R := (Nat.le_floor_iff' hs.ne_zero).mp hdR
    have hsub : d.primeFactors ⊆ sievePrimes Z := by
      intro p hp
      have hpd : (p : ℝ) ≤ d := by
        exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero)
          (Nat.dvd_of_mem_primeFactors hp))
      exact mem_sievePrimes.mpr ⟨Nat.prime_of_mem_primeFactors hp,
        hpd.trans_lt (hdR'.trans_lt hRZ)⟩
    refine ⟨⟨?_,sievePrimes_prod_ne_zero Z⟩,hdR'⟩
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- Any fixed positive exponent below the original alpha is a legal small-support
choice under the unchanged cube-root sieve prime carrier. -/
theorem power_cutoff_legal {N : ℕ} (hN : 1 < N) {β : ℝ}
    (hβ : 0 < β) (hβα : β < originalAlpha) :
    1 ≤ (N : ℝ)^β ∧ (N : ℝ)^β < (N : ℝ)^originalAlpha ∧
      (N : ℝ)^β < (N : ℝ)^(1/3 : ℝ) := by
  have hN' : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨Real.one_le_rpow hN'.le hβ.le,
    Real.rpow_lt_rpow_of_exponent_lt hN' hβα, ?_⟩
  apply Real.rpow_lt_rpow_of_exponent_lt hN'
  exact hβα.trans (by norm_num [originalAlpha])

end U8Literal.SmallProduct.TwoDimensional
