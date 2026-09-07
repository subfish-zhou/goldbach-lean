import MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalyticMass

/-!
# Euler-normalized analytic scale for the actual boundary mass

The constant is absolute, and the original dimension-one constant is
retained in `exp (6*K+2)`. No threshold is allowed to depend on `K`.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset SmallRosser
open scoped Classical

namespace BoundaryAnalytic

theorem boundary_scalar {ε L K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL : 0 < L) (hK : 0 ≤ K) (ht : 1 ≤ ε ^ 2 * L) :
    2 * ((1 + K / (ε ^ 2 * L)) / ε ^ 2) ^ 3 *
        (3 * ε ^ 7 + 2 * K / (ε ^ 2 * L)) ≤
      10 * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
        L ^ (-(1 / 3 : ℝ))) := by
  let t := ε ^ 2 * L
  let x := t ^ (-(1 / 3 : ℝ))
  let H := Real.exp (6 * K + 2)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hx0 : 0 ≤ x := Real.rpow_nonneg ht0.le _
  have hi0 : 0 ≤ t⁻¹ := inv_nonneg.mpr ht0.le
  have hi1 : t⁻¹ ≤ 1 := (inv_le_one₀ ht0).mpr ht
  have hix : t⁻¹ ≤ x := by
    calc
      t⁻¹ = t ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have hi2 : t⁻¹ ^ 2 ≤ x := by nlinarith
  have hi3 : t⁻¹ ^ 3 ≤ x := by
    have hh : t⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hi0 hi1
    have hm := mul_le_mul_of_nonneg_right hh hi0
    nlinarith
  have he : 1 + K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have he3 : (1 + K) ^ 3 ≤ Real.exp (3 * K) := by
    calc
      _ ≤ Real.exp K ^ 3 := pow_le_pow_left₀ (by linarith) he 3
      _ = _ := by
        rw [show 3 * K = K + K + K by ring, Real.exp_add, Real.exp_add]
        ring
  have hf : (1 + K / t) ^ 3 ≤ 1 + Real.exp (3 * K) * x := by
    have h1 := mul_le_mul_of_nonneg_left hix (show 0 ≤ 3 * K by positivity)
    have h2 := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ 3 * K ^ 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hi3 (pow_nonneg hK 3)
    have h4 := mul_le_mul_of_nonneg_right he3 hx0
    rw [div_eq_mul_inv]
    nlinarith
  have hf' : (1 + K / t) ^ 3 ≤ Real.exp (3 * K) := by
    apply le_trans _ he3
    apply pow_le_pow_left₀ (by positivity)
    have hm := mul_le_mul_of_nonneg_left hi1 hK
    rw [div_eq_mul_inv]
    linarith
  have htail : K / t * (1 + K / t) ^ 3 ≤ Real.exp (4 * K) * x := by
    have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hix hK) hf'
      (by positivity : 0 ≤ (1 + K / t) ^ 3) (mul_nonneg hK hx0)
    have hKexp : K ≤ Real.exp K := by linarith
    have hm := mul_le_mul_of_nonneg_right hKexp
      (mul_nonneg (Real.exp_pos (3 * K)).le hx0)
    have hid : Real.exp (4 * K) = Real.exp K * Real.exp (3 * K) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hid, div_eq_mul_inv]
    simp only [div_eq_mul_inv] at hmul
    nlinarith
  have h3H : Real.exp (3 * K) ≤ H := Real.exp_le_exp.mpr (by linarith)
  have h4H : Real.exp (4 * K) ≤ H := Real.exp_le_exp.mpr (by linarith)
  have hH0 : 0 ≤ H := (Real.exp_pos _).le
  have hε6 : ε ^ 6 ≤ 1 := pow_le_one₀ hε.le hε1
  have hεinv : ε ≤ (ε ^ 6)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos hε 6)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hε6 hε.le]
  have hbudget : x / ε ^ 6 ≤ (ε ^ 8)⁻¹ * L ^ (-(1 / 3 : ℝ)) := by
    have he6 : ε ^ 6 ≤ ε ^ 2 := by
      have hh : ε ^ 4 ≤ 1 := pow_le_one₀ hε.le hε1
      nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg ε),
        show ε ^ 6 = ε ^ 2 * ε ^ 4 by ring]
    have hx : x ≤ (ε ^ 6 * L) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (mul_le_mul_of_nonneg_right he6 hL.le) (by norm_num)
    have hid : (ε ^ 6 * L) ^ (-(1 / 3 : ℝ)) =
        (ε ^ 2)⁻¹ * L ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hL.le, ← Real.rpow_natCast_mul hε.le]
      norm_num
    apply (div_le_iff₀ (pow_pos hε 6)).mpr
    rw [hid] at hx
    calc
      _ ≤ _ := hx
      _ = _ := by field_simp
  have hmain : 2 * ((1 + K / t) / ε ^ 2) ^ 3 *
      (3 * ε ^ 7 + 2 * K / t) ≤ 6 * ε + 10 * H * (x / ε ^ 6) := by
    have hfirst := mul_le_mul_of_nonneg_left hf (show 0 ≤ 6 * ε by positivity)
    have hsecond := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ 4 / ε ^ 6 by positivity)
    have hfirstH := mul_le_mul_of_nonneg_right h3H hx0
    have hsecondH := mul_le_mul_of_nonneg_right h4H hx0
    have hfirstH' := mul_le_mul_of_nonneg_left hfirstH (show 0 ≤ 6 * ε by positivity)
    have hsecondH' := mul_le_mul_of_nonneg_left hsecondH
      (show 0 ≤ 4 / ε ^ 6 by positivity)
    have hpay := mul_le_mul_of_nonneg_right hεinv (mul_nonneg hH0 hx0)
    have hid : 2 * ((1 + K / t) / ε ^ 2) ^ 3 * (3 * ε ^ 7 + 2 * K / t) =
        6 * ε * (1 + K / t) ^ 3 +
          (4 / ε ^ 6) * (K / t * (1 + K / t) ^ 3) := by
      field_simp
      ring
    rw [hid]
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 10 * H by positivity)
  dsimp [t, H] at hmain hp
  nlinarith

theorem roughPlusProduct_le_dimensionOne (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 + g p)) ≤
      (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2 := by
  have hpar := CollisionAnalytic.rough_parameters hD hε hεsmall hlarge
  have hsub : P \ geometricSmallPrimes P D ε ⊆
      P.filter (fun p : ℕ => p.Prime ∧ D ^ (ε ^ 2) ≤ (p : ℝ) ∧ (p : ℝ) < D) := by
    intro p hp
    refine mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hP p (mem_sdiff.mp hp).1,
      CollisionAnalytic.rough_prime_lower P hP D ε hp, (hcut p hp).trans_le ?_⟩
    nlinarith [Real.sq_sqrt (show 0 ≤ D by linarith), Real.sqrt_nonneg D]
  have hinv : (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)⁻¹) ≤
      (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2 := by
    have hdim' := hdim (D ^ (ε ^ 2)) D hpar.1 hpar.2.1
    rw [hpar.2.2.2] at hdim'
    have hprod : (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)⁻¹) ≤
        ∏ p ∈ P.filter (fun p : ℕ => p.Prime ∧
          D ^ (ε ^ 2) ≤ (p : ℝ) ∧ (p : ℝ) < D), (1 - g p)⁻¹ := by
      apply prod_le_prod_of_subset_of_one_le hsub
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr (hg p (mem_filter.mp (hsub hp)).1).2.le)
      · intro p hp _
        apply (one_le_inv₀ (sub_pos.mpr (hg p (mem_filter.mp hp).1).2)).mpr
        linarith [(hg p (mem_filter.mp hp).1).1]
    have hid : Real.log D / (ε ^ 2 * Real.log D) *
        (1 + K / (ε ^ 2 * Real.log D)) =
          (1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2 := by
      field_simp [ne_of_gt hpar.2.2.1]
    rw [hid] at hdim'
    exact hprod.trans hdim'
  apply le_trans _ hinv
  apply prod_le_prod
  · intro p hp
    linarith [(hg p (mem_sdiff.mp hp).1).1]
  · intro p hp
    have hgp := hg p (mem_sdiff.mp hp).1
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sub_pos.mpr hgp.2)).mpr
    nlinarith [sq_nonneg (g p)]

theorem roughPlusProduct_square_le_normalized (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 + g p)) ^ 2 ≤
      (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)) *
        ((1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2) ^ 3 := by
  have h1 := roughEulerProduct_le_normalized P hP hD hε hεsmall hlarge hcut hg hdim
  have h2 := roughPlusProduct_le_dimensionOne P hP hD hε hεsmall hlarge hcut hg hdim
  have hm := mul_le_mul h1 h2
    (prod_nonneg (fun p hp => by linarith [(hg p (mem_sdiff.mp hp).1).1]))
    (mul_nonneg
      (prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_sdiff.mp hp).1).2.le))
      (sq_nonneg _))
  nlinarith

/-- The actual geometric rough boundary mass on the required normalized
scale, with absolute constant `10` and exactly the original `K`. -/
theorem roughBoundaryMass_le_target (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D) (hK : 0 ≤ K)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    let R := P \ geometricSmallPrimes P D ε
    let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
    roughBoundaryMass upper b (fun p => b p ^ (1 + ε ^ 9)) D R g ≤
      10 * (∏ p ∈ R, (1 - g p)) *
        (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))) := by
  dsimp only
  have hmass := roughBoundaryMass_le_dimensionOne upper P hP hD hε hεsmall hlarge hK hg hdim
  have hnorm := roughPlusProduct_square_le_normalized P hP hD hε hεsmall hlarge
    hcut hg hdim
  have hlog : 0 < Real.log D := Real.log_pos (by linarith)
  have hscalar := boundary_scalar hε (by linarith) hlog hK hlarge
  have hV : 0 ≤ ∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p) :=
    prod_nonneg (fun p hp => sub_nonneg.mpr (hg p (mem_sdiff.mp hp).1).2.le)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnorm (show (0 : ℝ) ≤ 2 by norm_num))
    (show 0 ≤ 3 * ε ^ 7 + 2 * K / (ε ^ 2 * Real.log D) by positivity)
  have hs := mul_le_mul_of_nonneg_left hscalar hV
  dsimp only at hmass
  nlinarith

/-- The uniform threshold precedes the carrier, density and `K`. -/
theorem exists_roughBoundaryMass_le_target :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) →
          ∀ g : ℕ → ℝ, (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P g K →
              ∀ upper : Bool,
                let R := P \ geometricSmallPrimes P D ε
                let b := fun p => geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p)
                roughBoundaryMass upper b (fun p => b p ^ (1 + ε ^ 9)) D R g ≤
                  C * (∏ p ∈ R, (1 - g p)) *
                    (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                      Real.log D ^ (-(1 / 3 : ℝ))) := by
  refine ⟨10, by norm_num, ?_⟩
  intro ε hε hεsmall
  refine ⟨max 2 (Real.exp (1 / ε ^ 2)), le_max_left _ _, ?_⟩
  intro D hD P hP hcut g hg K hK hdim upper
  have hlarge : 1 ≤ ε ^ 2 * Real.log D := by
    have hh := Real.log_le_log (Real.exp_pos (1 / ε ^ 2))
      ((le_max_right _ _).trans hD)
    rw [Real.log_exp] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  exact roughBoundaryMass_le_target upper P hP ((le_max_left _ _).trans hD)
    hε hεsmall hlarge hK hcut hg hdim

#print axioms boundary_scalar
#check roughBoundaryMass_le_target
#print axioms roughBoundaryMass_le_target
#check exists_roughBoundaryMass_le_target
#print axioms exists_roughBoundaryMass_le_target

end BoundaryAnalytic
end MathlibNt.SieveTheory.LiLiuPrereqWF
