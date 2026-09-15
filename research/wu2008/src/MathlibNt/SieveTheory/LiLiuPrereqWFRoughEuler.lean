import MathlibNt.SieveTheory.LiLiuPrereqWFSignedDensity

/-!
# Full-carrier normalization of the actual small-weight replacement

The rough Euler majorant is paid using the same dimension-one constant.
The absolute constant precedes epsilon, and the threshold precedes all
prime carriers, densities, depths, and signs. This does not estimate the
remaining signed rough density by the linear-sieve functions.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open scoped Classical

private theorem plusProduct_le_euler_mul_square {g : ℕ → ℝ}
    (R : Finset ℕ) {A : ℝ}
    (hg : ∀ p ∈ R, 0 ≤ g p ∧ g p < 1)
    (hA : (∏ p ∈ R, (1 - g p))⁻¹ ≤ A) :
    (∏ p ∈ R, (1 + g p)) ≤ (∏ p ∈ R, (1 - g p)) * A ^ 2 := by
  let V := ∏ p ∈ R, (1 - g p)
  have hV : 0 < V := Finset.prod_pos fun p hp => sub_pos.mpr (hg p hp).2
  have hprod : (∏ p ∈ R, (1 + g p)) * V ≤ 1 := by
    rw [show V = ∏ p ∈ R, (1 - g p) from rfl, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_one
      (fun p hp => mul_nonneg (by linarith [(hg p hp).1])
        (sub_nonneg.mpr (hg p hp).2.le))
      (fun p _ => by nlinarith [sq_nonneg (g p)])
  have hAV : 1 ≤ A * V := (inv_le_iff_one_le_mul₀ hV).mp hA
  have hpow : 1 ≤ (A * V) ^ 2 := one_le_pow₀ hAV
  apply (mul_le_mul_iff_left₀ hV).mp
  nlinarith [show (A * V) ^ 2 = V * (V * A ^ 2) by ring]

/-- The rough product is normalized by its own Euler factor, with an
explicit dimension-one loss and no threshold depending on `K`. -/
theorem roughEulerProduct_le_normalized (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε K : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlarge : 1 ≤ ε ^ 2 * Real.log D)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    {g : ℕ → ℝ} (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1)
    (hdim : DimensionOneProductBound P g K) :
    (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 + g p)) ≤
      (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)) *
        ((1 + K / (ε ^ 2 * Real.log D)) / ε ^ 2) ^ 2 := by
  let u := D ^ (ε ^ 2)
  have hD0 : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
  have hu0 : 0 < u := Real.rpow_pos_of_pos hD0 _
  have hlogu : Real.log u = ε ^ 2 * Real.log D := Real.log_rpow hD0 _
  have hu2 : 2 ≤ u := by
    have hexp : Real.exp 1 ≤ u := by
      apply (Real.log_le_log_iff (Real.exp_pos _) hu0).mp
      simpa only [Real.log_exp, hlogu] using hlarge
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    exact htwo.trans hexp
  have hε2 : ε ^ 2 < 1 := by nlinarith
  have huD : u < D := by
    calc
      u < D ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) hε2
      _ = D := Real.rpow_one _
  have hsqrt : Real.sqrt D ≤ D := by
    nlinarith [Real.sq_sqrt hD0.le, Real.sqrt_nonneg D]
  have heq : P \ geometricSmallPrimes P D ε =
      P.filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < D) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpP, hpB⟩ := Finset.mem_sdiff.mp hp
      have hlow : u ≤ (p : ℝ) := by
        by_contra hn
        exact hpB (Finset.mem_filter.mpr ⟨hpP, hP p hpP, lt_of_not_ge hn⟩)
      exact Finset.mem_filter.mpr
        ⟨hpP, hP p hpP, hlow, (hcut p hp).trans_le hsqrt⟩
    · intro hp
      obtain ⟨hpP, _, hlow, _⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_sdiff.mpr ⟨hpP, fun hpB =>
        (not_lt_of_ge hlow) (Finset.mem_filter.mp hpB).2.2⟩
  apply plusProduct_le_euler_mul_square _
    (fun p hp => hg p (Finset.mem_sdiff.mp hp).1)
  rw [heq, ← Finset.prod_inv_distrib]
  have h := hdim u D hu2 huD
  rw [hlogu] at h
  convert h using 1
  field_simp

private theorem eulerProduct_small_mul_rough (P : Finset ℕ) (D ε : ℝ)
    (g : ℕ → ℝ) :
    (∏ p ∈ geometricSmallPrimes P D ε, (1 - g p)) *
      (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - g p)) =
        ∏ p ∈ P, (1 - g p) := by
  have hB : geometricSmallPrimes P D ε ⊆ P := Finset.filter_subset _ _
  rw [mul_comm, ← Finset.prod_union Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset hB]

/-- Explicit full-`V(P)` bound for the replacement in the actual signed
family. In particular the enlargement of the threshold is independent of
the original dimension-one constant `K`. -/
theorem exists_signedFamilyDensity_replacement_normalized :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
          (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) →
          ∀ (ω : ArithmeticFunction ℝ), ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ upper : Bool,
                let B := geometricSmallPrimes P D ε
                let label := geometricSieveLabel D ε
                let b := fun p => geometricLower D ε (ε ^ 9) (label p)
                let c := fun p => b p ^ (1 + ε ^ 9)
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let E := C * (Real.exp (-(1 / ε)) +
                  Real.exp (Real.sqrt K - 1 / ε) *
                    (ε * Real.log D) ^ (-(1 / 3 : ℝ)))
                let δ := signedFamilyDensity upper P D ε label (primeDensity ω) -
                  smallWeightDensity upper P D ε (primeDensity ω) *
                    roughSignedDensity upper b c D (P \ B) (primeDensity ω)
                1 ≤ ε ^ 2 * Real.log D ∧
                  0 ≤ (if upper then 1 else -1) * δ ∧
                    |δ| ≤ 2 * V * E / ε ^ 4 *
                      (1 + K / (ε ^ 2 * Real.log D)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_signedFamilyDensity_replacement_bound
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₁, hD₁, hbound⟩ := hbound ε hε hεsmall
  refine ⟨max D₁ (Real.exp (1 / ε ^ 2)), hD₁.trans (le_max_left _ _), ?_⟩
  intro D hD P hP hcut ω hω hg K hK hdim upper
  have hDold : D₁ ≤ D := (le_max_left _ _).trans hD
  have hD2 : 2 ≤ D := hD₁.trans hDold
  have hlarge : 1 ≤ ε ^ 2 * Real.log D := by
    have hh := Real.log_le_log (Real.exp_pos (1 / ε ^ 2))
      ((le_max_right _ _).trans hD)
    rw [Real.log_exp] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hε)).mp hh |>.trans_eq (mul_comm _ _)
  have h := hbound D hDold P hP hcut ω hω hg K hK hdim upper
  have he := roughEulerProduct_le_normalized P hP hD2 hε hεsmall hlarge
    hcut (g := primeDensity ω) hg hdim
  dsimp only at h ⊢
  refine ⟨hlarge, h.1, h.2.trans ?_⟩
  simp only [primeDensity_apply] at he
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2 * (∏ p ∈ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ))) *
      (C * (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
        (ε * Real.log D) ^ (-(1 / 3 : ℝ)))) from by
      have hV : 0 < ∏ p ∈ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ)) :=
        Finset.prod_pos (fun p hp =>
        sub_pos.mpr (hg p (Finset.mem_filter.mp hp).1).2)
      have hlogD : 0 < Real.log D := Real.log_pos (by linarith)
      positivity)
  have hid := eulerProduct_small_mul_rough P D ε (primeDensity ω)
  simp only [primeDensity_apply] at hid
  convert hmul using 1
  rw [show 2 * (∏ p ∈ P, (1 - ω p / (p : ℝ))) *
      (C * (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
        (ε * Real.log D) ^ (-(1 / 3 : ℝ)))) / ε ^ 4 *
      (1 + K / (ε ^ 2 * Real.log D)) ^ 2 =
    2 * ((∏ p ∈ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ))) *
      (∏ p ∈ P \ geometricSmallPrimes P D ε, (1 - ω p / (p : ℝ)))) *
      (C * (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
        (ε * Real.log D) ^ (-(1 / 3 : ℝ)))) / ε ^ 4 *
      (1 + K / (ε ^ 2 * Real.log D)) ^ 2 by rw [hid]]
  ring

private theorem exp_neg_inv_div_fourth_le {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-(1 / ε)) / ε ^ 4 ≤ 120 * ε := by
  have hpow := Real.pow_div_factorial_le_exp (1 / ε) (by positivity) 5
  norm_num only [Nat.factorial] at hpow
  have hm := mul_le_mul_of_nonneg_left hpow
    (by positivity : (0 : ℝ) ≤ 120 * ε ^ 5)
  have hid : 120 * ε ^ 5 * ((1 / ε) ^ 5 / (120 : ℝ)) = 1 := by
    field_simp
  rw [hid] at hm
  rw [div_le_iff₀ (pow_pos hε 4), Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  convert hm using 1
  ring

/-- Scalar absorption keeps the leading epsilon term independent of `K`.
The logarithmic term, rather than the threshold, pays every rough factor. -/
theorem roughEuler_replacement_scalar {ε L K : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 < L) (hK : 0 ≤ K)
    (ht : 1 ≤ ε ^ 2 * L) :
    (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
      (ε * L) ^ (-(1 / 3 : ℝ))) / ε ^ 4 *
        (1 + K / (ε ^ 2 * L)) ^ 2 ≤
      120 * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * L ^ (-(1 / 3 : ℝ))) := by
  let t := ε ^ 2 * L
  let x := t ^ (-(1 / 3 : ℝ))
  let a := Real.exp (Real.sqrt K)
  let b := Real.exp (2 * K)
  let H := Real.exp (6 * K + 2)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hx0 : 0 ≤ x := Real.rpow_nonneg ht0.le _
  have hx1 : x ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) ht
        (by norm_num : -(1 / 3 : ℝ) ≤ 0)
  have htinv : t⁻¹ ≤ x := by
    calc
      t⁻¹ = t ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ x := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have htinvsq : (t⁻¹) ^ 2 ≤ x := by
    have hi : t⁻¹ ≤ 1 := by
      simpa using (inv_le_one₀ ht0).mpr ht
    nlinarith [inv_nonneg.mpr ht0.le]
  have hpoly : 2 * K + K ^ 2 ≤ b := by
    have he : 1 + K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
    have hs := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + K) he 2
    have hb : Real.exp K ^ 2 = b := by
      dsimp [b]
      rw [show 2 * K = K + K by ring, Real.exp_add]
      ring
    rw [hb] at hs
    nlinarith
  have hfactor : (1 + K / t) ^ 2 ≤ 1 + b * x := by
    have hi := mul_le_mul_of_nonneg_left htinv (by positivity : 0 ≤ 2 * K)
    have hisq := mul_le_mul_of_nonneg_left htinvsq (sq_nonneg K)
    have hp := mul_le_mul_of_nonneg_right hpoly hx0
    rw [div_eq_mul_inv]
    nlinarith
  have hy : (ε * L) ^ (-(1 / 3 : ℝ)) ≤ x := by
    apply Real.rpow_le_rpow_of_nonpos ht0
    · dsimp [t]
      nlinarith [mul_nonneg (sq_nonneg ε) hL.le]
    · norm_num
  have hsqrt : Real.sqrt K ≤ K + 1 := by
    nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K, sq_nonneg (K - 1)]
  have ha : a ≤ H := Real.exp_le_exp.mpr (by linarith)
  have hb : b ≤ H := Real.exp_le_exp.mpr (by linarith)
  have hab : a * b ≤ H := by
    dsimp [a, b, H]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hH0 : 0 ≤ H := (Real.exp_pos _).le
  have hcombine : (1 + a * x) * (1 + b * x) ≤ 1 + 3 * H * x := by
    have hxx : x ^ 2 ≤ x := by nlinarith
    have hxmul := mul_le_mul_of_nonneg_left hxx (mul_nonneg ha0 hb0)
    have hax := mul_le_mul_of_nonneg_right ha hx0
    have hbx := mul_le_mul_of_nonneg_right hb hx0
    have habx := mul_le_mul_of_nonneg_right hab hx0
    nlinarith
  have hbudget : x / ε ^ 4 ≤ (ε ^ 8)⁻¹ * L ^ (-(1 / 3 : ℝ)) := by
    have hep : ε ^ 12 ≤ ε ^ 2 := by
      have hh := pow_le_pow_left₀ hε.le hε1 10
      norm_num at hh
      nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg ε),
        show ε ^ 12 = ε ^ 2 * ε ^ 10 by ring]
    have hx : x ≤ (ε ^ 12 * L) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity)
        (mul_le_mul_of_nonneg_right hep hL.le) (by norm_num)
    have heq : (ε ^ 12 * L) ^ (-(1 / 3 : ℝ)) =
        (ε ^ 4)⁻¹ * L ^ (-(1 / 3 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hL.le,
        ← Real.rpow_natCast_mul hε.le]
      norm_num
    rw [heq] at hx
    have hh := div_le_div_of_nonneg_right hx (pow_nonneg hε.le 4)
    calc
      x / ε ^ 4 ≤ (ε ^ 4)⁻¹ * L ^ (-(1 / 3 : ℝ)) / ε ^ 4 := hh
      _ = (ε ^ 8)⁻¹ * L ^ (-(1 / 3 : ℝ)) := by ring
  have hneg : Real.exp (-(1 / ε)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hsource :
      Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
        (ε * L) ^ (-(1 / 3 : ℝ)) ≤
          Real.exp (-(1 / ε)) * (1 + a * x) := by
    have hh := mul_le_mul_of_nonneg_left hy
      (Real.exp_pos (Real.sqrt K - 1 / ε)).le
    rw [sub_eq_add_neg, Real.exp_add] at hh ⊢
    dsimp [a]
    nlinarith
  have htotal :
      (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
        (ε * L) ^ (-(1 / 3 : ℝ))) / ε ^ 4 *
          (1 + K / t) ^ 2 ≤
        Real.exp (-(1 / ε)) / ε ^ 4 * (1 + 3 * H * x) := by
    calc
      _ ≤ (Real.exp (-(1 / ε)) * (1 + a * x) / ε ^ 4) * (1 + b * x) :=
        mul_le_mul (div_le_div_of_nonneg_right hsource (pow_nonneg hε.le 4))
          hfactor (sq_nonneg _) (by positivity)
      _ = Real.exp (-(1 / ε)) / ε ^ 4 * ((1 + a * x) * (1 + b * x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcombine (by positivity)
  have hdec := exp_neg_inv_div_fourth_le hε
  have htail :
      Real.exp (-(1 / ε)) / ε ^ 4 * (3 * H * x) ≤
        3 * H * ((ε ^ 8)⁻¹ * L ^ (-(1 / 3 : ℝ))) := by
    calc
      _ = 3 * H * (Real.exp (-(1 / ε)) * (x / ε ^ 4)) := by ring
      _ ≤ 3 * H * (x / ε ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hneg (div_nonneg hx0 (pow_nonneg hε.le 4))
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)
  have htail0 : 0 ≤ (ε ^ 8)⁻¹ * H * L ^ (-(1 / 3 : ℝ)) := by positivity
  change _ ≤ 120 * (ε + (ε ^ 8)⁻¹ * H * L ^ (-(1 / 3 : ℝ)))
  change (Real.exp (-(1 / ε)) + Real.exp (Real.sqrt K - 1 / ε) *
    (ε * L) ^ (-(1 / 3 : ℝ))) / ε ^ 4 * (1 + K / t) ^ 2 ≤ _
  nlinarith

/-- The complete small-weight replacement cost at the target scale, for
the same signed family and the original `K`. The remaining rough-density
comparison with `F` and `f` is not asserted. -/
theorem exists_signedFamilyDensity_replacement_target :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
          (∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) →
          ∀ (ω : ArithmeticFunction ℝ), ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ upper : Bool,
                let B := geometricSmallPrimes P D ε
                let label := geometricSieveLabel D ε
                let b := fun p => geometricLower D ε (ε ^ 9) (label p)
                let c := fun p => b p ^ (1 + ε ^ 9)
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let δ := signedFamilyDensity upper P D ε label (primeDensity ω) -
                  smallWeightDensity upper P D ε (primeDensity ω) *
                    roughSignedDensity upper b c D (P \ B) (primeDensity ω)
                0 ≤ (if upper then 1 else -1) * δ ∧
                  |δ| ≤ V * C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                    (Real.log D) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_signedFamilyDensity_replacement_normalized
  refine ⟨240 * C, by positivity, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₀, hD₀, hbound⟩ := hbound ε hε hεsmall
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD P hP hcut ω hω hg K hK hdim upper
  have hD2 : 2 ≤ D := hD₀.trans hD
  have h := hbound D hD P hP hcut ω hω hg K hK hdim upper
  dsimp only at h ⊢
  refine ⟨h.2.1, h.2.2.trans ?_⟩
  have hs := roughEuler_replacement_scalar hε (by linarith : ε ≤ 1)
    (Real.log_pos (by linarith : 1 < D)) hK h.1
  have hV : 0 < ∏ p ∈ P, (1 - ω p / (p : ℝ)) :=
    Finset.prod_pos (fun p hp => sub_pos.mpr (hg p hp).2)
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2 * (∏ p ∈ P, (1 - ω p / (p : ℝ))) * C by positivity)
  convert hm using 1 <;> ring

#check roughEulerProduct_le_normalized
#print axioms roughEulerProduct_le_normalized
#check exists_signedFamilyDensity_replacement_normalized
#print axioms exists_signedFamilyDensity_replacement_normalized
#check roughEuler_replacement_scalar
#print axioms roughEuler_replacement_scalar
#check exists_signedFamilyDensity_replacement_target
#print axioms exists_signedFamilyDensity_replacement_target

end MathlibNt.SieveTheory.LiLiuPrereqWF
