

import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanPerronKernel
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedPerronMajorantIntegral
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanRankOneSeparation

/-!
 # Damped-arctangent rectangular hyperbolic primitive means

This leaf states the rectangular smoothed-kernel primitive mean and its two
quantitative endpoints.  It combines the exact `Ioi` damped Perron formula,
the finite two-term rank-one separation, the weighted rectangular primitive
large sieve, and the explicit damped-majorant integral.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A rectangular character sum weighted by the damped Perron step kernel. -/
def rectangularSmoothedKernelCharacterSum
    (a b : ℤ → ℂ) (ε y : ℝ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (dampedArctanPerronKernel ε
          (Real.log (y / ((m * n : ℤ) : ℝ))) : ℂ)


/-- The corresponding sharp hyperbolic-indicator character sum. -/
def rectangularSharpHyperbolicCharacterSum
    (a b : ℤ → ℂ) (Y : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (if m * n ≤ (Y : ℤ) then 1 else 0)


/-- The original rank-one large-sieve right hand side. -/
def rankOneRectangularLSRHS
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ) : ℝ :=
  Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
    ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2) *
  Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2)

/-- Explicit coefficient `L¹` mass of the rectangle. -/
def rectangularCoefficientL1
    (a b : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖) *
  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖)

/-- Explicit weighted mass of the primitive-character family. -/
def weightedPrimitiveFamilyMass (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) * Fintype.card (PrimitiveCharacter q)

/-- Exact damped Perron interchange, before any character mean estimate.
The real cutoff is arbitrary, so the same identity applies to each selector value. -/
theorem rectangularDampedPerron_integrable_formula
    (a b : ℤ → ℂ) (ε y : ℝ) (hε : 0 < ε)
    (Ma Mb : ℤ) (Na Nb : ℕ) :
    ∀ q (χ : PrimitiveCharacter q),
      IntegrableOn (fun t : ℝ => (Real.exp (-ε * t) : ℂ) *
        rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ) (Set.Ioi 0) ∧
      rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ =
        (1 / 2 : ℂ) *
          ((∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
            (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q))) +
        (1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-ε * t) : ℂ) *
            rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ := by
  let sM := Finset.Icc (Ma + 1) (Ma + Na)
  let sN := Finset.Icc (Mb + 1) (Mb + Nb)
  have hscalarInt : ∀ m n : ℤ, Integrable (fun t : ℝ =>
      Real.exp (-ε * t) *
        truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t)
      (volume.restrict (Set.Ioi 0)) := by
    intro m n
    have he : Integrable (fun t : ℝ => Real.exp (-ε * t)) (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
    apply he.mul_bdd
    · exact (continuous_truncatedPerronIntegrand_right
        (Real.log (y / ((m * n : ℤ) : ℝ)))).aestronglyMeasurable
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using abs_truncatedPerronIntegrand_le
        (Real.log (y / ((m * n : ℤ) : ℝ))) t
  have htermInt : ∀ q (χ : PrimitiveCharacter q) (m : ℤ), m ∈ sM →
      ∀ n ∈ sN,
      Integrable (fun t : ℝ =>
        (Real.exp (-ε * t) : ℂ) *
          (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (truncatedPerronIntegrand
              (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
    intro q χ m hm' n hn'
    have hg : Integrable (fun t : ℝ =>
        (Real.exp (-ε * t) : ℂ) *
          (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      have hs := (hscalarInt m n).ofReal (𝕜 := ℂ)
      convert hs using 1
      funext t
      rw [← Complex.ofReal_mul]
      rfl
    convert hg.mul_const (a m * b n * χ.1 ((m * n : ℤ) : ZMod q)) using 1;
      funext t; ring
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ := fun q χ t =>
    (Real.exp (-ε * t) : ℂ) *
      rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ
  have hFint : ∀ q (χ : PrimitiveCharacter q), IntegrableOn (F q χ) (Set.Ioi 0) := by
    intro q χ
    unfold F rectangularKernelCharacterSum
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum sM fun m hm' =>
      integrable_finsetSum sN (htermInt q χ m hm')
  have hkernel : ∀ q (χ : PrimitiveCharacter q),
      rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ =
        (1 / 2 : ℂ) *
          ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
            (∑ n ∈ sN, b n * χ.1 (n : ZMod q))) +
        (1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), F q χ t := by
    intro q χ
    unfold rectangularSmoothedKernelCharacterSum
    have hi : (∫ t in Set.Ioi (0 : ℝ), F q χ t) =
        ∑ m ∈ sM, ∑ n ∈ sN,
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (∫ t in Set.Ioi (0 : ℝ),
              (Real.exp (-ε * t) *
                truncatedPerronIntegrand
                  (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)) := by
      unfold F rectangularKernelCharacterSum
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum sM]
      · apply Finset.sum_congr rfl
        intro m hm'
        rw [integral_finsetSum sN]
        · apply Finset.sum_congr rfl
          intro n hn'
          rw [← MeasureTheory.integral_const_mul]
          congr 1
          funext t
          push_cast
          ring
        · intro n hn'
          exact htermInt q χ m hm' n hn'
      · intro m hm'
        exact integrable_finsetSum sN (htermInt q χ m hm')
    rw [hi]
    have hprod :
        ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
          (∑ n ∈ sN, b n * χ.1 (n : ZMod q))) =
        ∑ m ∈ sM, ∑ n ∈ sN,
          (a m * χ.1 (m : ZMod q)) * (b n * χ.1 (n : ZMod q)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm'
      rw [Finset.mul_sum]
    rw [hprod]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm'
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn'
    rw [dampedArctanPerronKernel_eq_half_add_integral _ _ hε]
    rw [Int.cast_mul, map_mul]
    have hcast :
        ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
          truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
        ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-ε * t) * truncatedPerronIntegrand
            (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ) := by
      simpa only [Complex.ofRealCLM_apply, ← Complex.ofReal_mul] using
        (Complex.ofRealCLM.integral_comp_comm (hscalarInt m n)).symm
    have hformula :
        ((1 / 2 + (1 / Real.pi) *
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
            truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
          (1 / 2 : ℂ) + (1 / Real.pi : ℂ) *
            ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
              truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hformula]
    rw [hcast]
    ring
  exact fun q χ => ⟨hFint q χ, hkernel q χ⟩

/-- Two-sided energy scaling of the original aggregated rank-one large sieve.
No estimate of individual character sums is substituted for this mean. -/
theorem rankOneRectangularWeightedPrimitiveMean_le_scaled_energy
    (a b c d : ℤ → ℂ) (Ma Mb : ℤ) (Na Nb Q : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc : ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖c m‖ ^ 2 ≤
      u ^ 2 * ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2)
    (hd : ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖d n‖ ^ 2 ≤
      v ^ 2 * ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2) :
    rankOneRectangularWeightedPrimitiveMean c d Ma Mb Na Nb S ≤
      (u * v) * rankOneRectangularLSRHS a b Ma Mb Na Nb Q := by
  have hsqrt (K A C r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r)
      (hC : C ≤ r ^ 2 * A) : Real.sqrt (K * C) ≤ r * Real.sqrt (K * A) := by
    calc
      Real.sqrt (K * C) ≤ Real.sqrt (K * (r ^ 2 * A)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hC hK)
      _ = r * Real.sqrt (K * A) := by
        rw [show K * (r ^ 2 * A) = r ^ 2 * (K * A) by ring,
          Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]
  refine (rankOneRectangularWeightedPrimitiveMean_le c d Ma Mb Na Nb Q hQ S hS).trans ?_
  unfold rankOneRectangularLSRHS
  calc
    _ ≤ (u * Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
          ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖ ^ 2)) *
        (v * Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖ ^ 2)) :=
      mul_le_mul (hsqrt _ _ _ _ (by unfold largeSieveBound; positivity) hu hc)
        (hsqrt _ _ _ _ (by unfold largeSieveBound; positivity) hv hd)
        (Real.sqrt_nonneg _) (mul_nonneg hu (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Integrability of the weighted primitive first moment. -/
theorem dampedPerron_weighted_norm_integrable
    (S : Finset ℕ) (w : ℕ → ℝ)
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ) (μ : Measure ℝ)
    (hF : ∀ q χ, Integrable (F q χ) μ) :
    Integrable (fun t => ∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖) μ :=
  integrable_finsetSum S fun q _ =>
    (integrable_finsetSum Finset.univ fun χ _ => (hF q χ).norm).const_mul _

/-- Norm/integral interchange for the actual weighted primitive family. -/
theorem dampedPerron_weighted_norm_integral_le
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q ∈ S, 0 ≤ w q)
    (F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ) (μ : Measure ℝ)
    (hF : ∀ q χ, Integrable (F q χ) μ) :
    (∑ q ∈ S, w q * ∑ χ, ‖∫ t, F q χ t ∂μ‖) ≤
      ∫ t, (∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖) ∂μ := by
  calc
    _ ≤ ∑ q ∈ S, w q * ∑ χ, ∫ t, ‖F q χ t‖ ∂μ :=
      Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun χ _ => norm_integral_le_integral_norm _) (hw q hq)
    _ = _ := by
      rw [integral_finsetSum S]
      · apply Finset.sum_congr rfl
        intro q hq
        rw [integral_const_mul, integral_finsetSum Finset.univ]
        exact fun χ _ => (hF q χ).norm
      · exact fun q _ =>
          (integrable_finsetSum Finset.univ fun χ _ => (hF q χ).norm).const_mul _

/-- Weighted norm subadditivity with the two real prefactors pulled out.
This is used only after the exact Perron identity, not to replace a rank-one mean. -/
theorem dampedPerron_weighted_norm_add_le
    (S : Finset ℕ) (w : ℕ → ℝ) (hw : ∀ q ∈ S, 0 ≤ w q)
    (D I : (q : ℕ) → PrimitiveCharacter q → ℂ)
    (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (∑ q ∈ S, w q * ∑ χ, ‖(p : ℂ) * D q χ + (r : ℂ) * I q χ‖) ≤
      p * (∑ q ∈ S, w q * ∑ χ, ‖D q χ‖) +
        r * (∑ q ∈ S, w q * ∑ χ, ‖I q χ‖) := by
  calc
    _ ≤ ∑ q ∈ S, w q * ∑ χ, (p * ‖D q χ‖ + r * ‖I q χ‖) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hw q hq)
      apply Finset.sum_le_sum
      intro χ hχ
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hp, abs_of_nonneg hr] using
        norm_add_le ((p : ℂ) * D q χ) ((r : ℂ) * I q χ)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]

/-- Integrate a two-frequency damped majorant without any sign assumption on
its integrable minorant. Multiplicity of equal lanes is absorbed into `R`. -/
theorem dampedPerron_integral_le_two_majorants
    {ε L₁ L₂ R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hR : 0 ≤ R)
    {G : ℝ → ℝ} (hGint : IntegrableOn G (Set.Ioi 0))
    (hG : ∀ t ∈ Set.Ioi (0 : ℝ), G t ≤
      (dampedPerronMajorantIntegrand ε L₁ t +
        dampedPerronMajorantIntegrand ε L₂ t) * R) :
    (∫ t in Set.Ioi (0 : ℝ), G t) ≤
      ((L₁ + Real.log (1 / ε) + 1) + (L₂ + Real.log (1 / ε) + 1)) * R := by
  have h₁ := dampedPerronMajorant_integrableOn_Ioi hε hL₁
  have h₂ := dampedPerronMajorant_integrableOn_Ioi hε hL₂
  calc
    (∫ t in Set.Ioi (0 : ℝ), G t) ≤
        ∫ t in Set.Ioi (0 : ℝ),
          (dampedPerronMajorantIntegrand ε L₁ t +
            dampedPerronMajorantIntegrand ε L₂ t) * R :=
      setIntegral_mono_on hGint ((h₁.add h₂).mul_const R) measurableSet_Ioi hG
    _ = ((∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₁ t) +
          (∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₂ t)) * R := by
      rw [integral_mul_const, integral_add h₁ h₂]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (dampedPerronMajorant_integral_Ioi_le hε hε1 hL₁)
        (dampedPerronMajorant_integral_Ioi_le hε hε1 hL₂)) hR


/-- The half-step smoothing error for one rectangular character sum.
The cutoff remains an argument, so it may later depend on the character. -/
theorem rectangularSharpHyperbolicCharacterSum_norm_le_smoothed
    (a b : ℤ → ℂ) (Y M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (hM : 1 ≤ M) (hYM : Y ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (q : ℕ) (χ : PrimitiveCharacter q) :
    ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ≤
      ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
        (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y)
        Ma Mb Na Nb q χ‖ +
      (8 / (Real.pi * (M : ℝ))) * rectangularCoefficientL1 a b Ma Mb Na Nb := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let E : ℝ := 8 / (Real.pi * (M : ℝ))
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have herror : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
        |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| ≤ E := by
    intro m hm n hn
    have hp := hmnPos m hm n hn
    let k : ℕ := (m * n).toNat
    have hkZ : (k : ℤ) = m * n := by
      exact Int.toNat_of_nonneg (le_of_lt hp)
    have hk0 : k ≠ 0 := by
      intro hk
      have : (m * n : ℤ) = 0 := by simpa [hk] using hkZ.symm
      omega
    have hkcut : k ≤ Y ↔ m * n ≤ (Y : ℤ) := by
      constructor
      · intro h
        rw [← hkZ]
        exact_mod_cast h
      · intro h
        rw [← hkZ] at h
        exact_mod_cast h
    have hh := abs_halfStepIndicator_sub_dampedArctanPerronKernel_le
      (ε := ε) (n := k) (Y := Y) (M := M) hε hk0 hM hYM
    have hconst : 8 * ε * (M : ℝ) / Real.pi = E := by
      dsimp [ε, E]
      field_simp [Real.pi_ne_zero, hMr.ne']
    have hkR : (k : ℝ) = ((m * n : ℤ) : ℝ) := by exact_mod_cast hkZ
    calc
      |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
          dampedArctanPerronKernel ε
            (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
              ((m * n : ℤ) : ℝ)))| ≤ 8 * ε * (M : ℝ) / Real.pi := by
            rw [hkR] at hh
            simpa only [hkcut] using hh
      _ = E := hconst
  have hχ : ∀ q (χ : PrimitiveCharacter q) (z : ZMod q), ‖χ.1 z‖ ≤ 1 := by
    intro q χ z
    exact DirichletCharacter.norm_le_one χ.1 z
  have hpoint : ∀ q (χ : PrimitiveCharacter q)
      (m : ℤ) (_ : m ∈ Finset.Icc (Ma + 1) (Ma + Na))
      (n : ℤ) (_ : n ∈ Finset.Icc (Mb + 1) (Mb + Nb)),
      ‖a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (if m * n ≤ (Y : ℤ) then 1 else 0) -
        a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (dampedArctanPerronKernel ε
            (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
              ((m * n : ℤ) : ℝ))) : ℂ)‖ ≤
        E * ‖a m‖ * ‖b n‖ := by
    intro q χ m hm n hn
    rw [← mul_sub]
    simp only [norm_mul]
    have hc := hχ q χ ((m * n : ℤ) : ZMod q)
    have he := herror m hm n hn
    have hE : 0 ≤ E := by
      dsimp [E]
      positivity
    have hreal :
        ‖(if m * n ≤ (Y : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                ((m * n : ℤ) : ℝ))) : ℂ)‖ =
          |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| := by
      by_cases hcut : m * n ≤ (Y : ℤ)
      · simp only [if_pos hcut, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      · simp only [if_neg hcut, ← Complex.ofReal_zero, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
    calc
      ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          ‖(if m * n ≤ (Y : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                ((m * n : ℤ) : ℝ))) : ℂ)‖ =
        ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          |(if m * n ≤ (Y : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                ((m * n : ℤ) : ℝ)))| := by rw [hreal]
      _ ≤
          ‖a m‖ * ‖b n‖ * 1 * E := by
            gcongr
      _ = E * ‖a m‖ * ‖b n‖ := by ring
  let A := rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ
  let B := rectangularSmoothedKernelCharacterSum a b ε
    (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y) Ma Mb Na Nb q χ
  change ‖A‖ ≤ ‖B‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb
  calc
    ‖A‖ = ‖B + (A - B)‖ := by congr 1; ring
    _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
    _ ≤ ‖B‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
      apply add_le_add le_rfl
      dsimp [A, B, rectangularSharpHyperbolicCharacterSum,
        rectangularSmoothedKernelCharacterSum]
      simp only [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
            ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), E * ‖a m‖ * ‖b n‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hpoint q χ m hm n hn))
        _ = E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
          simp only [rectangularCoefficientL1, Finset.mul_sum, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]


end

end AnalyticNumberTheory.LargeSieve
