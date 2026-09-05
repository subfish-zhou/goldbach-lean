

import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanPerronKernel
import MathlibNt.AnalyticNumberTheory.LargeSieve.RankOneRectangularPrimitiveL1
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

/-- Weighted primitive first moment of the smoothed rectangular kernel. -/
def rectangularSmoothedKernelWeightedPrimitiveMean
    (a b : ℤ → ℂ) (ε y : ℝ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ‖

/-- The corresponding sharp hyperbolic-indicator character sum. -/
def rectangularSharpHyperbolicCharacterSum
    (a b : ℤ → ℂ) (Y : ℕ) (Ma Mb : ℤ) (Na Nb q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
    ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
      a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
        (if m * n ≤ (Y : ℤ) then 1 else 0)

/-- Weighted primitive first moment with the sharp hyperbolic indicator. -/
def rectangularSharpHyperbolicWeightedPrimitiveMean
    (a b : ℤ → ℂ) (Y : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ)
    (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q,
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖

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

/-- For `ε=M⁻²`, positive rectangular supports bounded by `M`, and a half-step
parameter in `[1/2,M+1/2]`, the smoothed mean is bounded by the original
rank-one LS right hand side.  The constants `2 log M`, `log M` from the two
sine lanes contribute respectively `4 log M+1`, `3 log M+1` under
`dampedPerronMajorant_integral_Ioi_le`, hence `7 log M+2` in total. -/
theorem rectangularSmoothedKernelWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (y : ℝ) (Ma Mb : ℤ) (Na Nb Q M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M) (hy0 : 1 / 2 ≤ y) (hyM : y ≤ (M : ℝ) + 1 / 2)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    rectangularSmoothedKernelWeightedPrimitiveMean a b
        (1 / (M : ℝ) ^ 2) y Ma Mb Na Nb S ≤
      (1 / 2 + (7 * Real.log (M : ℝ) + 2) / Real.pi) *
        rankOneRectangularLSRHS a b Ma Mb Na Nb Q := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let R : ℝ := rankOneRectangularLSRHS a b Ma Mb Na Nb Q
  let sM : Finset ℤ := Finset.Icc (Ma + 1) (Ma + Na)
  let sN : Finset ℤ := Finset.Icc (Mb + 1) (Mb + Nb)
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one (sq_pos_of_pos hMr)]
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hy : 0 < y := lt_of_lt_of_le (by norm_num) hy0
  have hm : ∀ m ∈ sM, 0 < m := by
    intro m hm'
    exact lt_of_lt_of_le Int.zero_lt_one (hm1 m hm')
  have hn : ∀ n ∈ sN, 0 < n := by
    intro n hn'
    exact lt_of_lt_of_le Int.zero_lt_one (hn1 n hn')
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hR : 0 ≤ R := by
    dsimp [R, rankOneRectangularLSRHS]
    positivity
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
    convert hg.mul_const (a m * b n * χ.1 ((m * n : ℤ) : ZMod q)) using 1 <;>
      funext t <;> ring
  have hsumInt : ∀ {ι : Type} (s : Finset ι) (g : ι → ℝ → ℂ)
      (μ : Measure ℝ), (∀ i ∈ s, Integrable (g i) μ) →
        Integrable (fun t => ∑ i ∈ s, g i t) μ := by
    intro ι s g μ hg
    induction s using Finset.induction_on with
    | empty => simpa using (integrable_zero ℝ μ)
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hg i (Finset.mem_insert_self i s)).add
          (ih (fun j hj => hg j (Finset.mem_insert_of_mem hj)))
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ := fun q χ t =>
    (Real.exp (-ε * t) : ℂ) *
      rectangularKernelCharacterSum a b y t Ma Mb Na Nb q χ
  have hFint : ∀ q (χ : PrimitiveCharacter q), IntegrableOn (F q χ) (Set.Ioi 0) := by
    intro q χ
    unfold F rectangularKernelCharacterSum
    simp_rw [Finset.mul_sum]
    exact hsumInt sM (fun m t => ∑ n ∈ sN,
      (Real.exp (-ε * t) : ℂ) *
        (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)))
      (volume.restrict (Set.Ioi 0)) (fun m hm' =>
        hsumInt sN (fun n t =>
          (Real.exp (-ε * t) : ℂ) *
            (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
              (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)))
          (volume.restrict (Set.Ioi 0)) (htermInt q χ m hm'))
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
      rw [integral_finset_sum sM]
      · apply Finset.sum_congr rfl
        intro m hm'
        rw [integral_finset_sum sN]
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
        exact hsumInt sN (fun n t =>
          (Real.exp (-ε * t) : ℂ) *
            (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
              (truncatedPerronIntegrand (Real.log (y / ((m * n : ℤ) : ℝ))) t : ℂ)))
          (volume.restrict (Set.Ioi 0)) (htermInt q χ m hm')
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
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
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
  let w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let D : (q : ℕ) → PrimitiveCharacter q → ℂ := fun q χ =>
    ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
      (∑ n ∈ sN, b n * χ.1 (n : ZMod q)))
  let G : ℝ → ℝ := fun t =>
    ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖F q χ t‖
  have hGint : IntegrableOn G (Set.Ioi 0) := by
    dsimp only [G]
    apply integrable_finset_sum
    intro q hq
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro χ hχ
    exact (hFint q χ).norm
  have hDmean :
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖D q χ‖) =
        rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S := by
    unfold rankOneRectangularWeightedPrimitiveMean
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    apply Finset.sum_congr rfl
    intro χ hχ
    simp only [D, sM, sN, norm_mul]
  have hImean :
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
          ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) ≤
        ∫ t in Set.Ioi (0 : ℝ), G t := by
    calc
      (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
          ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) ≤
          ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
            ∫ t in Set.Ioi (0 : ℝ), ‖F q χ t‖ := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro χ hχ
          exact MeasureTheory.norm_integral_le_integral_norm _
        · dsimp [w]
          positivity
      _ = ∫ t in Set.Ioi (0 : ℝ), G t := by
        dsimp only [G]
        rw [integral_finset_sum S]
        · apply Finset.sum_congr rfl
          intro q hq
          rw [MeasureTheory.integral_const_mul]
          rw [integral_finset_sum Finset.univ]
          intro χ hχ
          exact (hFint q χ).norm
        · intro q hq
          exact (integrable_finset_sum Finset.univ fun χ hχ => (hFint q χ).norm).const_mul _
  have hbase :
      rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S ≤ R := by
    simpa only [R, rankOneRectangularLSRHS] using
      rankOneRectangularWeightedPrimitiveMean_le a b Ma Mb Na Nb Q hQ S hS
  let L₁ : ℝ := 2 * Real.log (M : ℝ)
  let L₂ : ℝ := Real.log (M : ℝ)
  have hL₁ : 0 ≤ L₁ := mul_nonneg (by norm_num) hlogM
  have hL₂ : 0 ≤ L₂ := hlogM
  have hlane₁ : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (leftSinTwist a y t) (rightCosTwist b t) Ma Mb Na Nb S ≤
        min 1 (L₁ * t) * R := by
    intro t ht
    have hc : 0 ≤ min 1 (L₁ * t) :=
      le_min (by norm_num) (mul_nonneg hL₁ ht.le)
    have heA := sum_norm_sq_leftSinTwist_Icc_le_of_halfstep
      a y t Ma Na M hM hy0 hyM hm1 hmM
    have heB := sum_norm_sq_rightCosTwist_le b t sN
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (leftSinTwist a y t) (rightCosTwist b t) Ma Mb Na Nb Q hQ S hS
    calc
      rankOneRectangularWeightedPrimitiveMean
          (leftSinTwist a y t) (rightCosTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖leftSinTwist a y t m‖ ^ 2) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖rightCosTwist b t n‖ ^ 2) := by simpa [sM, sN] using hls
      _ ≤ Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ((min 1 (L₁ * t)) ^ 2 * ∑ m ∈ sM, ‖a m‖ ^ 2)) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖b n‖ ^ 2) := by
        gcongr
        · unfold largeSieveBound
          positivity
        · simpa [L₁, abs_of_pos ht] using heA
        · unfold largeSieveBound
          positivity
      _ = min 1 (L₁ * t) * R := by
        have hA : 0 ≤ largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖a m‖ ^ 2 := by
          unfold largeSieveBound
          positivity
        rw [show largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
              ((min 1 (L₁ * t)) ^ 2 * ∑ m ∈ sM, ‖a m‖ ^ 2) =
            (min 1 (L₁ * t)) ^ 2 *
              (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
                ∑ m ∈ sM, ‖a m‖ ^ 2) by ring,
          Real.sqrt_mul (sq_nonneg (min 1 (L₁ * t))), Real.sqrt_sq hc]
        dsimp only [R, rankOneRectangularLSRHS]
        ring
  have hlane₂ : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (leftCosTwist a y t) (rightSinTwist b t) Ma Mb Na Nb S ≤
        min 1 (L₂ * t) * R := by
    intro t ht
    have hc : 0 ≤ min 1 (L₂ * t) :=
      le_min (by norm_num) (mul_nonneg hL₂ ht.le)
    have heA := sum_norm_sq_leftCosTwist_le a y t sM
    have heB := sum_norm_sq_rightSinTwist_Icc_le b t Mb Nb M (by omega) hn1 hnM
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (leftCosTwist a y t) (rightSinTwist b t) Ma Mb Na Nb Q hQ S hS
    calc
      rankOneRectangularWeightedPrimitiveMean
          (leftCosTwist a y t) (rightSinTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖leftCosTwist a y t m‖ ^ 2) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖rightSinTwist b t n‖ ^ 2) := by simpa [sM, sN] using hls
      _ ≤ Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖a m‖ ^ 2) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ((min 1 (L₂ * t)) ^ 2 * ∑ n ∈ sN, ‖b n‖ ^ 2)) := by
        gcongr
        · unfold largeSieveBound
          positivity
        · unfold largeSieveBound
          positivity
        · simpa [L₂, abs_of_pos ht] using heB
      _ = min 1 (L₂ * t) * R := by
        have hB : 0 ≤ largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖b n‖ ^ 2 := by
          unfold largeSieveBound
          positivity
        rw [show largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
              ((min 1 (L₂ * t)) ^ 2 * ∑ n ∈ sN, ‖b n‖ ^ 2) =
            (min 1 (L₂ * t)) ^ 2 *
              (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
                ∑ n ∈ sN, ‖b n‖ ^ 2) by ring,
          Real.sqrt_mul (sq_nonneg (min 1 (L₂ * t))), Real.sqrt_sq hc]
        dsimp only [R, rankOneRectangularLSRHS]
        ring
  have hG : ∀ t ∈ Set.Ioi (0 : ℝ),
      G t ≤ (dampedPerronMajorantIntegrand ε L₁ t +
        dampedPerronMajorantIntegrand ε L₂ t) * R := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hexp : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
    have hinv : 0 ≤ t⁻¹ :=
      inv_nonneg.mpr (show 0 ≤ t from (show 0 < t from ht).le)
    have hpoint : ∀ q (χ : PrimitiveCharacter q),
        ‖F q χ t‖ ≤ (Real.exp (-ε * t) / t) *
          (‖(∑ m ∈ sM, leftSinTwist a y t m * χ.1 (m : ZMod q)) *
              (∑ n ∈ sN, rightCosTwist b t n * χ.1 (n : ZMod q))‖ +
           ‖(∑ m ∈ sM, leftCosTwist a y t m * χ.1 (m : ZMod q)) *
              (∑ n ∈ sN, rightSinTwist b t n * χ.1 (n : ZMod q))‖) := by
      intro q χ
      dsimp only [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), rectangularKernelCharacterSum_eq_rankOne
          a b hy ht0 Ma Mb Na Nb q χ hm hn]
      rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, one_div]
      calc
        Real.exp (-ε * t) *
            (t⁻¹ * ‖(∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                    rightCosTwist b t n * χ.1 (n : ZMod q)) -
              (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                    rightSinTwist b t n * χ.1 (n : ZMod q))‖) ≤
          Real.exp (-ε * t) *
            (t⁻¹ * (‖(∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                    rightCosTwist b t n * χ.1 (n : ZMod q))‖ +
              ‖(∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                  (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                    rightSinTwist b t n * χ.1 (n : ZMod q))‖)) := by
            apply mul_le_mul_of_nonneg_left
            · apply mul_le_mul_of_nonneg_left
              · exact norm_sub_le _ _
              · exact hinv
            · exact hexp
        _ = _ := by
          dsimp only [sM, sN]
          rw [div_eq_mul_inv]
          ring
    calc
      G t ≤ (Real.exp (-ε * t) / t) *
          (rankOneRectangularWeightedPrimitiveMean
              (leftSinTwist a y t) (rightCosTwist b t) Ma Mb Na Nb S +
           rankOneRectangularWeightedPrimitiveMean
              (leftCosTwist a y t) (rightSinTwist b t) Ma Mb Na Nb S) := by
        dsimp only [G]
        calc
          (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖F q χ t‖) ≤
              ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
                (Real.exp (-ε * t) / t) *
                  (‖(∑ m ∈ sM, leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                      (∑ n ∈ sN, rightCosTwist b t n * χ.1 (n : ZMod q))‖ +
                   ‖(∑ m ∈ sM, leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                      (∑ n ∈ sN, rightSinTwist b t n * χ.1 (n : ZMod q))‖) := by
            apply Finset.sum_le_sum
            intro q hq
            apply mul_le_mul_of_nonneg_left
            · exact Finset.sum_le_sum fun χ hχ => hpoint q χ
            · dsimp [w]
              positivity
          _ = (Real.exp (-ε * t) / t) *
              (rankOneRectangularWeightedPrimitiveMean
                  (leftSinTwist a y t) (rightCosTwist b t) Ma Mb Na Nb S +
               rankOneRectangularWeightedPrimitiveMean
                  (leftCosTwist a y t) (rightSinTwist b t) Ma Mb Na Nb S) := by
            unfold rankOneRectangularWeightedPrimitiveMean
            rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            calc
              w q * ∑ χ : PrimitiveCharacter q,
                  (Real.exp (-ε * t) / t) *
                    (‖(∑ m ∈ sM, leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                        (∑ n ∈ sN, rightCosTwist b t n * χ.1 (n : ZMod q))‖ +
                     ‖(∑ m ∈ sM, leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                        (∑ n ∈ sN, rightSinTwist b t n * χ.1 (n : ZMod q))‖) =
                  w q * ((Real.exp (-ε * t) / t) *
                    ∑ χ : PrimitiveCharacter q,
                      ‖(∑ m ∈ sM, leftSinTwist a y t m * χ.1 (m : ZMod q)) *
                        (∑ n ∈ sN, rightCosTwist b t n * χ.1 (n : ZMod q))‖ +
                    (Real.exp (-ε * t) / t) *
                    ∑ χ : PrimitiveCharacter q,
                      ‖(∑ m ∈ sM, leftCosTwist a y t m * χ.1 (m : ZMod q)) *
                        (∑ n ∈ sN, rightSinTwist b t n * χ.1 (n : ZMod q))‖) := by
                      simp_rw [mul_add]
                      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
                      rw [mul_add]
              _ = _ := by
                simp only [norm_mul]
                dsimp only [w, sM, sN]
                rw [div_eq_mul_inv]
                ring
      _ ≤ (Real.exp (-ε * t) / t) *
          (min 1 (L₁ * t) * R + min 1 (L₂ * t) * R) := by
        apply mul_le_mul_of_nonneg_left
        · exact add_le_add (hlane₁ t ht) (hlane₂ t ht)
        · exact div_nonneg hexp (show 0 ≤ t from (show 0 < t from ht).le)
      _ = (dampedPerronMajorantIntegrand ε L₁ t +
          dampedPerronMajorantIntegrand ε L₂ t) * R := by
        rw [dampedPerronMajorantIntegrand, if_neg ht0,
          dampedPerronMajorantIntegrand, if_neg ht0]
        ring
  have hmajorInt :
      (∫ t in Set.Ioi (0 : ℝ), G t) ≤
        ((L₁ + Real.log (1 / ε) + 1) +
          (L₂ + Real.log (1 / ε) + 1)) * R := by
    calc
      (∫ t in Set.Ioi (0 : ℝ), G t) ≤
          ∫ t in Set.Ioi (0 : ℝ),
            (dampedPerronMajorantIntegrand ε L₁ t +
              dampedPerronMajorantIntegrand ε L₂ t) * R := by
        apply MeasureTheory.integral_mono_ae hGint
        · exact ((dampedPerronMajorant_integrableOn_Ioi hε hL₁).add
            (dampedPerronMajorant_integrableOn_Ioi hε hL₂)).mul_const R
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hG t ht
      _ = ((∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₁ t) +
            (∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₂ t)) * R := by
        rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_add
          (dampedPerronMajorant_integrableOn_Ioi hε hL₁)
          (dampedPerronMajorant_integrableOn_Ioi hε hL₂)]
      _ ≤ ((L₁ + Real.log (1 / ε) + 1) +
            (L₂ + Real.log (1 / ε) + 1)) * R := by
        gcongr
        · exact dampedPerronMajorant_integral_Ioi_le hε hε1 hL₁
        · exact dampedPerronMajorant_integral_Ioi_le hε hε1 hL₂
  have hlogε : Real.log (1 / ε) = 2 * Real.log (M : ℝ) := by
    dsimp only [ε]
    rw [show 1 / (1 / (M : ℝ) ^ 2) = (M : ℝ) ^ 2 by field_simp,
      Real.log_pow]
    norm_num
  have hGfinal : (∫ t in Set.Ioi (0 : ℝ), G t) ≤
      (7 * Real.log (M : ℝ) + 2) * R := by
    rw [hlogε] at hmajorInt
    dsimp only [L₁, L₂] at hmajorInt
    convert hmajorInt using 1 <;> ring
  unfold rectangularSmoothedKernelWeightedPrimitiveMean
  change (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
    ‖rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ‖) ≤ _
  calc
    (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
        ‖rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ‖) ≤
      (1 / 2) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖D q χ‖) +
        (1 / Real.pi) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
          ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) := by
      calc
        (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
            ‖rectangularSmoothedKernelCharacterSum a b ε y Ma Mb Na Nb q χ‖) ≤
            ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
              ((1 / 2) * ‖D q χ‖ + (1 / Real.pi) *
                ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) := by
          apply Finset.sum_le_sum
          intro q hq
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro χ hχ
            rw [hkernel q χ]
            calc
              ‖(1 / 2 : ℂ) * D q χ + (1 / Real.pi : ℂ) *
                  ∫ t in Set.Ioi (0 : ℝ), F q χ t‖ ≤
                  ‖(1 / 2 : ℂ) * D q χ‖ +
                    ‖(1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), F q χ t‖ :=
                norm_add_le _ _
              _ = (1 / 2) * ‖D q χ‖ + (1 / Real.pi) *
                  ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖ := by
                have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
                have hpi : ‖(1 / Real.pi : ℂ)‖ = (1 / Real.pi : ℝ) := by
                  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_pos Real.pi_pos, one_div]
                simp only [norm_mul, hhalf, hpi]
          · dsimp [w]
            positivity
        _ = (1 / 2) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖D q χ‖) +
              (1 / Real.pi) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
                ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro q hq
          calc
            w q * ∑ χ : PrimitiveCharacter q,
                ((1 / 2) * ‖D q χ‖ + (1 / Real.pi) *
                  ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) =
                w q * ((1 / 2) * ∑ χ : PrimitiveCharacter q, ‖D q χ‖ +
                  (1 / Real.pi) * ∑ χ : PrimitiveCharacter q,
                    ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
            _ = _ := by ring
    _ ≤ (1 / 2) * R + (1 / Real.pi) * ((7 * Real.log (M : ℝ) + 2) * R) := by
      gcongr
      · rw [hDmean]
        exact hbase
      · exact hImean.trans hGfinal
    _ = (1 / 2 + (7 * Real.log (M : ℝ) + 2) / Real.pi) * R := by ring
    _ = _ := rfl

/-- Sharp-to-smoothed comparison with the error displayed explicitly.  The
product-support bound is the exact hyperbolic support condition used to apply
the half-step separation lemma to the integer `m*n`. -/
theorem rectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    (a b : ℤ → ℂ) (Y M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hM : 1 ≤ M) (hYM : Y ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    rectangularSharpHyperbolicWeightedPrimitiveMean a b Y Ma Mb Na Nb S ≤
      rectangularSmoothedKernelWeightedPrimitiveMean a b (1 / (M : ℝ) ^ 2)
        (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y)
        Ma Mb Na Nb S +
      (8 / (Real.pi * (M : ℝ))) *
        rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
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
      have hnorm (r s : ℝ) : ‖(r : ℂ) - (s : ℂ)‖ = |r - s| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hnorm_one (s : ℝ) : ‖(1 : ℂ) - (s : ℂ)‖ = |1 - s| := by
        simpa using hnorm 1 s
      have hnorm_zero (s : ℝ) : ‖(0 : ℂ) - (s : ℂ)‖ = |0 - s| := by
        simpa using hnorm 0 s
      by_cases hcut : m * n ≤ (Y : ℤ)
      · simpa only [if_pos hcut] using hnorm_one
          (dampedArctanPerronKernel ε
            (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
              ((m * n : ℤ) : ℝ))))
      · simpa only [if_neg hcut] using hnorm_zero
          (dampedArctanPerronKernel ε
            (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
              ((m * n : ℤ) : ℝ))))
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
  have hsingle : ∀ q (χ : PrimitiveCharacter q),
      ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ≤
        ‖rectangularSmoothedKernelCharacterSum a b ε
          (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y)
          Ma Mb Na Nb q χ‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
    intro q χ
    let A := rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ
    let B := rectangularSmoothedKernelCharacterSum a b ε
      (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y) Ma Mb Na Nb q χ
    calc
      ‖A‖ = ‖B + (A - B)‖ := by congr 1 <;> ring
      _ ≤ ‖B‖ + ‖A - B‖ := norm_add_le _ _
      _ ≤ ‖B‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
        gcongr
        dsimp [A, B, rectangularSharpHyperbolicCharacterSum,
          rectangularSmoothedKernelCharacterSum]
        rw [← Finset.sum_sub_distrib]
        calc
          ‖∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
              ((∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                  (if m * n ≤ (Y : ℤ) then 1 else 0)) -
               ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                  (dampedArctanPerronKernel ε
                    (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                      ((m * n : ℤ) : ℝ))) : ℂ))‖ ≤
              ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                ‖(∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                  a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                    (if m * n ≤ (Y : ℤ) then 1 else 0)) -
                 ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                  a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                    (dampedArctanPerronKernel ε
                      (Real.log (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y /
                        ((m * n : ℤ) : ℝ))) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
              ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                E * ‖a m‖ * ‖b n‖ := by
            apply Finset.sum_le_sum
            intro m hm
            rw [← Finset.sum_sub_distrib]
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => hpoint q χ m hm n hn)
          _ = E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
            unfold rectangularCoefficientL1
            calc
              (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                  ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                    E * ‖a m‖ * ‖b n‖) =
                  ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                    E * ‖a m‖ *
                      (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    rw [Finset.mul_sum]
              _ = E * (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), ‖a m‖) *
                    (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), ‖b n‖) := by
                    rw [← Finset.sum_mul, ← Finset.mul_sum]
              _ = _ := by ring
  unfold rectangularSharpHyperbolicWeightedPrimitiveMean
    rectangularSmoothedKernelWeightedPrimitiveMean weightedPrimitiveFamilyMass
  change _ ≤ _ + E * rectangularCoefficientL1 a b Ma Mb Na Nb * _
  calc
    ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSharpHyperbolicCharacterSum a b Y Ma Mb Na Nb q χ‖ ≤
      ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          (‖rectangularSmoothedKernelCharacterSum a b ε
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y)
              Ma Mb Na Nb q χ‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun χ _ => hsingle q χ) (by positivity)
    _ = ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : PrimitiveCharacter q,
            ‖rectangularSmoothedKernelCharacterSum a b ε
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep Y)
              Ma Mb Na Nb q χ‖ +
        E * rectangularCoefficientL1 a b Ma Mb Na Nb *
          ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) * Fintype.card (PrimitiveCharacter q) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring

end

end AnalyticNumberTheory.LargeSieve
