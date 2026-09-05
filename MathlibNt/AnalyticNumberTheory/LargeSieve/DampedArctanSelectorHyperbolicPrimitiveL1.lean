import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanHyperbolicPrimitiveL1
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanMaximalPhaseSeparation

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Character-wise half-step smoothing still satisfies the same exact damped
Perron formula; only the positive-frequency majorant changes.  The four
selector-separated rank-one lanes contribute respectively `2 log M`, `log M`,
`log M`, and `2 log M`, so for `ε = M⁻²` the integral cost is exactly
`14 log M + 4`. -/
theorem selectorRectangularSmoothedKernelWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (Ma Mb : ℤ) (Na Nb Q M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
          (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
          Ma Mb Na Nb q χ‖) ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
        rankOneRectangularLSRHS a b Ma Mb Na Nb Q := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let R : ℝ := rankOneRectangularLSRHS a b Ma Mb Na Nb Q
  let sM : Finset ℤ := Finset.Icc (Ma + 1) (Ma + Na)
  let sN : Finset ℤ := Finset.Icc (Mb + 1) (Mb + Nb)
  let w : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let Y' : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ)
  let D : (q : ℕ) → PrimitiveCharacter q → ℂ := fun q χ =>
    ((∑ m ∈ sM, a m * χ.1 (m : ZMod q)) *
      (∑ n ∈ sN, b n * χ.1 (n : ZMod q)))
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ → ℂ := fun q χ t =>
    (Real.exp (-ε * t) : ℂ) *
      rectangularKernelCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ
  let G : ℝ → ℝ := fun t =>
    ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖F q χ t‖
  let L₁ : ℝ := 2 * Real.log (M : ℝ)
  let L₂ : ℝ := Real.log (M : ℝ)
  have hM1 : 1 ≤ M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    rw [div_le_one (sq_pos_of_pos hMr)]
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    nlinarith [sq_nonneg ((M : ℝ) - 1)]
  have hlogM : 0 ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hM1)
  have hL₁ : 0 ≤ L₁ := by
    dsimp [L₁]
    positivity
  have hL₂ : 0 ≤ L₂ := hlogM
  have hR : 0 ≤ R := by
    dsimp [R, rankOneRectangularLSRHS]
    positivity
  have hscalarInt : ∀ x : ℝ, Integrable (fun t : ℝ =>
      Real.exp (-ε * t) * truncatedPerronIntegrand x t)
      (volume.restrict (Set.Ioi 0)) := by
    intro x
    have he : Integrable (fun t : ℝ => Real.exp (-ε * t))
        (volume.restrict (Set.Ioi 0)) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0
    apply he.mul_bdd
    · exact (continuous_truncatedPerronIntegrand_right x).aestronglyMeasurable
    · filter_upwards with t
      simpa [Real.norm_eq_abs] using abs_truncatedPerronIntegrand_le x t
  have htermInt :
      ∀ q (χ : PrimitiveCharacter q) (m : ℤ), m ∈ sM →
        ∀ n ∈ sN,
          Integrable (fun t : ℝ =>
            (Real.exp (-ε * t) : ℂ) *
              (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                (truncatedPerronIntegrand
                  (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ)))
            (volume.restrict (Set.Ioi 0)) := by
    intro q χ m hm n hn
    have hg : Integrable (fun t : ℝ =>
        (Real.exp (-ε * t) : ℂ) *
          (truncatedPerronIntegrand
            (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      have hs := (hscalarInt (Real.log (Y' q χ / ((m * n : ℤ) : ℝ)))).ofReal (𝕜 := ℂ)
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
  have hFint : ∀ q (χ : PrimitiveCharacter q), IntegrableOn (F q χ) (Set.Ioi 0) := by
    intro q χ
    unfold F rectangularKernelCharacterSum
    simp_rw [Finset.mul_sum]
    exact hsumInt sM (fun m t => ∑ n ∈ sN,
      (Real.exp (-ε * t) : ℂ) *
        (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (truncatedPerronIntegrand
            (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ)))
      (volume.restrict (Set.Ioi 0)) (fun m hm =>
        hsumInt sN (fun n t =>
          (Real.exp (-ε * t) : ℂ) *
            (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
              (truncatedPerronIntegrand
                (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ)))
          (volume.restrict (Set.Ioi 0)) (htermInt q χ m hm))
  have hkernel : ∀ q (χ : PrimitiveCharacter q),
      rectangularSmoothedKernelCharacterSum a b ε (Y' q χ) Ma Mb Na Nb q χ =
        (1 / 2 : ℂ) * D q χ +
        (1 / Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), F q χ t := by
    intro q χ
    unfold rectangularSmoothedKernelCharacterSum
    have hi : (∫ t in Set.Ioi (0 : ℝ), F q χ t) =
        ∑ m ∈ sM, ∑ n ∈ sN,
          a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
            (∫ t in Set.Ioi (0 : ℝ),
              (Real.exp (-ε * t) *
                truncatedPerronIntegrand
                  (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ)) := by
      unfold F rectangularKernelCharacterSum
      simp_rw [Finset.mul_sum]
      rw [integral_finset_sum sM]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [integral_finset_sum sN]
        · apply Finset.sum_congr rfl
          intro n hn
          rw [← MeasureTheory.integral_const_mul]
          congr 1
          funext t
          push_cast
          ring
        · intro n hn
          exact htermInt q χ m hm n hn
      · intro m hm
        exact hsumInt sN (fun n t =>
          (Real.exp (-ε * t) : ℂ) *
            (a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
              (truncatedPerronIntegrand
                (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ)))
          (volume.restrict (Set.Ioi 0)) (htermInt q χ m hm)
    rw [hi]
    have hprod :
        D q χ =
          ∑ m ∈ sM, ∑ n ∈ sN,
            (a m * χ.1 (m : ZMod q)) * (b n * χ.1 (n : ZMod q)) := by
      unfold D
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    rw [hprod]
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [dampedArctanPerronKernel_eq_half_add_integral _ _ hε]
    rw [Int.cast_mul, map_mul]
    have hcast :
        ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
          truncatedPerronIntegrand
            (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
          ∫ t in Set.Ioi (0 : ℝ),
            (Real.exp (-ε * t) *
              truncatedPerronIntegrand
                (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℂ) := by
      simpa only [Complex.ofRealCLM_apply, ← Complex.ofReal_mul] using
        (Complex.ofRealCLM.integral_comp_comm
          (hscalarInt (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))))).symm
    have hformula :
        ((1 / 2 + (1 / Real.pi) *
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
            truncatedPerronIntegrand
              (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) =
          (1 / 2 : ℂ) + (1 / Real.pi : ℂ) *
            ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-ε * t) *
              truncatedPerronIntegrand
                (Real.log (Y' q χ / ((m * n : ℤ) : ℝ))) t : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hformula, hcast]
    ring
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
  have hY0 : ∀ q χ, 1 / 2 ≤ Y' q χ := by
    intro q χ
    dsimp [Y']
    unfold MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep
    linarith
  have hY'M : ∀ q χ, Y' q χ ≤ (M : ℝ) + 1 / 2 := by
    intro q χ
    dsimp [Y']
    unfold MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep
    have hYR : (Y q χ : ℝ) ≤ M := by exact_mod_cast hYM q χ
    linarith
  have hcc : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
        R := by
    intro t ht
    have heA := sum_norm_sq_phaseCosTwist_le a t sM
    have heB := sum_norm_sq_phaseCosTwist_le b t sN
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb Q hQ S hS
    let Aphase : ℝ :=
      largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ sM, ‖phaseCosTwist a t m‖ ^ 2
    let Aplain : ℝ :=
      largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ sM, ‖a m‖ ^ 2
    let Bphase : ℝ :=
      largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ sN, ‖phaseCosTwist b t n‖ ^ 2
    let Bplain : ℝ :=
      largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ sN, ‖b n‖ ^ 2
    calc
      rankOneRectangularWeightedPrimitiveMean
          (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt Aphase * Real.sqrt Bphase := by
            simpa [Aphase, Bphase, sM, sN] using hls
      _ ≤ Real.sqrt Aplain * Real.sqrt Bphase := by
        exact mul_le_mul
          (by
            apply Real.sqrt_le_sqrt
            dsimp [Aphase, Aplain]
            exact mul_le_mul_of_nonneg_left heA (by
              unfold largeSieveBound
              positivity))
          le_rfl (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt Aplain * Real.sqrt Bplain := by
        exact mul_le_mul le_rfl
          (by
            apply Real.sqrt_le_sqrt
            dsimp [Bphase, Bplain]
            exact mul_le_mul_of_nonneg_left heB (by
              unfold largeSieveBound
              positivity))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ R := by
        dsimp [R, rankOneRectangularLSRHS]
        exact le_rfl
  have hsc : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
        min 1 (L₂ * t) * R := by
    intro t ht
    have hc : 0 ≤ min 1 (L₂ * t) :=
      le_min (by norm_num) (mul_nonneg hL₂ ht.le)
    have heA := sum_norm_sq_phaseSinTwist_Icc_le a t Ma Na M hM1 hm1 hmM
    have heB := sum_norm_sq_phaseCosTwist_le b t sN
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb Q hQ S hS
    calc
      rankOneRectangularWeightedPrimitiveMean
          (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖phaseSinTwist a t m‖ ^ 2) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖phaseCosTwist b t n‖ ^ 2) := by
            simpa [sM, sN] using hls
      _ ≤ Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ((min 1 (L₂ * t)) ^ 2 * ∑ m ∈ sM, ‖a m‖ ^ 2)) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖b n‖ ^ 2) := by
        gcongr
        · unfold largeSieveBound
          positivity
        · simpa [L₂, abs_of_pos ht] using heA
        · unfold largeSieveBound
          positivity
      _ = min 1 (L₂ * t) * R := by
        have hA : 0 ≤ largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖a m‖ ^ 2 := by
          unfold largeSieveBound
          positivity
        rw [show largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
              ((min 1 (L₂ * t)) ^ 2 * ∑ m ∈ sM, ‖a m‖ ^ 2) =
            (min 1 (L₂ * t)) ^ 2 *
              (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
                ∑ m ∈ sM, ‖a m‖ ^ 2) by ring,
          Real.sqrt_mul (sq_nonneg (min 1 (L₂ * t))), Real.sqrt_sq hc]
        dsimp [R, rankOneRectangularLSRHS]
        ring
  have hcs : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
        min 1 (L₂ * t) * R := by
    intro t ht
    have hc : 0 ≤ min 1 (L₂ * t) :=
      le_min (by norm_num) (mul_nonneg hL₂ ht.le)
    have heA := sum_norm_sq_phaseCosTwist_le a t sM
    have heB := sum_norm_sq_phaseSinTwist_Icc_le b t Mb Nb M hM1 hn1 hnM
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb Q hQ S hS
    calc
      rankOneRectangularWeightedPrimitiveMean
          (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt (largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
            ∑ m ∈ sM, ‖phaseCosTwist a t m‖ ^ 2) *
          Real.sqrt (largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
            ∑ n ∈ sN, ‖phaseSinTwist b t n‖ ^ 2) := by
            simpa [sM, sN] using hls
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
        dsimp [R, rankOneRectangularLSRHS]
        ring
  have hsin_plain_left : ∀ t : ℝ,
      ∑ m ∈ sM, ‖phaseSinTwist a t m‖ ^ 2 ≤
        ∑ m ∈ sM, ‖a m‖ ^ 2 := by
    intro t
    have hs := sum_norm_sq_phaseSinTwist_Icc_le a t Ma Na M hM1 hm1 hmM
    have hmin : 0 ≤ min 1 (Real.log (M : ℝ) * |t|) := by
      apply le_min
      · norm_num
      · exact mul_nonneg hlogM (abs_nonneg t)
    have hfac : (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 ≤ 1 := by
      have hle : min 1 (Real.log (M : ℝ) * |t|) ≤ 1 := min_le_left _ _
      nlinarith
    have hsum : 0 ≤ ∑ m ∈ sM, ‖a m‖ ^ 2 := by
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      ∑ m ∈ sM, ‖phaseSinTwist a t m‖ ^ 2 ≤
          (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 * ∑ m ∈ sM, ‖a m‖ ^ 2 := hs
      _ ≤ ∑ m ∈ sM, ‖a m‖ ^ 2 := by
        nlinarith
  have hsin_plain_right : ∀ t : ℝ,
      ∑ n ∈ sN, ‖phaseSinTwist b t n‖ ^ 2 ≤
        ∑ n ∈ sN, ‖b n‖ ^ 2 := by
    intro t
    have hs := sum_norm_sq_phaseSinTwist_Icc_le b t Mb Nb M hM1 hn1 hnM
    have hmin : 0 ≤ min 1 (Real.log (M : ℝ) * |t|) := by
      apply le_min
      · norm_num
      · exact mul_nonneg hlogM (abs_nonneg t)
    have hfac : (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 ≤ 1 := by
      have hle : min 1 (Real.log (M : ℝ) * |t|) ≤ 1 := min_le_left _ _
      nlinarith
    have hsum : 0 ≤ ∑ n ∈ sN, ‖b n‖ ^ 2 := by
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      ∑ n ∈ sN, ‖phaseSinTwist b t n‖ ^ 2 ≤
          (min 1 (Real.log (M : ℝ) * |t|)) ^ 2 * ∑ n ∈ sN, ‖b n‖ ^ 2 := hs
      _ ≤ ∑ n ∈ sN, ‖b n‖ ^ 2 := by
        nlinarith
  have hss : ∀ t : ℝ, 0 < t →
      rankOneRectangularWeightedPrimitiveMean
          (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
        R := by
    intro t ht
    have heA := hsin_plain_left t
    have heB := hsin_plain_right t
    have hls := rankOneRectangularWeightedPrimitiveMean_le
      (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb Q hQ S hS
    let Aphase : ℝ :=
      largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ sM, ‖phaseSinTwist a t m‖ ^ 2
    let Aplain : ℝ :=
      largeSieveBound Na (1 / (Q : ℝ) ^ 2) *
        ∑ m ∈ sM, ‖a m‖ ^ 2
    let Bphase : ℝ :=
      largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ sN, ‖phaseSinTwist b t n‖ ^ 2
    let Bplain : ℝ :=
      largeSieveBound Nb (1 / (Q : ℝ) ^ 2) *
        ∑ n ∈ sN, ‖b n‖ ^ 2
    calc
      rankOneRectangularWeightedPrimitiveMean
          (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
          Real.sqrt Aphase * Real.sqrt Bphase := by
            simpa [Aphase, Bphase, sM, sN] using hls
      _ ≤ Real.sqrt Aplain * Real.sqrt Bphase := by
        exact mul_le_mul
          (by
            apply Real.sqrt_le_sqrt
            dsimp [Aphase, Aplain]
            exact mul_le_mul_of_nonneg_left heA (by
              unfold largeSieveBound
              positivity))
          le_rfl (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt Aplain * Real.sqrt Bplain := by
        exact mul_le_mul le_rfl
          (by
            apply Real.sqrt_le_sqrt
            dsimp [Bphase, Bplain]
            exact mul_le_mul_of_nonneg_left heB (by
              unfold largeSieveBound
              positivity))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ R := by
        dsimp [R, rankOneRectangularLSRHS]
        exact le_rfl
  have hG :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        G t ≤
          (2 * dampedPerronMajorantIntegrand ε L₁ t +
            2 * dampedPerronMajorantIntegrand ε L₂ t) * R := by
    intro t ht
    have ht0 : 0 < t := ht
    have hexp : 0 ≤ Real.exp (-ε * t) := (Real.exp_pos _).le
    have hd : 0 ≤ min 1 (L₁ * t) := le_min (by norm_num) (mul_nonneg hL₁ ht0.le)
    have hl : 0 ≤ min 1 (L₂ * t) := le_min (by norm_num) (mul_nonneg hL₂ ht0.le)
    have hselector :
        selectorDampedLogRectangularWeightedMean a b Y' t Ma Mb Na Nb S ≤
          (1 / t) *
            (min 1 (L₁ * t) * R +
              min 1 (L₂ * t) * R +
              min 1 (L₂ * t) * R +
              min 1 (L₁ * t) * R) := by
      have hsel := selectorDampedLogRectangularWeightedMean_le_four_rankOne
        a b hM Y' ht0 Ma Mb Na Nb S hY0 hY'M hm1 hmM hn1 hnM
      refine hsel.trans ?_
      apply mul_le_mul_of_nonneg_left
      · have h1 :
            min 1 (L₁ * t) *
                rankOneRectangularWeightedPrimitiveMean
                  (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
              min 1 (L₁ * t) * R :=
          mul_le_mul_of_nonneg_left (hcc t ht0) hd
        have h2 :
            rankOneRectangularWeightedPrimitiveMean
                (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤
              min 1 (L₂ * t) * R := hsc t ht0
        have h3 :
            rankOneRectangularWeightedPrimitiveMean
                (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
              min 1 (L₂ * t) * R := hcs t ht0
        have h4 :
            min 1 (L₁ * t) *
                rankOneRectangularWeightedPrimitiveMean
                  (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤
              min 1 (L₁ * t) * R :=
          mul_le_mul_of_nonneg_left (hss t ht0) hd
        linarith
      · positivity
    have hFpoint : ∀ q (χ : PrimitiveCharacter q),
        ‖F q χ t‖ =
          Real.exp (-ε * t) *
            ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖ := by
      intro q χ
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hsum :
          rectangularKernelCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ =
            dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ := by
        unfold rectangularKernelCharacterSum dampedLogRectangularCharacterSum
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        simp [truncatedPerronIntegrand, ht0.ne']
      rw [hsum]
    calc
      G t = Real.exp (-ε * t) *
          selectorDampedLogRectangularWeightedMean a b Y' t Ma Mb Na Nb S := by
        dsimp [G]
        simp_rw [hFpoint]
        unfold selectorDampedLogRectangularWeightedMean
        calc
          ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
              Real.exp (-ε * t) *
                ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖ =
              ∑ q ∈ S, Real.exp (-ε * t) *
                (w q * ∑ χ : PrimitiveCharacter q,
                  ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖) := by
                apply Finset.sum_congr rfl
                intro q hq
                calc
                  w q * ∑ χ : PrimitiveCharacter q,
                      Real.exp (-ε * t) *
                        ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖ =
                      w q * (Real.exp (-ε * t) *
                        ∑ χ : PrimitiveCharacter q,
                          ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖) := by
                        rw [← Finset.mul_sum]
                  _ = Real.exp (-ε * t) *
                      (w q * ∑ χ : PrimitiveCharacter q,
                        ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖) := by
                        ring
          _ = Real.exp (-ε * t) *
              ∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
                ‖dampedLogRectangularCharacterSum a b (Y' q χ) t Ma Mb Na Nb q χ‖ := by
                rw [← Finset.mul_sum]
      _ ≤ Real.exp (-ε * t) *
          ((1 / t) *
            (min 1 (L₁ * t) * R +
              min 1 (L₂ * t) * R +
              min 1 (L₂ * t) * R +
              min 1 (L₁ * t) * R)) := by
        exact mul_le_mul_of_nonneg_left hselector hexp
      _ = (2 * dampedPerronMajorantIntegrand ε L₁ t +
            2 * dampedPerronMajorantIntegrand ε L₂ t) * R := by
        rw [dampedPerronMajorantIntegrand, if_neg ht0.ne',
          dampedPerronMajorantIntegrand, if_neg ht0.ne']
        ring
  have hmajorInt :
      (∫ t in Set.Ioi (0 : ℝ), G t) ≤
        (2 * (L₁ + Real.log (1 / ε) + 1) +
          2 * (L₂ + Real.log (1 / ε) + 1)) * R := by
    calc
      (∫ t in Set.Ioi (0 : ℝ), G t) ≤
          ∫ t in Set.Ioi (0 : ℝ),
            (2 * dampedPerronMajorantIntegrand ε L₁ t +
              2 * dampedPerronMajorantIntegrand ε L₂ t) * R := by
        apply MeasureTheory.integral_mono_ae hGint
        · exact ((dampedPerronMajorant_integrableOn_Ioi hε hL₁).const_mul 2).add
            ((dampedPerronMajorant_integrableOn_Ioi hε hL₂).const_mul 2) |>.mul_const R
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hG t ht
      _ = (2 * (∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₁ t) +
            2 * (∫ t in Set.Ioi (0 : ℝ), dampedPerronMajorantIntegrand ε L₂ t)) * R := by
        rw [MeasureTheory.integral_mul_const]
        rw [MeasureTheory.integral_add
          ((dampedPerronMajorant_integrableOn_Ioi hε hL₁).const_mul 2)
          ((dampedPerronMajorant_integrableOn_Ioi hε hL₂).const_mul 2)]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ (2 * (L₁ + Real.log (1 / ε) + 1) +
            2 * (L₂ + Real.log (1 / ε) + 1)) * R := by
        nlinarith [hR, dampedPerronMajorant_integral_Ioi_le hε hε1 hL₁,
          dampedPerronMajorant_integral_Ioi_le hε hε1 hL₂]
  have hlogε : Real.log (1 / ε) = 2 * Real.log (M : ℝ) := by
    dsimp [ε]
    rw [show 1 / (1 / (M : ℝ) ^ 2) = (M : ℝ) ^ 2 by field_simp,
      Real.log_pow]
    norm_num
  have hGfinal : (∫ t in Set.Ioi (0 : ℝ), G t) ≤
      (14 * Real.log (M : ℝ) + 4) * R := by
    rw [hlogε] at hmajorInt
    dsimp [L₁, L₂] at hmajorInt
    convert hmajorInt using 1 <;> ring
  change (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
    ‖rectangularSmoothedKernelCharacterSum a b ε (Y' q χ) Ma Mb Na Nb q χ‖) ≤ _
  calc
    (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
        ‖rectangularSmoothedKernelCharacterSum a b ε (Y' q χ) Ma Mb Na Nb q χ‖) ≤
      (1 / 2) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q, ‖D q χ‖) +
        (1 / Real.pi) * (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
          ‖∫ t in Set.Ioi (0 : ℝ), F q χ t‖) := by
      calc
        (∑ q ∈ S, w q * ∑ χ : PrimitiveCharacter q,
            ‖rectangularSmoothedKernelCharacterSum a b ε (Y' q χ) Ma Mb Na Nb q χ‖) ≤
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
    _ ≤ (1 / 2) * R + (1 / Real.pi) * ((14 * Real.log (M : ℝ) + 4) * R) := by
      gcongr
      · rw [hDmean]
        exact hbase
      · exact hImean.trans hGfinal
    _ = (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) * R := by ring
    _ = _ := rfl

private theorem selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hM : 1 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
            (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
            Ma Mb Na Nb q χ‖) +
      (8 / (Real.pi * (M : ℝ))) *
        rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let E : ℝ := 8 / (Real.pi * (M : ℝ))
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have herror : ∀ q (χ : PrimitiveCharacter q)
      (m : ℤ) (_ : m ∈ Finset.Icc (Ma + 1) (Ma + Na))
      (n : ℤ) (_ : n ∈ Finset.Icc (Mb + 1) (Mb + Nb)),
        |(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log
                (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                  ((m * n : ℤ) : ℝ)))| ≤ E := by
    intro q χ m hm n hn
    have hp := hmnPos m hm n hn
    let k : ℕ := (m * n).toNat
    have hkZ : (k : ℤ) = m * n := by
      exact Int.toNat_of_nonneg (le_of_lt hp)
    have hk0 : k ≠ 0 := by
      intro hk
      have : (m * n : ℤ) = 0 := by simpa [hk] using hkZ.symm
      omega
    have hkcut : k ≤ Y q χ ↔ m * n ≤ (Y q χ : ℤ) := by
      constructor
      · intro h
        rw [← hkZ]
        exact_mod_cast h
      · intro h
        rw [← hkZ] at h
        exact_mod_cast h
    have hh := abs_halfStepIndicator_sub_dampedArctanPerronKernel_le
      (ε := ε) (n := k) (Y := Y q χ) (M := M) hε hk0 hM (hYM q χ)
    have hconst : 8 * ε * (M : ℝ) / Real.pi = E := by
      dsimp [ε, E]
      field_simp [Real.pi_ne_zero, hMr.ne']
    have hkR : (k : ℝ) = ((m * n : ℤ) : ℝ) := by exact_mod_cast hkZ
    calc
      |(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℝ) -
          dampedArctanPerronKernel ε
            (Real.log
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                ((m * n : ℤ) : ℝ)))| ≤
          8 * ε * (M : ℝ) / Real.pi := by
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
          (if m * n ≤ (Y q χ : ℤ) then 1 else 0) -
        a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
          (dampedArctanPerronKernel ε
            (Real.log
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                ((m * n : ℤ) : ℝ))) : ℂ)‖ ≤
        E * ‖a m‖ * ‖b n‖ := by
    intro q χ m hm n hn
    rw [← mul_sub]
    simp only [norm_mul]
    have hc := hχ q χ ((m * n : ℤ) : ZMod q)
    have he := herror q χ m hm n hn
    have hreal :
        ‖(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log
                (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                  ((m * n : ℤ) : ℝ))) : ℂ)‖ =
          |(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log
                (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                  ((m * n : ℤ) : ℝ)))| := by
      have hnorm (r s : ℝ) : ‖(r : ℂ) - (s : ℂ)‖ = |r - s| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hnorm_one (s : ℝ) : ‖(1 : ℂ) - (s : ℂ)‖ = |1 - s| := by
        simpa using hnorm 1 s
      have hnorm_zero (s : ℝ) : ‖(0 : ℂ) - (s : ℂ)‖ = |0 - s| := by
        simpa using hnorm 0 s
      by_cases hcut : m * n ≤ (Y q χ : ℤ)
      · simpa only [if_pos hcut] using hnorm_one
          (dampedArctanPerronKernel ε
            (Real.log
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                ((m * n : ℤ) : ℝ))))
      · simpa only [if_neg hcut] using hnorm_zero
          (dampedArctanPerronKernel ε
            (Real.log
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                ((m * n : ℤ) : ℝ))))
    calc
      ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          ‖(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℂ) -
            (dampedArctanPerronKernel ε
              (Real.log
                (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                  ((m * n : ℤ) : ℝ))) : ℂ)‖ =
        ‖a m‖ * ‖b n‖ * ‖χ.1 ((m * n : ℤ) : ZMod q)‖ *
          |(if m * n ≤ (Y q χ : ℤ) then 1 else 0 : ℝ) -
            dampedArctanPerronKernel ε
              (Real.log
                (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                  ((m * n : ℤ) : ℝ)))| := by rw [hreal]
      _ ≤ ‖a m‖ * ‖b n‖ * 1 * E := by
        gcongr
      _ = E * ‖a m‖ * ‖b n‖ := by ring
  have hsingle : ∀ q (χ : PrimitiveCharacter q),
      ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖ ≤
        ‖rectangularSmoothedKernelCharacterSum a b ε
          (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
          Ma Mb Na Nb q χ‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb := by
    intro q χ
    let A := rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ
    let B := rectangularSmoothedKernelCharacterSum a b ε
      (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
      Ma Mb Na Nb q χ
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
                  (if m * n ≤ (Y q χ : ℤ) then 1 else 0)) -
               ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                  (dampedArctanPerronKernel ε
                    (Real.log
                      (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
                        ((m * n : ℤ) : ℝ))) : ℂ))‖ ≤
              ∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
                ‖(∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                  a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                    (if m * n ≤ (Y q χ : ℤ) then 1 else 0)) -
                 ∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb),
                  a m * b n * χ.1 ((m * n : ℤ) : ZMod q) *
                    (dampedArctanPerronKernel ε
                      (Real.log
                        (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ) /
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
  unfold weightedPrimitiveFamilyMass
  change _ ≤ _ + E * rectangularCoefficientL1 a b Ma Mb Na Nb * _
  calc
    ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖ ≤
      ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : PrimitiveCharacter q,
          (‖rectangularSmoothedKernelCharacterSum a b ε
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
              Ma Mb Na Nb q χ‖ + E * rectangularCoefficientL1 a b Ma Mb Na Nb) := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun χ _ => hsingle q χ) (by positivity)
    _ = ∑ q ∈ S, (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : PrimitiveCharacter q,
            ‖rectangularSmoothedKernelCharacterSum a b ε
              (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
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

/-- Character-wise selector version of the sharp hyperbolic rectangular
primitive `L¹` bound.  The smoothed selector mean is paid by the four
`y`-independent phase-separated lanes, and the sharp comparison keeps the exact
`8 / (π M)` coefficient error. -/
theorem selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (Ma Mb : ℤ) (Na Nb Q M : ℕ)
    (hQ : 0 < Q) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q)
    (hM : 3 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hm1 : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), 1 ≤ m)
    (hmM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na), m ≤ (M : ℤ))
    (hn1 : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 1 ≤ n)
    (hnM : ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), n ≤ (M : ℤ))
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), m * n ≤ (M : ℤ)) :
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
  have hsharp := selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    a b Y M Ma Mb Na Nb S (by omega) hYM hmnPos hmnM
  have hsmoothed := selectorRectangularSmoothedKernelWeightedPrimitiveMean_le
    a b Y Ma Mb Na Nb Q M hQ S hS hM hYM hm1 hmM hn1 hnM
  calc
    (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter q,
        ‖rectangularSharpHyperbolicCharacterSum a b (Y q χ) Ma Mb Na Nb q χ‖) ≤
      (∑ q ∈ S, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖rectangularSmoothedKernelCharacterSum a b (1 / (M : ℝ) ^ 2)
            (MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ))
            Ma Mb Na Nb q χ‖) +
      (8 / (Real.pi * (M : ℝ))) *
        rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := hsharp
    _ ≤ (1 / 2 + (14 * Real.log (M : ℝ) + 4) / Real.pi) *
          rankOneRectangularLSRHS a b Ma Mb Na Nb Q +
        (8 / (Real.pi * (M : ℝ))) *
          rectangularCoefficientL1 a b Ma Mb Na Nb * weightedPrimitiveFamilyMass S := by
      gcongr

end

end AnalyticNumberTheory.LargeSieve
