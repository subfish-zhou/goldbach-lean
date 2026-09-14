import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanHyperbolicPrimitiveL1
import MathlibNt.AnalyticNumberTheory.LargeSieve.DampedArctanMaximalPhaseSeparation

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Character-wise half-step smoothing still satisfies the same exact damped
Perron formula; only the positive-frequency majorant changes.  The four
selector-separated rank-one lanes contribute respectively `2 log M`, `log M`,
`log M`, and `2 log M`, so for `ε = M⁻²` the integral cost is bounded by
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
  classical
  let ε : ℝ := 1 / (M : ℝ) ^ 2
  let L := Real.log (M : ℝ)
  let R := rankOneRectangularLSRHS a b Ma Mb Na Nb Q
  let y := fun q χ => MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep (Y q χ)
  let w := fun q : ℕ => (q : ℝ) / (q.totient : ℝ)
  let F := fun q χ t => (Real.exp (-ε * t) : ℂ) *
    rectangularKernelCharacterSum a b (y q χ) t Ma Mb Na Nb q χ
  have hM1 : 1 ≤ M := by omega
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]; exact (div_le_one (by positivity)).2 (one_le_pow₀ hMr)
  have hL : 0 ≤ L := Real.log_nonneg hMr
  have hR : 0 ≤ R := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hw : ∀ q ∈ S, 0 ≤ w q := by intros; dsimp [w]; positivity
  have hy0 : ∀ q χ, 1 / 2 ≤ y q χ := by
    intro q χ
    dsimp [y, MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep]
    linarith [Nat.cast_nonneg (α := ℝ) (Y q χ)]
  have hyM : ∀ q χ, y q χ ≤ (M : ℝ) + 1 / 2 := by
    intro q χ
    dsimp [y, MathlibNt.SieveTheory.LiuWeight.liuPanPerronHalfStep]
    have hy : (Y q χ : ℝ) ≤ M := by exact_mod_cast hYM q χ
    linarith
  have hF : ∀ q χ, IntegrableOn (F q χ) (Ioi 0) := fun q χ =>
    (rectangularDampedPerron_integrable_formula a b ε (y q χ) hε Ma Mb Na Nb q χ).1
  let G := fun t => ∑ q ∈ S, w q * ∑ χ, ‖F q χ t‖
  have hG := dampedPerron_weighted_norm_integrable S w F (volume.restrict (Ioi 0)) hF
  -- Apply the large sieve to the four actual, selector-independent phase twists.
  have hmajor : ∀ t ∈ Ioi (0 : ℝ), G t ≤
      (dampedPerronMajorantIntegrand ε (2 * L) t +
        dampedPerronMajorantIntegrand ε L t) * (2 * R) := by
    intro t ht
    change 0 < t at ht
    let s := min 1 (L * t)
    let d := min 1 (2 * L * t)
    have hs : 0 ≤ s := le_min (by norm_num) (mul_nonneg hL ht.le)
    have hd : 0 ≤ d := le_min (by norm_num) (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsa := sum_norm_sq_phaseSinTwist_Icc_le a t Ma Na M hM1 hm1 hmM
    have hsb := sum_norm_sq_phaseSinTwist_Icc_le b t Mb Nb M hM1 hn1 hnM
    rw [abs_of_pos ht] at hsa hsb
    have hca := sum_norm_sq_phaseCosTwist_le a t (Finset.Icc (Ma + 1) (Ma + Na))
    have hcb := sum_norm_sq_phaseCosTwist_le b t (Finset.Icc (Mb + 1) (Mb + Nb))
    have ls := fun c d => rankOneRectangularWeightedPrimitiveMean_le_scaled_energy
      a b c d Ma Mb Na Nb Q hQ S hS
    have hcc : rankOneRectangularWeightedPrimitiveMean
        (phaseCosTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤ R := by
      simpa using ls (phaseCosTwist a t) (phaseCosTwist b t) 1 1
        (by norm_num) (by norm_num) (by simpa using hca) (by simpa using hcb)
    have hsc : rankOneRectangularWeightedPrimitiveMean
        (phaseSinTwist a t) (phaseCosTwist b t) Ma Mb Na Nb S ≤ s * R := by
      simpa using ls (phaseSinTwist a t) (phaseCosTwist b t) s 1 hs
        (by norm_num) hsa (by simpa using hcb)
    have hcs : rankOneRectangularWeightedPrimitiveMean
        (phaseCosTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤ s * R := by
      simpa using ls (phaseCosTwist a t) (phaseSinTwist b t) 1 s
        (by norm_num) hs (by simpa using hca) hsb
    have hss : rankOneRectangularWeightedPrimitiveMean
        (phaseSinTwist a t) (phaseSinTwist b t) Ma Mb Na Nb S ≤ R := by
      refine (ls (phaseSinTwist a t) (phaseSinTwist b t) s s hs hs hsa hsb).trans ?_
      exact mul_le_of_le_one_left hR (by nlinarith)
    have hb := selectorDampedLogRectangularWeightedMean_le_four_rankOne
      a b hM y ht Ma Mb Na Nb S hy0 hyM hm1 hmM hn1 hnM
    have hbound : selectorDampedLogRectangularWeightedMean a b y t Ma Mb Na Nb S ≤
        (1 / t) * ((d + s) * (2 * R)) := by
      refine hb.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ d * R + s * R + s * R + d * R :=
          add_le_add (add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hcc hd) hsc) hcs)
            (mul_le_mul_of_nonneg_left hss hd)
        _ = _ := by ring
    have hident : G t = Real.exp (-ε * t) *
        selectorDampedLogRectangularWeightedMean a b y t Ma Mb Na Nb S := by
      dsimp only [G, F, selectorDampedLogRectangularWeightedMean]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp only [rectangularKernelCharacterSum, dampedLogRectangularCharacterSum,
        truncatedPerronIntegrand, if_neg (ne_of_gt ht), Complex.ofReal_div]
      dsimp only [w]
      simp only [Finset.mul_sum, mul_left_comm]
    rw [hident]
    refine (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq ?_
    simp only [dampedPerronMajorantIntegrand, if_neg (ne_of_gt ht)]
    dsimp [d, s]
    ring
  have hint := dampedPerron_integral_le_two_majorants hε hε1
    (by positivity : 0 ≤ 2 * L) hL (by positivity : 0 ≤ 2 * R) hG hmajor
  have hlog : Real.log (1 / ε) = 2 * L := by
    simp [ε, L, Real.log_pow]
  rw [hlog] at hint
  have hint' : (∑ q ∈ S, w q * ∑ χ, ‖∫ t in Ioi (0 : ℝ), F q χ t‖) ≤
      (14 * L + 4) * R := by
    refine (dampedPerron_weighted_norm_integral_le S w hw F
      (volume.restrict (Ioi 0)) hF).trans (hint.trans_eq ?_)
    ring
  -- Use the signed identity before taking norms and averaging with nonnegative weights.
  have hadd := dampedPerron_weighted_norm_add_le S w hw
    (fun q χ => (∑ m ∈ Finset.Icc (Ma + 1) (Ma + Na), a m * χ.1 (m : ZMod q)) *
      (∑ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), b n * χ.1 (n : ZMod q)))
    (fun q χ => ∫ t in Ioi (0 : ℝ), F q χ t) (1 / 2) (1 / Real.pi)
    (by positivity) (by positivity)
  have hbase := rankOneRectangularWeightedPrimitiveMean_le a b Ma Mb Na Nb Q hQ S hS
  simp only [norm_mul] at hadd
  change _ ≤ (1 / 2) * rankOneRectangularWeightedPrimitiveMean a b Ma Mb Na Nb S +
    (1 / Real.pi) * (∑ q ∈ S, w q * ∑ χ, ‖∫ t in Ioi (0 : ℝ), F q χ t‖) at hadd
  calc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [(rectangularDampedPerron_integrable_formula a b ε (y q χ) hε
        Ma Mb Na Nb q χ).2]
      simp only [F, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    _ ≤ _ := hadd
    _ ≤ (1 / 2) * R + (1 / Real.pi) * ((14 * L + 4) * R) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by positivity))
        (mul_le_mul_of_nonneg_left hint' (by positivity))
    _ = (1 / 2 + (14 * L + 4) / Real.pi) * R := by ring


private theorem selectorRectangularSharpHyperbolicWeightedPrimitiveMean_le_smoothed
    (a b : ℤ → ℂ) (Y : (q : ℕ) → PrimitiveCharacter q → ℕ)
    (M : ℕ) (Ma Mb : ℤ) (Na Nb : ℕ) (S : Finset ℕ)
    (hM : 1 ≤ M)
    (hYM : ∀ q χ, Y q χ ≤ M)
    (hmnPos : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
      ∀ n ∈ Finset.Icc (Mb + 1) (Mb + Nb), 0 < m * n)
    (_hmnM : ∀ m ∈ Finset.Icc (Ma + 1) (Ma + Na),
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
  have hsingle := fun q χ => rectangularSharpHyperbolicCharacterSum_norm_le_smoothed
    a b (Y q χ) M Ma Mb Na Nb hM (hYM q χ) hmnPos q χ
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
