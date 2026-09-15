import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerPowerSaving

/-!
# Combined inverse-log discrepancy for Liu's Pan endpoint

The Type I endpoint, Type II endpoint, and complete signed-main kernel are
recombined before taking an absolute value.  Vaughan's finite identity then
identifies this expression with the source-weighted `Λ / log` discrepancy.
The already separated prime-power correction remains on its own power-saving
scale.

The older componentwise contracts are intentionally left unchanged.  Their
degenerate or conductor-one endpoint behavior does not prove the combined
estimate introduced here.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve

/-! ## Exact finite combination -/

/-- The Type I endpoint, Type II endpoint, and complete signed main, combined
inside one absolute value before any analytic estimate is applied. -/
noncomputable def liuPanCombinedInverseLogDiscrepancy
    (main : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  |panPieceSum y X q l f
        (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
    panPieceSum y X q l f
        (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
    liuPanSignedMainSum main y X q l f u v|

/-- Vaughan's logarithmic identity recombines the three endpoint terms into
the exact source-weighted `Λ / log` discrepancy. -/
theorem liuPanCombinedInverseLogDiscrepancy_eq
    (main : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogDiscrepancy main y X q l f u v =
      |∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          main ((y : ℝ) / a) / Nat.totient q) else 0| := by
  unfold liuPanCombinedInverseLogDiscrepancy panPieceSum liuPanSignedMainSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop, liuPanSignedMainKernel]
    rw [apLogVonMangoldt_eq_logPieces]
    ring
  · simp [hcop]

/-- Source-facing specialization of the exact combined identity. -/
theorem liuPanCombinedInverseLogDiscrepancy_source_eq
    (kappa : ℝ) (N y q l u v : ℕ) :
    liuPanCombinedInverseLogDiscrepancy
        (liuLogarithmicIntegral kappa) y N q l
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v =
      |∑ a ∈ Icc 1 N, if a.Coprime q then
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a *
          (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
            liuLogarithmicIntegral kappa ((y : ℝ) / a) / Nat.totient q)
        else 0| :=
  liuPanCombinedInverseLogDiscrepancy_eq
    (liuLogarithmicIntegral kappa) y N q l
    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v

/-- Maximum of the exact combined discrepancy over canonical reduced residues. -/
noncomputable def liuPanCombinedInverseLogMaxL
    (main : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l =>
      liuPanCombinedInverseLogDiscrepancy main y X q l f u v)).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Maximum of the exact combined discrepancy over `y ≤ x`. -/
noncomputable def liuPanCombinedInverseLogMaxY
    (main : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanCombinedInverseLogMaxL main y X q f u v)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The zero modulus has no canonical reduced residue. -/
@[simp] theorem liuPanCombinedInverseLogMaxL_zero
    (main : ℝ → ℝ) (y X : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL main y X 0 f u v = 0 := by
  simp [liuPanCombinedInverseLogMaxL]

/-- Modulus one uses its unique canonical residue `0`. -/
@[simp] theorem liuPanCombinedInverseLogMaxL_one
    (main : ℝ → ℝ) (y X : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL main y X 1 f u v =
      liuPanCombinedInverseLogDiscrepancy main y X 1 0 f u v := by
  simp [liuPanCombinedInverseLogMaxL]

/-- The zero-modulus `y`-maximum is canonically zero. -/
@[simp] theorem liuPanCombinedInverseLogMaxY_zero
    (main : ℝ → ℝ) (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxY main X 0 x f u v = 0 := by
  unfold liuPanCombinedInverseLogMaxY
  apply le_antisymm
  · apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩

/-- The modulus-one `y`-maximum retains the unique residue `0`. -/
theorem liuPanCombinedInverseLogMaxY_one
    (main : ℝ → ℝ) (X x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxY main X 1 x f u v =
      ((range (x + 1)).image (fun y =>
        liuPanCombinedInverseLogDiscrepancy main y X 1 0 f u v)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanCombinedInverseLogMaxY
  simp only [liuPanCombinedInverseLogMaxL_one]

theorem liuPanCombinedInverseLogDiscrepancy_nonneg
    (main : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanCombinedInverseLogDiscrepancy main y X q l f u v :=
  abs_nonneg _

theorem liuPanCombinedInverseLogMaxL_nonneg
    (main : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanCombinedInverseLogMaxL main y X q f u v := by
  unfold liuPanCombinedInverseLogMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · rw [dif_pos hS]
    obtain ⟨l, hl⟩ := hS
    apply (liuPanCombinedInverseLogDiscrepancy_nonneg main y X q l f u v).trans
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  · simp [hS]

theorem liuPanCombinedInverseLogMaxY_nonneg
    (main : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ liuPanCombinedInverseLogMaxY main X q x f u v := by
  unfold liuPanCombinedInverseLogMaxY
  apply (liuPanCombinedInverseLogMaxL_nonneg main 0 X q f u v).trans
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

/-! ## Exact correction separation and maxima -/

/-- Only the prime-power correction is separated after the three principal
endpoint terms have been recombined. -/
theorem abs_liuMainPanCoprimeSum_le_combinedInverseLog_add_primePower
    (main : ℝ → ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    |liuMainPanCoprimeSum main y X q l f| ≤
      liuPanCombinedInverseLogDiscrepancy main y X q l f u v +
        liuPanSignedCorrectionBound y X q l f := by
  rw [liuMainPanCoprimeSum_eq_sourceFaithfulSigned main y X q l f u v hf0]
  rw [sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  simp only [abs_neg]
  exact add_le_add le_rfl (abs_liuPanSignedCorrectionSum_le y X q l f)

/-- The canonical residue maximum inherits the exact combined-plus-correction
bound. -/
theorem liuMainPanMaxL_le_combinedInverseLog_add_primePower
    (main : ℝ → ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    liuMainPanMaxL main y X q f ≤
      liuPanCombinedInverseLogMaxL main y X q f u v +
        liuPanAPPrimePowerCorrectionMaxL y X q f := by
  unfold liuMainPanMaxL liuPanCombinedInverseLogMaxL
    liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hcombined := Finset.le_max'
      ((unitResidues q).image (fun l =>
        liuPanCombinedInverseLogDiscrepancy main y X q l f u v))
      (liuPanCombinedInverseLogDiscrepancy main y X q l f u v)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have hpp := Finset.le_max'
      ((unitResidues q).image (fun l =>
        liuPanSignedCorrectionBound y X q l f))
      (liuPanSignedCorrectionBound y X q l f)
      (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    exact (abs_liuMainPanCoprimeSum_le_combinedInverseLog_add_primePower
      main y X q l f u v hf0).trans (add_le_add hcombined hpp)
  · simp [hS]

/-- The two nested maxima preserve the combined-before-absolute-value route. -/
theorem liuMainPanMaxY_le_combinedInverseLog_add_primePower
    (main : ℝ → ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    liuMainPanMaxY main X q x f ≤
      liuPanCombinedInverseLogMaxY main X q x f u v +
        liuPanAPPrimePowerCorrectionMaxY X q x f := by
  unfold liuMainPanMaxY liuPanCombinedInverseLogMaxY
    liuPanAPPrimePowerCorrectionMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hcombined := Finset.le_max'
    ((range (x + 1)).image (fun y =>
      liuPanCombinedInverseLogMaxL main y X q f u v))
    (liuPanCombinedInverseLogMaxL main y X q f u v)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  have hpp := Finset.le_max'
    ((range (x + 1)).image (fun y =>
      liuPanAPPrimePowerCorrectionMaxL y X q f))
    (liuPanAPPrimePowerCorrectionMaxL y X q f)
    (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
  exact (liuMainPanMaxL_le_combinedInverseLog_add_primePower
    main y X q f u v hf0).trans (add_le_add hcombined hpp)

/-! ## Source-family analytic input -/

/-- The weighted combined inverse-log average for Liu's source at a fixed `N`. -/
noncomputable def liuMainPanCombinedInverseLogAverage
    (kappa : ℝ) (N : ℕ) (B : ℝ) (u v : ℕ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanCombinedInverseLogMaxY
        (liuLogarithmicIntegral kappa) N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v

/-- The fixed-source combined inverse-log estimate. -/
def LiuMainPanCombinedInverseLogBoundAt
    (kappa : ℝ) (N : ℕ) (A B C : ℝ) (u v : ℕ) : Prop :=
  liuMainPanCombinedInverseLogAverage kappa N B u v ≤
    C * N / Real.log N ^ A

/-- The source-family combined estimate, with `f_N` chosen inside the final
universal quantifier over `N`. -/
def LiuMainPanCombinedInverseLogSourceFamilyBound
    (kappa : ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N →
      LiuMainPanCombinedInverseLogBoundAt kappa N A B C u v

/-- The source Pan average is bounded by the combined discrepancy and only the
separately controlled prime-power correction. -/
theorem liuMainPanWeightedSum_le_combinedInverseLog_add_primePower
    (kappa : ℝ) (N : ℕ) (B : ℝ) (u v : ℕ) :
    liuMainPanWeightedSum (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      liuMainPanCombinedInverseLogAverage kappa N B u v +
        liuMainPanAPPrimePowerCorrectionAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B := by
  have hf0 :
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) 0 = 0 := by
    simp only [liuWeight, ite_eq_right_iff, one_ne_zero, imp_false]
    rintro ⟨⟨p1, p2⟩, hp, hprod⟩
    have hpair := mem_liuWeightPairs.mp hp
    exact (Nat.mul_ne_zero hpair.1.ne_zero hpair.2.1.ne_zero) hprod
  unfold liuMainPanWeightedSum liuMainPanCombinedInverseLogAverage
    liuMainPanAPPrimePowerCorrectionAverage
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
          liuMainPanMaxY (liuLogarithmicIntegral kappa) N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
        ∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
            (liuPanCombinedInverseLogMaxY
                (liuLogarithmicIntegral kappa) N q N
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v +
              liuPanAPPrimePowerCorrectionMaxY N q N
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (liuMainPanMaxY_le_combinedInverseLog_add_primePower
          (liuLogarithmicIntegral kappa) N q N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v hf0)
        (panTypeI_weight_nonneg q)
    _ = (∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
            liuPanCombinedInverseLogMaxY
              (liuLogarithmicIntegral kappa) N q N
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v) +
        ∑ q ∈ range (panModulusCutoff N B + 1),
          (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
            (3 : ℝ) ^ q.primeFactors.card *
            liuPanAPPrimePowerCorrectionMaxY N q N
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
      simp only [mul_add, Finset.sum_add_distrib]

/-- Fixed-`N` `eqn-r` consumer.  The combined inverse-log estimate and the
prime-power power saving remain on their distinct scales. -/
theorem liuPaperQSourceFullDistributionMajorant_le_of_combinedInverseLog
    (kappa epsilon A B C Cpp delta K : ℝ) (N u v : ℕ)
    (hN : 8 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hcut : liuSourceDEpsilon N epsilon ≤ panModulusCutoff N B)
    (hcombined : LiuMainPanCombinedInverseLogBoundAt
      kappa N A B C u v)
    (hpp : LiuMainPanAPPrimePowerPowerSavingBoundAt N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      B Cpp delta K) :
    liuPaperQSourceFullDistributionMajorant
        (liuLogarithmicIntegral kappa) N epsilon ≤
      C * N / Real.log N ^ A +
        Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
        15 * liuLogarithmicIntegralUpperConstant kappa *
          liuSourceR1P₂ReciprocalBound *
          paperQStyleDivisorWeightLogConstant *
          (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hpan :=
    liuMainPanWeightedSum_le_combinedInverseLog_add_primePower
      kappa N B u v
  unfold LiuMainPanCombinedInverseLogBoundAt at hcombined
  unfold LiuMainPanAPPrimePowerPowerSavingBoundAt at hpp
  have hpan' :
      liuMainPanWeightedSum (liuLogarithmicIntegral kappa) N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        C * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K :=
    hpan.trans (add_le_add hcombined hpp.2)
  have hcoprime :=
    liuPaperQSourceCoprimeDistributionMajorant_le_liuMainPanAverage
      (liuLogarithmicIntegral kappa) N epsilon B (by omega) hcut
  exact (liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1
      (liuLogarithmicIntegral kappa) N epsilon (by omega) hepsilon).trans
    (add_le_add (hcoprime.trans hpan')
      (liuLogarithmicIntegral_liuPaperQSourceR1Majorant_le_log_square
        kappa N epsilon hN hepsilon))

/-! ## Source-family and little-oh consumers -/

/-- The source-family combined estimate and the proved source prime-power
endpoint give the exact `eqn-r` majorant with three distinct scales. -/
theorem eventually_liuPaperQSourceFullDistributionMajorant_le_of_combinedInverseLog
    (kappa epsilon : ℝ) (u v : ℕ) (hepsilon : 0 < epsilon)
    (hcombined : LiuMainPanCombinedInverseLogSourceFamilyBound kappa u v) :
    ∃ C : ℝ, 0 < C ∧ ∃ Cpp : ℝ, 0 < Cpp ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ N : ℕ in atTop,
        liuPaperQSourceFullDistributionMajorant
            (liuLogarithmicIntegral kappa) N epsilon ≤
          C * N / Real.log N ^ (3 : ℝ) +
            Cpp * (N : ℝ) ^ (1 - (1 / 30 : ℝ)) *
              Real.log N ^ (20 : ℝ) +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  rcases hcombined 3 (by norm_num) with ⟨C, hC, B, hB, N0, hcombinedN⟩
  rcases exists_liuMainPanAPPrimePowerPowerSavingBoundAt_source B hB with
    ⟨Cpp, hCpp, hppN⟩
  refine ⟨C, hC, Cpp, hCpp, B, hB, ?_⟩
  have hcut :=
    eventually_liuSourceDEpsilon_le_panModulusCutoff
      epsilon B hepsilon hB
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop (8 : ℕ), hcut] with
    N hN0 hN hcutN
  exact liuPaperQSourceFullDistributionMajorant_le_of_combinedInverseLog
    kappa epsilon 3 B C Cpp (1 / 30) 20 N u v
    hN hepsilon.le hcutN (hcombinedN N hN0) (hppN N hN)

/-- A cubic inverse-log bound is negligible relative to `N / log(N)^2`. -/
theorem tendsto_inverseLogCubeScale_div_mainScale (C : ℝ) :
    Tendsto (fun N : ℕ =>
      (C * N / Real.log N ^ (3 : ℝ)) /
        ((N : ℝ) / Real.log N ^ (2 : ℝ)))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa using hlog.inv_tendsto_atTop.const_mul C
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [show (3 : ℝ) = 1 + 2 by norm_num,
    Real.rpow_add hlogpos, Real.rpow_one]
  field_simp

/-- The exact Liu `eqn-r` distribution majorant is
`o(N / log(N)^2)` under the combined source-family predicate.  The proved
prime-power power saving and the established `R₁` estimate are used only at
their own scales. -/
theorem tendsto_liuPaperQSourceFullDistributionMajorant_div_mainScale_of_combinedInverseLog
    (kappa epsilon : ℝ) (u v : ℕ) (hepsilon : 0 < epsilon)
    (hcombined : LiuMainPanCombinedInverseLogSourceFamilyBound kappa u v) :
    Tendsto (fun N : ℕ =>
      liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral kappa) N epsilon /
        ((N : ℝ) / Real.log N ^ (2 : ℝ)))
      atTop (nhds 0) := by
  rcases
      eventually_liuPaperQSourceFullDistributionMajorant_le_of_combinedInverseLog
        kappa epsilon u v hepsilon hcombined with
    ⟨C, hC, Cpp, hCpp, B, hB, hbound⟩
  have hbound' :
      ∀ᶠ N : ℕ in atTop,
        liuPaperQSourceFullDistributionMajorant
            (liuLogarithmicIntegral kappa) N epsilon ≤
          C * N / Real.log N ^ (3 : ℝ) +
            Cpp * (N : ℝ) ^ (1 - (1 / 30 : ℝ)) *
              Real.log N ^ (20 : ℝ) +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (2 : ℝ) := by
    filter_upwards [hbound] with N hN
    simpa only [Real.rpow_two] using hN
  have hupper :
      Tendsto (fun N : ℕ =>
        (C * N / Real.log N ^ (3 : ℝ) +
            Cpp * (N : ℝ) ^ (1 - (1 / 30 : ℝ)) *
              Real.log N ^ (20 : ℝ) +
                15 * liuLogarithmicIntegralUpperConstant kappa *
                  liuSourceR1P₂ReciprocalBound *
                  paperQStyleDivisorWeightLogConstant *
                  (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ (2 : ℝ)) /
              ((N : ℝ) / Real.log N ^ (2 : ℝ)))
            atTop (nhds 0) := by
    have hcombinedScale := tendsto_inverseLogCubeScale_div_mainScale C
    have hrest :=
          tendsto_primePower_add_liuR1_div_mainScale Cpp
            (15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant)
            (1 / 30 : ℝ) (20 : ℝ) (by norm_num)
    convert hcombinedScale.add hrest using 1 <;> simp
    funext N
    ring
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hscale :
        0 < (N : ℝ) / Real.log N ^ (2 : ℝ) := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hlogpos : 0 < Real.log (N : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      exact div_pos hNpos (Real.rpow_pos_of_pos hlogpos 2)
    exact div_nonneg (by
      unfold liuPaperQSourceFullDistributionMajorant
      apply Finset.sum_nonneg
      intro q hq
      positivity) hscale.le
  · filter_upwards [hbound', eventually_ge_atTop (2 : ℕ)] with N hboundN hN
    have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      positivity
    exact div_le_div_of_nonneg_right hboundN hscale
  · exact hupper

/-- Consequently, every eventually admissible Selberg lambda family has its
actual signed remainder negligible on the downstream main scale. -/
theorem tendsto_abs_liuSelbergRemainder_div_mainScale_of_combinedInverseLog
    (kappa epsilon : ℝ) (u v : ℕ) (lambda : ℕ → ℕ → ℝ)
    (hepsilon : 0 < epsilon)
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hcombined : LiuMainPanCombinedInverseLogSourceFamilyBound kappa u v) :
    Tendsto (fun N : ℕ =>
      |liuSelbergRemainder
          (liuLogarithmicIntegral kappa) N epsilon (lambda N)| /
        ((N : ℝ) / Real.log N ^ (2 : ℝ)))
      atTop (nhds 0) := by
  have hmajorant :=
    tendsto_liuPaperQSourceFullDistributionMajorant_div_mainScale_of_combinedInverseLog
      kappa epsilon u v hepsilon hcombined
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      positivity
    exact div_nonneg (abs_nonneg _) hscale
  · filter_upwards [hlambda, eventually_ge_atTop (2 : ℕ)] with N hlambdaN hN
    have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      positivity
    exact div_le_div_of_nonneg_right
      (abs_liuSelbergRemainder_le_fullDistributionMajorant
        (liuLogarithmicIntegral kappa) N epsilon (lambda N)
        (by omega) hlambdaN) hscale
  · exact hmajorant

end MathlibNt.SieveTheory.LiuWeight
