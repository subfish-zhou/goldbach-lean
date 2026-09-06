import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanSignedResidualSplit
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergEvenAssembly
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve

/-!
# Liu's prime-power correction on its own power-saving scale

This module keeps the existing arbitrary-`A` signed-residual interfaces intact
and adds the source-faithful alternative needed by Liu's argument.  Type I,
Type II, and the complete signed main retain the `N / log(N)^A` scale.  The
exact AP prime-power correction is a separate input on the
`N^(1 - delta) log(N)^K` scale, and the established `R₁` term remains separate.

The estimate demanded by `LiuMainPanAPPrimePowerPowerSavingBoundAt` is proved
below for Liu's source weight, with the safe exponents `delta = 1/30` and
`K = 20`.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve

/-- The exact weighted AP prime-power correction average at the source
parameter `N`. -/
noncomputable def liuMainPanAPPrimePowerCorrectionAverage
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanAPPrimePowerCorrectionMaxY N q N f

/-- A transparent fixed-`N` power-saving input for the exact AP prime-power
correction average.  In particular, `delta` is required to be positive. -/
def LiuMainPanAPPrimePowerPowerSavingBoundAt
    (N : ℕ) (f : ℕ → ℝ) (B Cpp delta K : ℝ) : Prop :=
  0 < delta ∧
    liuMainPanAPPrimePowerCorrectionAverage N f B ≤
      Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K

/-- The four source-faithful finite inputs, with the prime-power correction
kept on its own power-saving scale. -/
def LiuMainPanPrimePowerPowerSavingInputsAt
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ)
    (A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ) : Prop :=
  LiuMainPanTypeIPieceBoundAt N f A B C1 u ∧
  LiuMainPanTypeIIPieceBoundAt N f A B C2 u v ∧
  LiuMainPanSignedMainBoundAt distMain N f A B Cmain u v ∧
  LiuMainPanAPPrimePowerPowerSavingBoundAt N f B Cpp delta K

/-- Eventual source-family packaging of the four separate finite inputs. -/
def LiuMainPanPrimePowerPowerSavingSourceFamilyInputs
    (distMain : ℝ → ℝ) (A B C1 C2 Cmain Cpp delta K : ℝ)
    (u v : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    LiuMainPanPrimePowerPowerSavingInputsAt distMain N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 Cmain Cpp delta K u v

/-- Liu's source prime-power correction satisfies a uniform finite power-saving
bound for every nonnegative logarithmic conductor exponent. -/
theorem exists_liuMainPanAPPrimePowerPowerSavingBoundAt_source
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 8 ≤ N →
      LiuMainPanAPPrimePowerPowerSavingBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
        B C (1 / 30 : ℝ) (20 : ℝ) := by
  obtain ⟨Cd, hCd, hdensity⟩ :=
    liuMainPanAPPrimePowerCorrectionAverage_le_rpow_polylog_add_characterNoncoprime
  obtain ⟨Cr, hCr, hresidual⟩ :=
    liuMainPanPrimePowerCharacterNoncoprimeResidual_le_rpow_polylog
  let C : ℝ := 64 * Cd + Cr
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  unfold LiuMainPanAPPrimePowerPowerSavingBoundAt
  refine ⟨by norm_num, ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
  have hL : (1 : ℝ) ≤ Real.log N := by
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
  have hlogQ :
      Real.log ((panModulusCutoff N B : ℝ) + 2) ≤ 2 * Real.log N := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      liuPanPrimePower_cutoff_log_add_two_le_two_mul_log N B (by omega) hB
  have hlogQ0 :
      0 ≤ Real.log ((panModulusCutoff N B : ℝ) + 2) :=
    Real.log_nonneg (by
      have : (0 : ℝ) ≤ panModulusCutoff N B := by positivity
      linarith)
  have hpowDensity :
      (N : ℝ) ^ (107 / 120 : ℝ) ≤ (N : ℝ) ^ (29 / 30 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hpowResidual :
      (N : ℝ) ^ (227 / 240 : ℝ) ≤ (N : ℝ) ^ (29 / 30 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
  have hlogPower :
      Real.log N ^ (6 : ℝ) ≤ Real.log N ^ (20 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hdensity' :
      Cd * (N : ℝ) ^ (107 / 120 : ℝ) *
          Real.log ((panModulusCutoff N B : ℝ) + 2) ^ (6 : ℝ) ≤
        (64 * Cd) * (N : ℝ) ^ (29 / 30 : ℝ) *
          Real.log N ^ (20 : ℝ) := by
    calc
      Cd * (N : ℝ) ^ (107 / 120 : ℝ) *
          Real.log ((panModulusCutoff N B : ℝ) + 2) ^ (6 : ℝ) ≤
          Cd * (N : ℝ) ^ (107 / 120 : ℝ) *
            (2 * Real.log N) ^ (6 : ℝ) := by
        gcongr
      _ = (64 * Cd) * (N : ℝ) ^ (107 / 120 : ℝ) *
          Real.log N ^ (6 : ℝ) := by
        rw [Real.rpow_ofNat, Real.rpow_ofNat]
        ring
      _ ≤ (64 * Cd) * (N : ℝ) ^ (29 / 30 : ℝ) *
          Real.log N ^ (20 : ℝ) := by
        gcongr
  have hresidual' :
      liuMainPanPrimePowerCharacterNoncoprimeResidual N B ≤
        Cr * (N : ℝ) ^ (29 / 30 : ℝ) * Real.log N ^ (20 : ℝ) :=
    (hresidual N B hN hB).trans (by
      gcongr)
  change
    (∑ q ∈ range (panModulusCutoff N B + 1),
      liuPanPrimePowerModulusWeight q *
        liuPanAPPrimePowerCorrectionMaxY N q N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
      C * (N : ℝ) ^ (1 - (1 / 30 : ℝ)) * Real.log N ^ (20 : ℝ)
  calc
    _ ≤ Cd * (N : ℝ) ^ (107 / 120 : ℝ) *
          Real.log ((panModulusCutoff N B : ℝ) + 2) ^ (6 : ℝ) +
        liuMainPanPrimePowerCharacterNoncoprimeResidual N B :=
      hdensity N B hN
    _ ≤ (64 * Cd) * (N : ℝ) ^ (29 / 30 : ℝ) *
          Real.log N ^ (20 : ℝ) +
        Cr * (N : ℝ) ^ (29 / 30 : ℝ) * Real.log N ^ (20 : ℝ) :=
      add_le_add hdensity' hresidual'
    _ = C * (N : ℝ) ^ (1 - (1 / 30 : ℝ)) *
          Real.log N ^ (20 : ℝ) := by
      dsimp [C]
      norm_num
      ring

/-- Eventual source-family form of the prime-power power saving. -/
theorem eventually_liuMainPanAPPrimePowerPowerSavingBoundAt_source
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      LiuMainPanAPPrimePowerPowerSavingBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
        B C (1 / 30 : ℝ) (20 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_liuMainPanAPPrimePowerPowerSavingBoundAt_source B hB
  exact ⟨C, hC, (eventually_atTop.2 ⟨8, hbound⟩)⟩

/-- The coprime source majorant is bounded by the raw fixed-`N` Pan average.
This is the scale-neutral form of the existing structural consumption bridge. -/
theorem liuPaperQSourceCoprimeDistributionMajorant_le_liuMainPanAverage
    (main : ℝ → ℝ) (N : ℕ) (epsilon B : ℝ) (hN : 1 ≤ N)
    (hcut : liuSourceDEpsilon N epsilon ≤ panModulusCutoff N B) :
    liuPaperQSourceCoprimeDistributionMajorant main N epsilon ≤
      ∑ q ∈ range (panModulusCutoff N B + 1),
        (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
          (3 : ℝ) ^ q.primeFactors.card *
          liuMainPanMaxY main N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  let M := ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuMainPanMaxY main N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hpan : LiuMainPanMeanValueAt main N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      0 B (M / N) := by
    unfold LiuMainPanMeanValueAt
    change M ≤ M / (N : ℝ) * N / Real.log N ^ (0 : ℝ)
    rw [Real.rpow_zero, div_one]
    field_simp
    exact le_rfl
  have h := liuPaperQCoprimeRBound_of_liuMainPanMeanValueAt
    main N epsilon 0 B (M / N) hcut hpan
  unfold LiuPaperQCoprimeRBound at h
  change liuPaperQSourceCoprimeDistributionMajorant main N epsilon ≤ M
  rw [Real.rpow_zero, div_one] at h
  field_simp at h
  exact h

/-- The four finite inputs bound the raw Pan average, with the prime-power term
displayed separately and without absorption. -/
theorem liuMainPanAverage_le_of_primePowerPowerSavingInputsAt
    (distMain : ℝ → ℝ) (N : ℕ) (f : ℕ → ℝ)
    (A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ)
    (hf0 : f 0 = 0)
    (hsource : LiuMainPanPrimePowerPowerSavingInputsAt distMain N f
      A B C1 C2 Cmain Cpp delta K u v) :
    (∑ q ∈ range (panModulusCutoff N B + 1),
      (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
        (3 : ℝ) ^ q.primeFactors.card *
        liuMainPanMaxY distMain N q N f) ≤
      (C1 + C2 + Cmain) * N / Real.log N ^ A +
        Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K := by
  rcases hsource with ⟨hI, hII, hmain, hpp⟩
  unfold LiuMainPanTypeIPieceBoundAt at hI
  unfold LiuMainPanTypeIIPieceBoundAt at hII
  unfold LiuMainPanSignedMainBoundAt at hmain
  unfold LiuMainPanAPPrimePowerPowerSavingBoundAt at hpp
  unfold liuMainPanAPPrimePowerCorrectionAverage at hpp
  let w : ℕ → ℝ := fun q =>
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card
  let pI : ℕ → ℝ := fun q =>
    panPieceMaxY N q N f
      (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let pII : ℕ → ℝ := fun q =>
    panPieceMaxY N q N f
      (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let pMain : ℕ → ℝ := fun q =>
    liuPanSignedMainMaxY distMain N q N f u v
  let pPP : ℕ → ℝ := fun q =>
    liuPanAPPrimePowerCorrectionMaxY N q N f
  have hw : ∀ q, 0 ≤ w q := by
    intro q
    exact panTypeI_weight_nonneg q
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
        w q * liuMainPanMaxY distMain N q N f) ≤
        ∑ q ∈ range (panModulusCutoff N B + 1),
          w q * (pI q + pII q + pMain q + pPP q) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (hw q)
      calc
        liuMainPanMaxY distMain N q N f ≤
            pI q + pII q +
              liuPanSignedResidualMaxY distMain N q N f u v := by
          simpa [pI, pII] using
            liuMainPanMaxY_le_sourceFaithfulSigned
              distMain N q N f u v hf0
        _ ≤ pI q + pII q + (pMain q + pPP q) := by
          simpa [pMain, pPP, add_assoc, add_comm, add_left_comm] using
            add_le_add_left
              (liuPanSignedResidualMaxY_le_split
                distMain N q N f u v) (pI q + pII q)
        _ = pI q + pII q + pMain q + pPP q := by ring
    _ = (∑ q ∈ range (panModulusCutoff N B + 1), w q * pI q) +
          (∑ q ∈ range (panModulusCutoff N B + 1), w q * pII q) +
          (∑ q ∈ range (panModulusCutoff N B + 1), w q * pMain q) +
          ∑ q ∈ range (panModulusCutoff N B + 1), w q * pPP q := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ C1 * N / Real.log N ^ A +
          C2 * N / Real.log N ^ A +
          Cmain * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K := by
      exact add_le_add
        (add_le_add
          (add_le_add (by simpa [w, pI] using hI)
            (by simpa [w, pII] using hII))
          (by simpa [w, pMain] using hmain))
        (by simpa [w, pPP] using hpp.2)
    _ = (C1 + C2 + Cmain) * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K := by ring

/-- Fixed-`N` assembly into Liu's full source distribution majorant.  The
arbitrary-`A` terms, prime-power term, and `R₁` term remain separate. -/
theorem liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputsAt
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (N u v : ℕ)
    (hN : 8 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hcut : liuSourceDEpsilon N epsilon ≤ panModulusCutoff N B)
    (hsource : LiuMainPanPrimePowerPowerSavingInputsAt
      (liuLogarithmicIntegral kappa) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 Cmain Cpp delta K u v) :
    liuPaperQSourceFullDistributionMajorant
        (liuLogarithmicIntegral kappa) N epsilon ≤
      (C1 + C2 + Cmain) * N / Real.log N ^ A +
        Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
        15 * liuLogarithmicIntegralUpperConstant kappa *
          liuSourceR1P₂ReciprocalBound *
          paperQStyleDivisorWeightLogConstant *
          (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hf0 :
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) 0 = 0 := by
    simp only [liuWeight, ite_eq_right_iff, one_ne_zero, imp_false]
    rintro ⟨⟨p1, p2⟩, hp, hprod⟩
    have hpair := mem_liuWeightPairs.mp hp
    exact (Nat.mul_ne_zero hpair.1.ne_zero hpair.2.1.ne_zero) hprod
  have haverage :=
    liuMainPanAverage_le_of_primePowerPowerSavingInputsAt
      (liuLogarithmicIntegral kappa) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 Cmain Cpp delta K u v hf0 hsource
  have hcoprime :=
    liuPaperQSourceCoprimeDistributionMajorant_le_liuMainPanAverage
      (liuLogarithmicIntegral kappa) N epsilon B (by omega) hcut
  exact (liuPaperQSourceFullDistributionMajorant_le_coprime_add_r1
      (liuLogarithmicIntegral kappa) N epsilon (by omega) hepsilon).trans
    (add_le_add (hcoprime.trans haverage)
      (liuLogarithmicIntegral_liuPaperQSourceR1Majorant_le_log_square
        kappa N epsilon hN hepsilon))

/-- Eventual assembly into the full source distribution majorant. -/
theorem eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputs
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ)
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hsource : LiuMainPanPrimePowerPowerSavingSourceFamilyInputs
      (liuLogarithmicIntegral kappa)
      A B C1 C2 Cmain Cpp delta K u v) :
    ∀ᶠ N : ℕ in atTop,
      liuPaperQSourceFullDistributionMajorant
          (liuLogarithmicIntegral kappa) N epsilon ≤
        (C1 + C2 + Cmain) * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
          15 * liuLogarithmicIntegralUpperConstant kappa *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hcut :=
    eventually_liuSourceDEpsilon_le_panModulusCutoff
      epsilon B hepsilon hB
  filter_upwards [hsource, hcut, eventually_ge_atTop (8 : ℕ)] with
    N hsourceN hcutN hN
  exact
    liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputsAt
      kappa epsilon A B C1 C2 Cmain Cpp delta K N u v
      hN hepsilon.le hcutN hsourceN

/-- Fixed-`N` assembly for the actual signed lambda-pair Selberg remainder. -/
theorem abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputsAt
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (N u v : ℕ)
    (lambda : ℕ → ℝ) (hN : 8 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hcut : liuSourceDEpsilon N epsilon ≤ panModulusCutoff N B)
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hsource : LiuMainPanPrimePowerPowerSavingInputsAt
      (liuLogarithmicIntegral kappa) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 Cmain Cpp delta K u v) :
    |liuSelbergRemainder
        (liuLogarithmicIntegral kappa) N epsilon lambda| ≤
      (C1 + C2 + Cmain) * N / Real.log N ^ A +
        Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
        15 * liuLogarithmicIntegralUpperConstant kappa *
          liuSourceR1P₂ReciprocalBound *
          paperQStyleDivisorWeightLogConstant *
          (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 :=
  (abs_liuSelbergRemainder_le_fullDistributionMajorant
      (liuLogarithmicIntegral kappa) N epsilon lambda (by omega) hlambda).trans
    (liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputsAt
      kappa epsilon A B C1 C2 Cmain Cpp delta K N u v
      hN hepsilon hcut hsource)

/-- Eventual assembly for the actual signed lambda-pair Selberg remainder. -/
theorem eventually_abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputs
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ)
    (lambda : ℕ → ℕ → ℝ) (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hsource : LiuMainPanPrimePowerPowerSavingSourceFamilyInputs
      (liuLogarithmicIntegral kappa)
      A B C1 C2 Cmain Cpp delta K u v) :
    ∀ᶠ N : ℕ in atTop,
      |liuSelbergRemainder
          (liuLogarithmicIntegral kappa) N epsilon (lambda N)| ≤
        (C1 + C2 + Cmain) * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
          15 * liuLogarithmicIntegralUpperConstant kappa *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hmajorant :=
    eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputs
      kappa epsilon A B C1 C2 Cmain Cpp delta K u v
      hepsilon hB hsource
  filter_upwards [hlambda, hmajorant, eventually_ge_atTop (1 : ℕ)] with
    N hlambdaN hmajorantN hN
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant
      (liuLogarithmicIntegral kappa) N epsilon (lambda N) hN hlambdaN).trans
    hmajorantN

/-- Fixed-`N` switched-count assembly, conditional on the displayed numerical
main-term input. -/
theorem liuSelbergSwitchedCount_le_of_mainTermUpperBound_primePowerPowerSavingInputsAt
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (N u v : ℕ)
    (lambda : ℕ → ℝ) (hN : 8 ≤ N) (hepsilon : 0 ≤ epsilon)
    (hcut : liuSourceDEpsilon N epsilon ≤ panModulusCutoff N B)
    (hmainTerm : LiuSelbergMainTermUpperBound
      kappa N epsilon lambda)
    (hlambda : LiuSelbergLambdaAdmissible N epsilon lambda)
    (hsource : LiuMainPanPrimePowerPowerSavingInputsAt
      (liuLogarithmicIntegral kappa) N
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      A B C1 C2 Cmain Cpp delta K u v) :
    liuSelbergSwitchedCount N epsilon lambda ≤
      3.94033 *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log N ^ 2 +
        ((C1 + C2 + Cmain) * N / Real.log N ^ A +
          Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
          15 * liuLogarithmicIntegralUpperConstant kappa *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  rw [liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainTerm
    ((le_abs_self _).trans
      (abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputsAt
        kappa epsilon A B C1 C2 Cmain Cpp delta K N u v lambda
        hN hepsilon hcut hlambda hsource))

/-- Eventual switched-count assembly for an arbitrary admissible lambda family. -/
theorem eventually_liuSelbergSwitchedCount_le_of_mainTermUpperBound_primePowerPowerSavingInputs
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ)
    (lambda : ℕ → ℕ → ℝ) (hepsilon : 0 < epsilon) (hB : 0 ≤ B)
    (hmainTerm : ∀ᶠ N : ℕ in atTop,
      LiuSelbergMainTermUpperBound kappa N epsilon (lambda N))
    (hlambda : ∀ᶠ N : ℕ in atTop,
      LiuSelbergLambdaAdmissible N epsilon (lambda N))
    (hsource : LiuMainPanPrimePowerPowerSavingSourceFamilyInputs
      (liuLogarithmicIntegral kappa)
      A B C1 C2 Cmain Cpp delta K u v) :
    ∀ᶠ N : ℕ in atTop,
      liuSelbergSwitchedCount N epsilon (lambda N) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + Cmain) * N / Real.log N ^ A +
            Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hR :=
    eventually_abs_liuSelbergRemainder_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputs
      kappa epsilon A B C1 C2 Cmain Cpp delta K u v lambda
      hepsilon hB hlambda hsource
  filter_upwards [hmainTerm, hR] with N hmainN hRN
  rw [liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainN ((le_abs_self _).trans hRN)

/-- The optimal even-filter square count with all three error scales displayed. -/
theorem eventually_liuSelbergOptimalSquareCount_le_even_of_primePowerPowerSavingInputs
    (kappa epsilon A B C1 C2 Cmain Cpp delta K : ℝ) (u v : ℕ)
    (hkappa : 0 ≤ kappa) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hB : 0 ≤ B)
    (hsource : LiuMainPanPrimePowerPowerSavingSourceFamilyInputs
      (liuLogarithmicIntegral kappa)
      A B C1 C2 Cmain Cpp delta K u v) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      liuSelbergSquareCount N epsilon
          (liuSelbergOptimalLambda N epsilon) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + Cmain) * N / Real.log N ^ A +
            Cpp * (N : ℝ) ^ (1 - delta) * Real.log N ^ K +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hmain :=
    eventually_liuSelbergOptimalLambda_mainTermUpperBound_even
      kappa hkappa hepsilon hepsilon_le
  have hlambda :=
    eventually_liuSelbergOptimalLambda_admissible_even hepsilon_le
  have hmajorant :=
    eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_primePowerPowerSavingInputs
      kappa epsilon A B C1 C2 Cmain Cpp delta K u v
      hepsilon hB hsource
  filter_upwards [hmain, hlambda, hmajorant.filter_mono inf_le_left,
      (eventually_ge_atTop (1 : ℕ)).filter_mono inf_le_left] with
    N hmainN hlambdaN hmajorantN hN
  rw [liuSelbergSquareCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainN
    ((le_abs_self _).trans
      ((abs_liuSelbergRemainder_le_fullDistributionMajorant
        (liuLogarithmicIntegral kappa) N epsilon
          (liuSelbergOptimalLambda N epsilon) hN hlambdaN).trans
        hmajorantN))

/-! ## Symbolic asymptotic consumers -/

/-- For every fixed positive `delta` and real logarithmic exponent `K`, the
prime-power scale is negligible relative to `N / log(N)^2`. -/
theorem tendsto_primePowerPowerSavingScale_div_mainScale
    (delta K : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ (1 - delta) * Real.log (N : ℝ) ^ K) /
        ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)))
      atTop (nhds 0) := by
  have hcore :
      Tendsto (fun N : ℕ =>
        Real.log (N : ℝ) ^ (K + 2) / (N : ℝ) ^ delta)
        atTop (nhds 0) := by
    exact
      ((isLittleO_log_rpow_rpow_atTop (K + 2) hdelta).tendsto_div_nhds_zero).comp
        tendsto_natCast_atTop_atTop
  apply hcore.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  rw [Real.rpow_sub hNpos, Real.rpow_one, Real.rpow_add hlogpos]
  field_simp

/-- The unchanged `N^(9/10) log(N)^2` scale from `R₁` is also negligible
relative to `N / log(N)^2`; this is kept as a separate triangular consumer. -/
theorem tendsto_liuR1Scale_div_mainScale :
    Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ (9 / 10 : ℝ) * Real.log (N : ℝ) ^ (2 : ℝ)) /
        ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)))
      atTop (nhds 0) := by
  simpa [show (9 / 10 : ℝ) = 1 - 1 / 10 by norm_num] using
    tendsto_primePowerPowerSavingScale_div_mainScale
      (1 / 10 : ℝ) (2 : ℝ) (by norm_num)

/-- Constant multiples of the separate prime-power and `R₁` scales remain
negligible when combined only after their individual estimates. -/
theorem tendsto_primePower_add_liuR1_div_mainScale
    (Cpp CR1 delta K : ℝ) (hdelta : 0 < delta) :
    Tendsto (fun N : ℕ =>
      (Cpp * ((N : ℝ) ^ (1 - delta) * Real.log (N : ℝ) ^ K) +
          CR1 * ((N : ℝ) ^ (9 / 10 : ℝ) *
            Real.log (N : ℝ) ^ (2 : ℝ))) /
        ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ)))
      atTop (nhds 0) := by
  have hpp :=
    (tendsto_primePowerPowerSavingScale_div_mainScale delta K hdelta).const_mul Cpp
  have hR1 := tendsto_liuR1Scale_div_mainScale.const_mul CR1
  simpa only [add_div, mul_div_assoc, mul_zero, zero_add] using hpp.add hR1

end MathlibNt.SieveTheory.LiuWeight
