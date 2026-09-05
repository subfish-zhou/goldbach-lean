import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergMainTermInstantiation

/-!
# Liu's Selberg assembly on the even filter

This module instantiates the source-facing Selberg argument with the explicit
optimizer `liuSelbergOptimalLambda N epsilon`.  Evenness is carried by the
filter rather than requested for all natural numbers.  It retains the
componentwise source-input route and also supplies the canonical aggregate
Pan--Wang--Ding route.
-/

open Filter

namespace MathlibNt.SieveTheory.LiuWeight

/-- A fixed epsilon endpoint below both the denominator margin used for `M₁`
and `1 / 2`. -/
noncomputable def liuEvenAssemblyEpsilon0 : ℝ := 1 / 10000000000

lemma liuEvenAssemblyEpsilon0_pos : 0 < liuEvenAssemblyEpsilon0 := by
  norm_num [liuEvenAssemblyEpsilon0]

lemma liuEvenAssemblyEpsilon0_lt_m1_margin :
    liuEvenAssemblyEpsilon0 <
      liuM1Delta / (2 * (8 + liuM1Delta)) := by
  norm_num [liuEvenAssemblyEpsilon0, liuM1Delta]

lemma liuEvenAssemblyEpsilon0_lt_half :
    liuEvenAssemblyEpsilon0 < (1 / 2 : ℝ) := by
  norm_num [liuEvenAssemblyEpsilon0]

/-- For every epsilon in the fixed assembly interval, the source cutoff
eventually contains `1`. -/
theorem eventually_one_le_paperQSourceCutoff_of_le_evenAssemblyEpsilon0
    {epsilon : ℝ} (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ paperQSourceCutoff N epsilon := by
  have hbeta : 0 < 1 / 4 - epsilon / 2 := by
    nlinarith [liuEvenAssemblyEpsilon0_lt_half]
  have hpow :
      ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 - epsilon / 2) :=
    ((tendsto_rpow_atTop hbeta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hpow] with N hN
  unfold paperQSourceCutoff
  simpa using Nat.floor_mono hN

/-- The explicit optimal coefficients are eventually admissible along the even
natural numbers. -/
theorem eventually_liuSelbergOptimalLambda_admissible_even
    {epsilon : ℝ} (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      LiuSelbergLambdaAdmissible N epsilon
        (liuSelbergOptimalLambda N epsilon) := by
  have hcutoff :=
    eventually_one_le_paperQSourceCutoff_of_le_evenAssemblyEpsilon0 hepsilon_le
  rw [eventually_inf_principal]
  filter_upwards [hcutoff] with N hR
  intro hNeven
  exact ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
    fun d => abs_liuSelbergOptimalLambda_le_one hNeven hR⟩

/-- The explicit optimal coefficients satisfy Liu's printed `M₁` bound
eventually along the even natural numbers. -/
theorem eventually_liuSelbergOptimalLambda_mainTermUpperBound_even
    (kappa : ℝ) (hκ : 0 ≤ kappa) {epsilon : ℝ}
    (_hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      LiuSelbergMainTermUpperBound kappa N epsilon
        (liuSelbergOptimalLambda N epsilon) := by
  have hmargin :
      epsilon < liuM1Delta / (2 * (8 + liuM1Delta)) :=
    hepsilon_le.trans_lt liuEvenAssemblyEpsilon0_lt_m1_margin
  have hden :=
    liuSelbergDenominatorLowerBound_of_lt_margin liuM1Delta_pos hmargin
  have hcutoff :=
    eventually_one_le_paperQSourceCutoff_of_le_evenAssemblyEpsilon0 hepsilon_le
  obtain ⟨N₀, hweight⟩ :=
    eventually_liuGenuineLiWeightMainSumBound kappa hκ liuM1Eta liuM1Eta_pos
  rw [eventually_inf_principal]
  filter_upwards [hden, hcutoff, eventually_ge_atTop N₀,
      eventually_ge_atTop (8 : ℕ)] with N hdenN hR hN₀ hN8
  intro hNeven
  have hadmissible :
      LiuSelbergLambdaAdmissible N epsilon
        (liuSelbergOptimalLambda N epsilon) :=
    ⟨fun _ hd => liuSelbergOptimalLambda_support hd,
      fun d => abs_liuSelbergOptimalLambda_le_one hNeven hR⟩
  have hcoefficient :
      LiuSelbergCoefficientFactorBound liuM1Delta N epsilon
        (liuSelbergOptimalLambda N epsilon) := by
    unfold LiuSelbergCoefficientFactorBound
    rw [liuSelbergCoefficientFactor_optimalLambda hNeven hR]
    exact one_div_liuSelbergDenominator_le
      (by norm_num [liuM1Delta]) (by omega) hNeven hR
        (hdenN (by omega) hNeven hR)
  exact LiuSelbergMainTermUpperBound.of_componentBounds
    kappa liuM1Delta liuM1Eta (0.49254 + liuM1Eta) N epsilon
      (liuSelbergOptimalLambda N epsilon) hNeven hadmissible
      (by norm_num [liuM1Delta])
      (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N).le
      (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
      (le_refl _) liuM1DeltaEta_margin hcoefficient (hweight N hN₀)

/-- The three Pan source-family bounds give the explicit Selberg remainder
bound for the optimal coefficients along the even filter. -/
theorem eventually_abs_liuSelbergOptimalRemainder_le_even_of_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hB : 0 ≤ B)
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      |liuSelbergRemainder (liuLogarithmicIntegral kappa) N epsilon
          (liuSelbergOptimalLambda N epsilon)| ≤
        (C1 + C2 + C3) * N / Real.log N ^ A +
          15 * liuLogarithmicIntegralUpperConstant kappa *
            liuSourceR1P₂ReciprocalBound *
            paperQStyleDivisorWeightLogConstant *
            (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2 := by
  have hsource : LiuMainPanSourceFamilyInputs
      (liuLogarithmicIntegral kappa) A B C1 C2 C3 u v := by
    filter_upwards [hI, hII, hresidual] with N hIN hIIN hresidualN
    exact ⟨hIN, hIIN, hresidualN⟩
  have hmajorant :=
    eventually_liuPaperQSourceFullDistributionMajorant_liuLogarithmicIntegral_le_of_sourceFaithfulSignedInputs
      kappa epsilon A B C1 C2 C3 u v hepsilon hB hsource
  have hlambda :=
    eventually_liuSelbergOptimalLambda_admissible_even hepsilon_le
  filter_upwards [hlambda, hmajorant.filter_mono inf_le_left,
      (eventually_ge_atTop (1 : ℕ)).filter_mono inf_le_left] with
    N hlambdaN hmajorantN hN
  exact (abs_liuSelbergRemainder_le_fullDistributionMajorant
    (liuLogarithmicIntegral kappa) N epsilon
      (liuSelbergOptimalLambda N epsilon) hN hlambdaN).trans hmajorantN

/-- Liu's switched Selberg count has the printed main term plus the explicit
remainder bound along the even filter. -/
theorem eventually_liuSelbergOptimalSwitchedCount_le_even_of_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (hκ : 0 ≤ kappa) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hB : 0 ≤ B)
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      liuSelbergSwitchedCount N epsilon
          (liuSelbergOptimalLambda N epsilon) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + C3) * N / Real.log N ^ A +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hmain :=
    eventually_liuSelbergOptimalLambda_mainTermUpperBound_even
      kappa hκ hepsilon hepsilon_le
  have hR :=
    eventually_abs_liuSelbergOptimalRemainder_le_even_of_sourceInputs
      kappa epsilon A B C1 C2 C3 u v hepsilon hepsilon_le hB
        hI hII hresidual
  filter_upwards [hmain, hR] with N hmainN hRN
  rw [liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainN (le_trans (le_abs_self _) hRN)

/-- Liu's original squared-divisor Selberg count has the same bound along the
even filter. -/
theorem eventually_liuSelbergOptimalSquareCount_le_even_of_sourceInputs
    (kappa epsilon A B C1 C2 C3 : ℝ) (u v : ℕ)
    (hκ : 0 ≤ kappa) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hB : 0 ≤ B)
    (hI : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C1 u)
    (hII : ∀ᶠ N : ℕ in atTop,
      LiuMainPanTypeIIPieceBoundAt N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C2 u v)
    (hresidual : ∀ᶠ N : ℕ in atTop,
      LiuMainPanSignedResidualBoundAt (liuLogarithmicIntegral kappa) N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C3 u v) :
    ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
      liuSelbergSquareCount N epsilon
          (liuSelbergOptimalLambda N epsilon) ≤
        3.94033 *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
            (N : ℝ) / Real.log N ^ 2 +
          ((C1 + C2 + C3) * N / Real.log N ^ A +
            15 * liuLogarithmicIntegralUpperConstant kappa *
              liuSourceR1P₂ReciprocalBound *
              paperQStyleDivisorWeightLogConstant *
              (N : ℝ) ^ (9 / 10 : ℝ) * Real.log N ^ 2) := by
  have hM :=
    eventually_liuSelbergOptimalSwitchedCount_le_even_of_sourceInputs
      kappa epsilon A B C1 C2 C3 u v hκ hepsilon hepsilon_le hB
        hI hII hresidual
  filter_upwards [hM] with N hMN
  rw [liuSelbergSquareCount_eq_switchedCount]
  exact hMN

/-- The canonical coprime consumer interface gives arbitrary logarithmic
saving for the actual optimal Selberg remainder along the even filter. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_abs_liuSelbergOptimalRemainder_le_even
    (hPan : LiuPanCanonicalCoprimeTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon
            (liuSelbergOptimalLambda N epsilon)| ≤
          C * N / Real.log N ^ A := by
  exact hPan.eventually_abs_liuSelbergRemainder_le
    (atTop ⊓ 𝓟 {N : ℕ | Even N}) inf_le_left epsilon A
    (fun N => liuSelbergOptimalLambda N epsilon) hepsilon hA
    (eventually_liuSelbergOptimalLambda_admissible_even hepsilon_le)

/-- The canonical coprime consumer interface and the proved optimal main-term
estimate bound Liu's switched Selberg count without componentwise Pan inputs. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_liuSelbergOptimalSwitchedCount_le_even
    (hPan : LiuPanCanonicalCoprimeTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSwitchedCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A := by
  rcases hPan.eventually_abs_liuSelbergOptimalRemainder_le_even
      epsilon A hepsilon hepsilon_le hA with ⟨C, hC, hR⟩
  have hmain :=
    eventually_liuSelbergOptimalLambda_mainTermUpperBound_even
      2 (by norm_num) hepsilon hepsilon_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, hR] with N hmainN hRN
  rw [liuSelbergSwitchedCount_eq_logarithmicIntegralMainTerm_add_remainder]
  exact add_le_add hmainN (le_trans (le_abs_self _) hRN)

/-- The same canonical consumer bound holds for Liu's original squared-divisor
Selberg count by the exact square expansion. -/
theorem LiuPanCanonicalCoprimeTheorem.eventually_liuSelbergOptimalSquareCount_le_even
    (hPan : LiuPanCanonicalCoprimeTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSquareCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A := by
  rcases hPan.eventually_liuSelbergOptimalSwitchedCount_le_even
      epsilon A hepsilon hepsilon_le hA with ⟨C, hC, hM⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hM] with N hMN
  rw [liuSelbergSquareCount_eq_switchedCount]
  exact hMN

/-- Backward-compatible optimal-remainder wrapper for the stronger canonical
Pan--Wang--Ding endpoint contract. -/
theorem LiuPanWangDingTheorem.eventually_abs_liuSelbergOptimalRemainder_le_even
    (hPan : LiuPanWangDingTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon
            (liuSelbergOptimalLambda N epsilon)| ≤
          C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_abs_liuSelbergOptimalRemainder_le_even
    epsilon A hepsilon hepsilon_le hA

/-- Backward-compatible switched-count wrapper for the stronger canonical
Pan--Wang--Ding endpoint contract. -/
theorem LiuPanWangDingTheorem.eventually_liuSelbergOptimalSwitchedCount_le_even
    (hPan : LiuPanWangDingTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSwitchedCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_liuSelbergOptimalSwitchedCount_le_even
    epsilon A hepsilon hepsilon_le hA

/-- Backward-compatible square-count wrapper for the stronger canonical
Pan--Wang--Ding endpoint contract. -/
theorem LiuPanWangDingTheorem.eventually_liuSelbergOptimalSquareCount_le_even
    (hPan : LiuPanWangDingTheorem) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSquareCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_liuSelbergOptimalSquareCount_le_even
    epsilon A hepsilon hepsilon_le hA

/-- Source-faithful optimal-remainder wrapper from literal Corollary `(2.30)`. -/
theorem LiuPanWangDingCorollary230.eventually_abs_liuSelbergOptimalRemainder_le_even
    (hPan : LiuPanWangDingCorollary230) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        |liuSelbergRemainder (liuLogarithmicIntegral 2) N epsilon
            (liuSelbergOptimalLambda N epsilon)| ≤
          C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_abs_liuSelbergOptimalRemainder_le_even
    epsilon A hepsilon hepsilon_le hA

/-- Source-faithful switched-count wrapper from literal Corollary `(2.30)`. -/
theorem LiuPanWangDingCorollary230.eventually_liuSelbergOptimalSwitchedCount_le_even
    (hPan : LiuPanWangDingCorollary230) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSwitchedCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_liuSelbergOptimalSwitchedCount_le_even
    epsilon A hepsilon hepsilon_le hA

/-- Source-faithful square-count wrapper from literal Corollary `(2.30)`. -/
theorem LiuPanWangDingCorollary230.eventually_liuSelbergOptimalSquareCount_le_even
    (hPan : LiuPanWangDingCorollary230) (epsilon A : ℝ)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ liuEvenAssemblyEpsilon0) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop ⊓ 𝓟 {N : ℕ | Even N},
        liuSelbergSquareCount N epsilon
            (liuSelbergOptimalLambda N epsilon) ≤
          3.94033 *
              MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N *
              (N : ℝ) / Real.log N ^ 2 +
            C * N / Real.log N ^ A :=
  hPan.to_canonicalCoprimeTheorem.eventually_liuSelbergOptimalSquareCount_le_even
    epsilon A hepsilon hepsilon_le hA

end MathlibNt.SieveTheory.LiuWeight
