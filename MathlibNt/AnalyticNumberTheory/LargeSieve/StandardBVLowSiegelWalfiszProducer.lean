

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSufficientAssembly

/-!
 # Producer for the low-conductor Standard-BV source

This module reduces the low source to two genuinely one-dimensional inputs:
the already isolated modulus-one PNT/partial-summation contract, and a
pointwise primitive nonprincipal `ψ(N,χ)` Siegel--Walfisz estimate.  All finite
character multiplicities, conductor fibres and logarithmic losses are paid
here.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The exact remaining low-conductor analytic theorem.  It is pointwise in a
primitive nonprincipal character and contains neither an AP average nor a BV
conclusion.  (For `d ≥ 2`, primitivity in fact forces nonprincipality; the
explicit hypothesis records the intended mathematical lane.) -/
def NonprincipalPrimitivePsiSiegelWalfiszSource : Prop :=
  ∀ C D : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
      ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
        ∀ ψ : PrimitiveCharacter d, ψ.1 ≠ 1 →
          primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D

lemma primitiveCharacter_ne_one_of_two_le
    {d : ℕ} (hd : 2 ≤ d) (ψ : PrimitiveCharacter d) : ψ.1 ≠ 1 := by
  letI : NeZero d := ⟨by omega⟩
  intro h
  have hc : ψ.1.conductor = 1 := by rw [h, DirichletCharacter.conductor_one]
  rw [primitive_conductor ψ] at hc
  omega

/-- The explicitly nonprincipal formulation is equivalent to the older
all-primitive pointwise formulation, since conductors in the low set start at
`2`. -/
theorem primitivePrefixSiegelWalfiszSource_of_nonprincipal
    (h : NonprincipalPrimitivePsiSiegelWalfiszSource) :
    PrimitivePrefixSiegelWalfiszSource := by
  intro C D
  obtain ⟨K, hK, hN⟩ := h C D
  refine ⟨K, hK, ?_⟩
  filter_upwards [hN] with N hSN
  intro hN2 d hd ψ
  exact hSN hN2 d hd ψ
    (primitiveCharacter_ne_one_of_two_le (Finset.mem_Icc.mp hd).1 ψ)

/-- The complete finite arithmetic mass in the low conductor lane is at most
`R H(Q)^2`, where `R = floor(log(N)^C)`. -/
theorem lowConductorArithmeticMass_le_explicit (N Q C : ℕ) :
    lowConductorArithmeticMass N Q C ≤
      (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 := by
  unfold lowConductorArithmeticMass
  have hterm : ∀ d ∈ lowConductorSet N Q C,
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d) ≤
        conductorHarmonicFactor Q ^ 2 := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hφ : (0 : ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < d)
    have hcard : (Fintype.card (PrimitiveCharacter d) : ℝ) ≤ d.totient := by
      exact_mod_cast card_primitiveCharacter_le_totient d (by omega : 0 < d)
    calc
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d) ≤
          (conductorHarmonicFactor Q ^ 2 / (d.totient : ℝ)) *
            Fintype.card (PrimitiveCharacter d) := by
              gcongr
              exact directConductorWeight_le Q d
      _ ≤ conductorHarmonicFactor Q ^ 2 := by
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hφ).2 (by
          nlinarith [sq_nonneg (conductorHarmonicFactor Q)])
  calc
    (∑ d ∈ lowConductorSet N Q C,
      directConductorWeight Q d * Fintype.card (PrimitiveCharacter d)) ≤
        ∑ _d ∈ lowConductorSet N Q C, conductorHarmonicFactor Q ^ 2 :=
          Finset.sum_le_sum hterm
    _ = (lowConductorSet N Q C).card * conductorHarmonicFactor Q ^ 2 := by simp
    _ ≤ (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 := by
      gcongr
      norm_cast
      refine (Finset.card_le_card (show lowConductorSet N Q C ⊆
        Finset.Icc 1 (logConductorThreshold N C) from ?_)).trans ?_
      · intro d hd
        rcases Finset.mem_filter.mp hd with ⟨hdI, hdR⟩
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdI).1.trans' (by omega), hdR⟩
      · simp

/-- The two modulus-one terms, after summing `1/φ(q)`, cost only the proved
finite reciprocal-totient mass. -/
theorem principalGlobal_add_chebyshevToLi_le_qOne
    (N Q : ℕ) :
    discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
        chebyshevToLiPhysical N Q ≤
      conductorHarmonicFactor Q ^ 2 * globalPartialSummationSource N := by
  unfold principalGlobalPhysical chebyshevToLiPhysical globalPartialSummationSource
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum := sum_inv_totient_le_harmonic_sq Q
  have hprincipal : 0 ≤ principalLambdaPrefixMaxError N 1 := by
    unfold principalLambdaPrefixMaxError
    exact (norm_nonneg (principalLambdaMainError 0 1)).trans
      (Finset.le_max'
        ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖)) _
        (Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
  have hcheb : 0 ≤ globalChebyshevToLiSourcePrefixMaxError N := by
    unfold globalChebyshevToLiSourcePrefixMaxError
    have hsource0 : 0 ≤ globalChebyshevToLiSourceError 0 := by
      unfold globalChebyshevToLiSourceError
      exact abs_nonneg _
    exact hsource0.trans
      (Finset.le_max'
        ((Finset.range (N + 1)).image globalChebyshevToLiSourceError) _
        (Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
  have habel : 0 ≤ discreteAbelAmplifierPrefixMax N := by
    have h0 : 0 ≤ discreteAbelAmplifier 0 := by unfold discreteAbelAmplifier; positivity
    exact h0.trans (Finset.le_max' _ _ (Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
  nlinarith [mul_nonneg habel hprincipal]

private theorem panModulusCutoff_le_self_eventually (B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ) ≤ N := by
  filter_upwards [eventually_ge_atTop (8 : ℕ)] with N hN
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have h8 : (1 : ℝ) < Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact h8.le.trans (Real.strictMonoOn_log.monotoneOn
      (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (N : ℝ) ∈ Set.Ioi 0 by
        change 0 < (N : ℝ)
        exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hN))
  have hden : 1 ≤ Real.log (N : ℝ) ^ (B : ℝ) :=
    Real.one_le_rpow hlog (by positivity)
  have hsqrt : Real.sqrt (N : ℝ) ≤ N := by
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    exact (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith⟩
  unfold MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
  apply Nat.floor_le_of_le
  calc
    (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) := div_le_self (Real.rpow_nonneg (by positivity) _) hden
    _ = Real.sqrt (N : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ N := hsqrt

private theorem low_scalar_envelopes (C B : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
      lowConductorArithmeticMass N Q C ≤ 4 * Real.log N ^ (C + 2) ∧
      conductorHarmonicFactor Q ^ 2 ≤ 4 * Real.log N ^ 2 := by
  filter_upwards [panModulusCutoff_le_self_eventually B,
    eventually_ge_atTop (8 : ℕ)] with N hQN hN
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have h8 : (1 : ℝ) < Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact h8.le.trans (Real.strictMonoOn_log.monotoneOn
      (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (N : ℝ) ∈ Set.Ioi 0 by
        change 0 < (N : ℝ)
        exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hN))
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hQ : Q = 0
    · rw [hQ, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg
        (show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N))
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hQN)
  have hH : conductorHarmonicFactor Q ≤ 2 * Real.log N :=
    (conductorHarmonicFactor_le Q).trans (by linarith)
  have hH0 := conductorHarmonicFactor_nonneg Q
  have hR : (logConductorThreshold N C : ℝ) ≤ Real.log N ^ C := by
    unfold logConductorThreshold
    exact_mod_cast Nat.floor_le (pow_nonneg (by positivity) C)
  have hpow0 : 0 ≤ Real.log N ^ C := pow_nonneg (by positivity) C
  constructor
  · refine (lowConductorArithmeticMass_le_explicit N Q C).trans ?_
    calc
      (logConductorThreshold N C : ℝ) * conductorHarmonicFactor Q ^ 2 ≤
          Real.log N ^ C * (2 * Real.log N) ^ 2 := by gcongr
      _ = 4 * Real.log N ^ (C + 2) := by rw [pow_add]; ring
  · nlinarith

/-- Producer for the former full low-source black box.  Besides the existing
one-dimensional modulus-one PNT contract, the only analytic premise is the
pointwise nonprincipal primitive `ψ(N,χ)` Siegel--Walfisz theorem above. -/
theorem standardBVLowSiegelWalfiszSource_of_nonprincipalPrimitivePsi
    (hSW : NonprincipalPrimitivePsiSiegelWalfiszSource)
    (hPNT : GlobalChebyshevToLiPrincipalPNTSourceContract) :
    StandardBVLowSiegelWalfiszSource := by
  intro A C B
  obtain ⟨KS, hKS, hSN⟩ := hSW C (A + C + 5)
  obtain ⟨KP, hKP, hPN⟩ := hPNT (A + 3) (by positivity)
  refine ⟨32 * KS + 4 * KP, by positivity, ?_⟩
  filter_upwards [hSN, hPN, low_scalar_envelopes C B,
    eventually_ge_atTop (8 : ℕ)] with N hS hP henv hN
  dsimp only at henv ⊢
  let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have h8 : (1 : ℝ) < Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact h8.le.trans (Real.strictMonoOn_log.monotoneOn
      (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (N : ℝ) ∈ Set.Ioi 0 by
        change 0 < (N : ℝ)
        exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hN))
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hX0 : 0 ≤ KS * (N : ℝ) / Real.log N ^ (A + C + 5) := by positivity
  have hlowPoint : ∀ d ∈ lowConductorSet N Q C, ∀ ψ : PrimitiveCharacter d,
      primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
        KS * (N : ℝ) / Real.log N ^ (A + C + 5) := by
    intro d hd ψ
    apply hS (by omega) d
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
        (Finset.mem_filter.mp hd).2⟩
    · exact primitiveCharacter_ne_one_of_two_le
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1 ψ
  have hlow := lowConductorPhysical_le_of_primitivePrefix N Q C _ hX0 hlowPoint
  have hglobal := principalGlobal_add_chebyshevToLi_le_qOne N Q
  have hP' : globalPartialSummationSource N ≤
      KP * (N : ℝ) / Real.log N ^ (A + 3) := by
    convert hP (by omega) using 1
    rw [← Real.rpow_natCast]
    norm_num
  have hglobal0 : 0 ≤ globalPartialSummationSource N := by
    unfold globalPartialSummationSource
    have hp : 0 ≤ principalLambdaPrefixMaxError N 1 := by
      unfold principalLambdaPrefixMaxError
      exact (norm_nonneg (principalLambdaMainError 0 1)).trans
        (Finset.le_max'
          ((Finset.range (N + 1)).image (fun y => ‖principalLambdaMainError y 1‖)) _
          (Finset.mem_image.mpr
            ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
    have hc : 0 ≤ globalChebyshevToLiSourcePrefixMaxError N := by
      unfold globalChebyshevToLiSourcePrefixMaxError
      have hsource0 : 0 ≤ globalChebyshevToLiSourceError 0 := by
        unfold globalChebyshevToLiSourceError
        exact abs_nonneg _
      exact hsource0.trans
        (Finset.le_max'
          ((Finset.range (N + 1)).image globalChebyshevToLiSourceError) _
          (Finset.mem_image.mpr
            ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
    have habel0 : 0 ≤ discreteAbelAmplifierPrefixMax N := by
      have h0 : 0 ≤ discreteAbelAmplifier 0 := by
        unfold discreteAbelAmplifier
        positivity
      exact h0.trans (Finset.le_max' _ _ (Finset.mem_image.mpr
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N), rfl⟩))
    exact add_nonneg (mul_nonneg habel0 hp) hc
  have habel4 : discreteAbelAmplifierPrefixMax N ≤ 4 := by
    refine (discreteAbelAmplifierPrefixMax_le_two_inv_log_two N).trans ?_
    have hlt : (1 / 2 : ℝ) < Real.log 2 := Real.log_two_gt_d9.trans' (by norm_num)
    have hinv : (Real.log 2)⁻¹ < 2 := by
      rw [inv_eq_one_div, one_div_lt (Real.log_pos (by norm_num)) (by norm_num)]
      norm_num
      exact hlt
    linarith
  have hlowPay :
      2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C ≤
        32 * KS * (N : ℝ) / Real.log N ^ A := by
    have hlow0 : 0 ≤ lowConductorPhysical N Q C := by
      unfold lowConductorPhysical directConductorMeanOn
      apply Finset.sum_nonneg
      intro d hd
      apply mul_nonneg
      · unfold directConductorWeight
        positivity
      · exact Finset.sum_nonneg fun ψ _ =>
          primitivePrefixAmplitude_nonneg vonMangoldtIntegerCoeff N d ψ
    calc
      _ ≤ 2 * 4 * lowConductorPhysical N Q C := by gcongr
      _ ≤ 2 * 4 *
          (4 * Real.log N ^ (C + 2) *
            (KS * (N : ℝ) / Real.log N ^ (A + C + 5))) := by
              gcongr
              exact hlow.trans (mul_le_mul_of_nonneg_right henv.1 hX0)
      _ ≤ 32 * KS * (N : ℝ) / Real.log N ^ A := by
        rw [pow_add, pow_add]
        field_simp
        have hpowAC : 0 ≤ Real.log (N : ℝ) ^ (A + C) := by positivity
        have hlog3 : 1 ≤ Real.log (N : ℝ) ^ 3 := by
          exact one_le_pow₀ hlog
        have hpowmul : Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
            Real.log (N : ℝ) ^ (A + C) := by
          rw [← pow_add]
          congr 1
          omega
        calc
          2 * 4 ^ 2 * Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A =
              32 * (Real.log (N : ℝ) ^ C * Real.log (N : ℝ) ^ A) := by ring
          _ = 32 * Real.log (N : ℝ) ^ (A + C) := by rw [hpowmul]
          _ ≤ 32 * (Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C)) := by
            have hh : Real.log (N : ℝ) ^ (A + C) ≤
                Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C) := by
              simpa using mul_le_mul_of_nonneg_right hlog3 hpowAC
            exact mul_le_mul_of_nonneg_left hh (by norm_num)
          _ = Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (A + C) * 32 := by ring
  have hglobalPay :
      discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q ≤
        4 * KP * (N : ℝ) / Real.log N ^ A := by
    calc
      _ ≤ conductorHarmonicFactor Q ^ 2 * globalPartialSummationSource N := hglobal
      _ ≤ (4 * Real.log N ^ 2) *
          (KP * (N : ℝ) / Real.log N ^ (A + 3)) := by
            exact mul_le_mul henv.2 hP' hglobal0 (by positivity)
      _ ≤ 4 * KP * (N : ℝ) / Real.log N ^ A := by
        rw [pow_add]
        field_simp
        exact hlog
  change 2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C +
      discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
      chebyshevToLiPhysical N Q ≤ _
  calc
    _ = (2 * discreteAbelAmplifierPrefixMax N * lowConductorPhysical N Q C) +
        (discreteAbelAmplifierPrefixMax N * principalGlobalPhysical N Q +
          chebyshevToLiPhysical N Q) := by ring
    _ ≤ 32 * KS * (N : ℝ) / Real.log N ^ A +
        4 * KP * (N : ℝ) / Real.log N ^ A := add_le_add hlowPay hglobalPay
    _ = (32 * KS + 4 * KP) * (N : ℝ) / Real.log N ^ A := by ring

end

end AnalyticNumberTheory.LargeSieve
