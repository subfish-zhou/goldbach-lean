import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowS
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface

open scoped Classical BigOperators
open Filter Topology Asymptotics Set

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-- The strengthened prefactor estimate needed in the low-coordinate branch.
Unlike the preliminary version, this statement retains the moving
`sourceSigma` factor occurring in the denominator of Claim 14.5. -/
def Claim145CaseALowSSourceSigmaPrefactor
    (d Δ C1 Θ C : ℝ) : Prop :=
  ∀ᶠ K : ℝ in atTop, 2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 2 ≤ s →
    s ≤ Real.sqrt K / Real.log K →
    Real.log D ≤ C1 * K ^ Θ →
    (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
        sourceSigma D d * (Real.log D) ^ (1 + Δ) * Real.exp (C * s) ≤
      Real.exp (Real.sqrt K / 2)

/-- Proposition 13.1(ii)'s eventual lower profile can be enlarged in its linear
loss so that it starts at `s = 2`.  This is the compact initial interval which
must be closed before the final low-`s` branch is genuinely uniform in `s`. -/
theorem proposition131iiUniformQuantitativeLower_from_two
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (sign : ErrorSign) (s : ℝ), 2 ≤ s →
      proposition131iiLowerProfile C s ≤ H.T sign s := by
  rcases proposition131iiUniformQuantitativeLower_of_source hH with
    ⟨C₀, M, hC₀, hM, htail⟩
  have hcompact : IsCompact (Icc (2 : ℝ) M) := isCompact_Icc
  have hnonempty : (Icc (2 : ℝ) M).Nonempty := ⟨2, le_rfl, by linarith⟩
  have hcont : ∀ sign : ErrorSign, ContinuousOn (H.T sign) (Icc (2 : ℝ) M) := by
    intro sign
    exact (hH.toSection13HatContract.continuous sign).mono (by
      intro s hs
      show 0 < s
      linarith [hs.1])
  choose xmin hxmin hmin using fun sign =>
    hcompact.exists_isMinOn hnonempty (hcont sign)
  let δ : ℝ := min (H.T ErrorSign.plus (xmin ErrorSign.plus))
    (H.T ErrorSign.minus (xmin ErrorSign.minus))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min
      (hH.toSection13HatContract.positive ErrorSign.plus _ (by linarith [(hxmin ErrorSign.plus).1]))
      (hH.toSection13HatContract.positive ErrorSign.minus _ (by linarith [(hxmin ErrorSign.minus).1]))
  have hδle : ∀ sign : ErrorSign, ∀ s ∈ Icc (2 : ℝ) M, δ ≤ H.T sign s := by
    intro sign s hs
    cases sign with
    | plus =>
        exact (min_le_left _ _).trans (hmin ErrorSign.plus hs)
    | minus =>
        exact (min_le_right _ _).trans (hmin ErrorSign.minus hs)
  let C : ℝ := max C₀ (max 0 (-Real.log δ / 2))
  have hC : 0 ≤ C := (le_max_left 0 _).trans (le_max_right C₀ _)
  refine ⟨C, hC, ?_⟩
  intro sign s hs
  by_cases hsM : M ≤ s
  · have hprof := htail sign s hsM
    unfold proposition131iiLowerProfile at hprof ⊢
    apply hprof.trans'
    apply Real.exp_le_exp.mpr
    have hC₀C : C₀ ≤ C := le_max_left _ _
    nlinarith
  · have hsI : s ∈ Icc (2 : ℝ) M := ⟨hs, le_of_not_ge hsM⟩
    unfold proposition131iiLowerProfile
    have hlogs : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
    have hloglog : 0 ≤ Real.log (Real.log (3 * s)) := by
      apply Real.log_nonneg
      have hlog6 : 1 ≤ Real.log 6 := by
        exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 6)).2
          (Real.exp_one_lt_d9.trans (by norm_num)) |>.le
      have hm : Real.log 6 ≤ Real.log (3 * s) :=
        Real.strictMonoOn_log.monotoneOn
          (show (0 : ℝ) < 6 by norm_num)
          (show (0 : ℝ) < 3 * s by nlinarith)
          (show (6 : ℝ) ≤ 3 * s by nlinarith)
      exact hlog6.trans hm
    have hClog : -Real.log δ / 2 ≤ C :=
      (le_max_right 0 (-Real.log δ / 2)).trans (le_max_right C₀ _)
    calc
      Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) - C * s) ≤
          Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by nlinarith)
      _ = δ := Real.exp_log hδ
      _ ≤ H.T sign s := hδle sign s hsI

/-- At the bottom endpoint `2`, the local-product contract gives exactly the
reciprocal Euler-product factor used by the prefactor estimate. -/
theorem one_le_claim145_local_factor_mul_vProduct
    (S : BoundingSieve) {D : ℕ} {K : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hD : 2 ≤ D) :
    1 ≤ (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2) *
      claim14_5VProduct S (D : ℝ) := by
  have hratio := hlocal 2 (D : ℝ) (by norm_num) (by exact_mod_cast hD)
  have hfilter :
      S.prodPrimes.primeFactors.filter
          (fun p : ℕ => (2 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (D : ℝ)) =
        S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < (D : ℝ)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, _, hpD⟩
      exact ⟨hp, hpD⟩
    · rintro ⟨hp, hpD⟩
      have hpprime := Nat.prime_of_mem_primeFactors hp
      exact ⟨hp, by exact_mod_cast hpprime.two_le, hpD⟩
  have hprod : suzukiLocalRatio S 2 (D : ℝ) *
      claim14_5VProduct S (D : ℝ) = 1 := by
    unfold suzukiLocalRatio claim14_5VProduct
    rw [hfilter, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpprime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv := (Nat.mem_primeFactors.mp hpS).2.1
    have hne : 1 - S.nu p ≠ 0 := by
      linarith [S.nu_lt_one_of_prime p hpprime hpdiv]
    exact inv_mul_cancel₀ hne
  have hV : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    unfold claim14_5VProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hpS) (Nat.mem_primeFactors.mp hpS).2.1).le
  calc
    1 = suzukiLocalRatio S 2 (D : ℝ) * claim14_5VProduct S (D : ℝ) := hprod.symm
    _ ≤ ((Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)) *
        claim14_5VProduct S (D : ℝ) := mul_le_mul_of_nonneg_right hratio hV
    _ = _ := by ring

/-- Pure terminal algebra: the sourceSigma-inclusive prefactor turns the second
exponential comparison into the explicit lower side of (14.6). -/
theorem claim145_caseA_lowS_target_le_equation14_6_lower
    (S : BoundingSieve) {D : ℕ} {d Δ K s C : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hs : 2 ≤ s)
    (hpref :
      (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2) *
          sourceSigma (D : ℝ) d * (Real.log (D : ℝ)) ^ (1 + Δ) *
            Real.exp (C * s) ≤ Real.exp (Real.sqrt K / 2)) :
    Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
        Real.sqrt K / 2) ≤
      claim14_5VProduct S (D : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
          ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
            proposition131iiLowerProfile C s) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
  let R := (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)
  let σ := sourceSigma (D : ℝ) d
  let L := Real.log (D : ℝ)
  let X := Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
    Real.sqrt K / 2)
  let P := σ * L ^ (1 + Δ) * Real.exp (C * s)
  let V := claim14_5VProduct S (D : ℝ)
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hD1
  have hσ : 0 < σ := by dsimp [σ]; exact sourceSigma_pos_of_nat_two_le hD
  have hP : 0 < P := by dsimp [P]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hRV : 1 ≤ R * V := by
    simpa [R, V, mul_assoc] using one_le_claim145_local_factor_mul_vProduct S hlocal hD
  have hPV : P ≤ V * Real.exp (Real.sqrt K / 2) := by
    have hP_RP : P ≤ (R * V) * P := by nlinarith [mul_le_mul_of_nonneg_right hRV hP.le]
    have hmult := mul_le_mul_of_nonneg_right hpref (show 0 ≤ V by
      dsimp [V, claim14_5VProduct]
      apply Finset.prod_nonneg
      intro p hp
      have hpS := (Finset.mem_filter.mp hp).1
      exact sub_nonneg.mpr (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpS)
        (Nat.mem_primeFactors.mp hpS).2.1).le)
    dsimp [R, P] at hP_RP hmult
    dsimp [V]
    nlinarith
  have hquot : X ≤ X * (V * Real.exp (Real.sqrt K / 2)) / P := by
    apply (le_div_iff₀ hP).2
    nlinarith [mul_le_mul_of_nonneg_left hPV hX.le]
  have hbase : 1 ≤ (1 + s ^ d / L) ^ s * s := by
    have hb : 1 ≤ 1 + s ^ d / L := by
      have : 0 ≤ s ^ d / L := div_nonneg (Real.rpow_nonneg (by linarith) _) hL.le
      linarith
    have hp : 1 ≤ (1 + s ^ d / L) ^ s := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num) hb (by linarith)
    nlinarith
  calc
    X ≤ X * (V * Real.exp (Real.sqrt K / 2)) / P := hquot
    _ = V * (Real.exp (Real.sqrt K) / (L * σ)) *
          proposition131iiLowerProfile C s * L ^ (-Δ) := by
      rw [div_eq_iff hP.ne']
      have hexpLeft : X * Real.exp (Real.sqrt K / 2) =
          Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
            Real.sqrt K) := by
        dsimp [X]
        rw [← Real.exp_add]
        congr 1
        ring
      have hexpRight : Real.exp (Real.sqrt K) *
            proposition131iiLowerProfile C s * Real.exp (C * s) =
          Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
            Real.sqrt K) := by
        unfold proposition131iiLowerProfile
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hpow : L ^ (-Δ) * L ^ (1 + Δ) = L := by
        rw [← Real.rpow_add hL]
        convert Real.rpow_one L using 1 <;> ring
      calc
        X * (V * Real.exp (Real.sqrt K / 2)) =
            V * Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
              Real.sqrt K) := by rw [show X * (V * Real.exp (Real.sqrt K / 2)) =
              V * (X * Real.exp (Real.sqrt K / 2)) by ring, hexpLeft]
        _ = (V * (Real.exp (Real.sqrt K) / (L * σ)) *
              proposition131iiLowerProfile C s * L ^ (-Δ)) * P := by
            dsimp [P]
            rw [show (V * (Real.exp (Real.sqrt K) / (L * σ)) *
                proposition131iiLowerProfile C s * L ^ (-Δ)) *
                (σ * L ^ (1 + Δ) * Real.exp (C * s)) =
              V * (Real.exp (Real.sqrt K) * proposition131iiLowerProfile C s *
                Real.exp (C * s)) * (L ^ (-Δ) * L ^ (1 + Δ)) *
                (σ / (L * σ)) by ring]
            rw [hexpRight, hpow]
            field_simp [hL.ne', hσ.ne']
    _ ≤ V * (Real.exp (Real.sqrt K) / (L * σ)) *
          ((1 + s ^ d / L) ^ s * s * proposition131iiLowerProfile C s) *
          L ^ (-Δ) := by
      have hV : 0 ≤ V := by
        dsimp [V, claim14_5VProduct]
        apply Finset.prod_nonneg
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        exact sub_nonneg.mpr (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hpS)
          (Nat.mem_primeFactors.mp hpS).2.1).le
      have hprof : 0 ≤ proposition131iiLowerProfile C s := Real.exp_pos _ |>.le
      have hfront : 0 ≤ V * (Real.exp (Real.sqrt K) / (L * σ)) := by positivity
      have htail : 0 ≤ L ^ (-Δ) := Real.rpow_nonneg hL.le _
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hbase hprof) hfront,
        mul_nonneg (mul_nonneg hfront hprof) htail]
    _ = _ := by dsimp [V, L, σ]

/-- Final Case-A low-`s` assembly.  A single `K0` is selected before
`K,N,D,s`; the conclusion is the actual production `Claim14_5Bound` (through
its source-native spelling `ActualClaim145BoundAt`), with constant one. -/
theorem claim145_caseA_lowS_actual_of_bigOScalarTarget
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hbigO : Claim145CaseALowSBigOScalarTarget C1 Θ)
    (hpref : ∀ C : ℝ, 0 ≤ C →
      Claim145CaseALowSSourceSigmaPrefactor d Δ C1 Θ C) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧
      Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 1 := by
  rcases hbigO with ⟨A, KA, hA, hKA, hbigO⟩
  rcases proposition131iiUniformQuantitativeLower_from_two hH with
    ⟨C, hC, hprop⟩
  have hcmp := claim145_caseA_lowS_exponent_comparison_eventually hA
  have hpre := hpref C hC
  have hall : ∀ᶠ K : ℝ in atTop,
      KA ≤ K ∧ (2 ≤ K ∧ ∀ s : ℝ, 2 ≤ s →
        s ≤ Real.sqrt K / Real.log K →
        Real.exp (-s * Real.log s + s * Real.log (Real.log (3 * K)) +
          A * (Real.log K + s)) ≤
        Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
          Real.sqrt K / 2)) ∧
      (2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 2 ≤ s →
        s ≤ Real.sqrt K / Real.log K → Real.log D ≤ C1 * K ^ Θ →
        (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          sourceSigma D d * (Real.log D) ^ (1 + Δ) * Real.exp (C * s) ≤
          Real.exp (Real.sqrt K / 2)) :=
    (eventually_ge_atTop KA).and (hcmp.and hpre)
  rcases eventually_atTop.1 hall with ⟨K0, hK0⟩
  refine ⟨K0, ?_, ?_⟩
  · have h := hK0 K0 le_rfl
    exact hKA.trans h.1
  · intro K N D s hK hlocal hD hs hsupper hsmall
    have hkdata := hK0 K hK
    have htail := claim145_caseA_lowS_lemma14_3_upper (N := N) S hlocal hD rfl hs
    have hfirst := hbigO D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
      hkdata.1 hD rfl hs hsupper hsmall
    have hsecond := hkdata.2.1.2 s hs hsupper
    have htarget := claim145_caseA_lowS_target_le_equation14_6_lower
      S hlocal hD hs (hkdata.2.2.2 (D : ℝ) s (by exact_mod_cast hD)
        hs hsupper hsmall)
    have hlower := claim14_5Scale_lower_of_proposition131ii
      S H (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ)
        (σ := sourceSigma (D : ℝ) d) (K := K) (C := C) (M := 2) (s := s)
        (by exact_mod_cast (show 1 < D by omega))
        (sourceSigma_pos_of_nat_two_le hD) (by linarith) hs
        (fun sign t ht => hprop sign t ht)
    unfold ActualClaim145BoundAt
    simpa only [one_mul] using
      htail.trans (hfirst.trans (hsecond.trans (htarget.trans hlower)))

/-- Closed production-facing low-`s` leaf, using the strengthened
sourceSigma-inclusive prefactor theorem.  The first source big-O estimate is supplied by `claim145_caseA_lowS_bigOScalarTarget`. -/
theorem claim145_caseA_lowS_actual
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧
      Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 1 := by
  apply claim145_caseA_lowS_actual_of_bigOScalarTarget S H hH
    (claim145_caseA_lowS_bigOScalarTarget C1 Θ)
  intro C hC
  simpa only [Claim145CaseALowSSourceSigmaPrefactor, mul_assoc,
      mul_left_comm, mul_comm] using
    (claim145_caseA_lowS_146_prefactor_eventually hC1 hΘ hd hsource hΔ0 hΔ1 hC)

/-- Uniform-in-sieve strengthening of the low-coordinate Case-A leaf.  All
analytic witnesses and the `K` threshold are chosen before the varying sieve. -/
theorem claim145_caseA_lowS_actual_uniform_in_S
    (H : Section13HatLayers) {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    ∃ K0 : ℝ, 2 ≤ K0 ∧ ∀ S : BoundingSieve,
      Claim145CaseALargeKLowSClosed S H d Δ C1 Θ K0 1 := by
  rcases claim145_caseA_lowS_bigOScalarTarget C1 Θ with ⟨A, KA, hA, hKA, hbigO⟩
  rcases proposition131iiUniformQuantitativeLower_from_two hH with ⟨C, hC, hprop⟩
  have hcmp := claim145_caseA_lowS_exponent_comparison_eventually hA
  have hpre : Claim145CaseALowSSourceSigmaPrefactor d Δ C1 Θ C := by
    simpa only [Claim145CaseALowSSourceSigmaPrefactor, mul_assoc,
      mul_left_comm, mul_comm] using
      (claim145_caseA_lowS_146_prefactor_eventually hC1 hΘ hd hsource hΔ0 hΔ1 hC)
  have hall : ∀ᶠ K : ℝ in atTop,
      KA ≤ K ∧ (2 ≤ K ∧ ∀ s : ℝ, 2 ≤ s →
        s ≤ Real.sqrt K / Real.log K →
        Real.exp (-s * Real.log s + s * Real.log (Real.log (3 * K)) +
          A * (Real.log K + s)) ≤
        Real.exp (-s * Real.log s - s * Real.log (Real.log (3 * s)) +
          Real.sqrt K / 2)) ∧
      (2 ≤ K ∧ ∀ D s : ℝ, 2 ≤ D → 2 ≤ s →
        s ≤ Real.sqrt K / Real.log K → Real.log D ≤ C1 * K ^ Θ →
        (Real.log D / Real.log 2) * (1 + K / Real.log 2) *
          sourceSigma D d * (Real.log D) ^ (1 + Δ) * Real.exp (C * s) ≤
          Real.exp (Real.sqrt K / 2)) :=
    (eventually_ge_atTop KA).and (hcmp.and hpre)
  rcases eventually_atTop.1 hall with ⟨K0, hK0⟩
  refine ⟨K0, ?_, ?_⟩
  · exact hKA.trans (hK0 K0 le_rfl).1
  · intro S K N D s hK hlocal hD hs hsupper hsmall
    have hkdata := hK0 K hK
    have htail := claim145_caseA_lowS_lemma14_3_upper (N := N) S hlocal hD rfl hs
    have hfirst := hbigO D ⌈(D : ℝ) ^ (1 / s)⌉₊ K s
      hkdata.1 hD rfl hs hsupper hsmall
    have hsecond := hkdata.2.1.2 s hs hsupper
    have htarget := claim145_caseA_lowS_target_le_equation14_6_lower
      S hlocal hD hs (hkdata.2.2.2 (D : ℝ) s (by exact_mod_cast hD)
        hs hsupper hsmall)
    have hlower := claim14_5Scale_lower_of_proposition131ii
      S H (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ)
        (σ := sourceSigma (D : ℝ) d) (K := K) (C := C) (M := 2) (s := s)
        (by exact_mod_cast (show 1 < D by omega))
        (sourceSigma_pos_of_nat_two_le hD) (by linarith) hs
        (fun sign t ht => hprop sign t ht)
    unfold ActualClaim145BoundAt
    simpa only [one_mul] using
      htail.trans (hfirst.trans (hsecond.trans (htarget.trans hlower)))


end MathlibNt.SieveTheory
