import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorEnvelopeTransportFull
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIErrorTransportUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144IHInstantiation

open scoped Classical BigOperators Interval
open Filter Finset Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-!
# The Case-I recursive coordinate lies below the quotient source endpoint

This is a genuine moving-carrier estimate.  It uses both power inequalities in
`sigmaOneCarrier`; in particular, it does not replace the carrier by an
asymptotically empty fixed finite support.
-/

private noncomputable def sourceRatio (d x : ℝ) : ℝ :=
  x ^ (1 - 1 / d) / Real.log (Real.log 27 + x)

private noncomputable def sourceRatioStart (d : ℝ) : ℝ :=
  Real.exp (2 / (1 - 1 / d))

private theorem sourceRatio_hasDerivAt {d x : ℝ} (hx : 0 < x)
    (hlog : Real.log (Real.log 27 + x) ≠ 0) :
    HasDerivAt (sourceRatio d)
      ((((1 - 1 / d) * x ^ (1 - 1 / d - 1)) *
          Real.log (Real.log 27 + x) -
        x ^ (1 - 1 / d) * (Real.log 27 + x)⁻¹) /
        Real.log (Real.log 27 + x) ^ 2) x := by
  unfold sourceRatio
  have hinner0 : 0 < Real.log 27 + x := by
    have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hinner : HasDerivAt (fun y : ℝ => Real.log 27 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add (Real.log 27)
  have hlogder : HasDerivAt (fun y : ℝ => Real.log (Real.log 27 + y))
      (Real.log 27 + x)⁻¹ x := by
    simpa using hinner.log (ne_of_gt hinner0)
  exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).div hlogder hlog

private theorem sourceRatio_monotoneOn {d : ℝ} (hd : 1 < d) :
    MonotoneOn (sourceRatio d) (Set.Ici (sourceRatioStart d)) := by
  have hb : 0 < 1 - 1 / d := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd
    norm_num at h ⊢
    linarith
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro x hx
    have hstart1 : 1 < sourceRatioStart d := by
      unfold sourceRatioStart
      exact Real.one_lt_exp_iff.mpr (div_pos (by norm_num) hb)
    have hx0 : 0 < x := zero_lt_one.trans (hstart1.trans_le hx)
    have hx1 : 1 < x := hstart1.trans_le hx
    have hlog : Real.log (Real.log 27 + x) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      linarith
    exact (sourceRatio_hasDerivAt hx0 hlog).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := (Real.exp_pos _).trans hx
    have hlogne : Real.log (Real.log 27 + x) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      have hstart1 : 1 < sourceRatioStart d := by
        unfold sourceRatioStart
        exact Real.one_lt_exp_iff.mpr (div_pos (by norm_num) hb)
      have hx1 : 1 < x := hstart1.trans hx
      linarith
    exact (sourceRatio_hasDerivAt hx0 hlogne).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := (Real.exp_pos _).trans hx
    have hinner0 : 0 < Real.log 27 + x := by
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      positivity
    have hlogpos : 0 < Real.log (Real.log 27 + x) := by
      apply Real.log_pos
      have : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
      have hstart1 : 1 < sourceRatioStart d := by
        unfold sourceRatioStart
        exact Real.one_lt_exp_iff.mpr (div_pos (by norm_num) hb)
      have hx1 : 1 < x := hstart1.trans hx
      linarith
    have hderiv := sourceRatio_hasDerivAt (d := d) hx0 (ne_of_gt hlogpos)
    rw [hderiv.deriv]
    have hstart : sourceRatioStart d < x := hx
    have hlogx : 2 / (1 - 1 / d) < Real.log x := by
      rw [← Real.log_exp (2 / (1 - 1 / d))]
      exact Real.strictMonoOn_log (Real.exp_pos _) hx0 hstart
    have hloginner : Real.log x ≤ Real.log (Real.log 27 + x) := by
      have hlog27 : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
      exact Real.log_le_log hx0 (by linarith)
    have hbig : 1 ≤ (1 - 1 / d) * Real.log (Real.log 27 + x) := by
      have : 2 < (1 - 1 / d) * Real.log (Real.log 27 + x) := by
        have := lt_of_lt_of_le hlogx hloginner
        simpa [mul_comm] using (div_lt_iff₀ hb).mp this
      linarith
    have hfrac : x / (Real.log 27 + x) ≤ 1 := by
      apply (div_le_one hinner0).2
      have : 0 ≤ Real.log (27 : ℝ) := (Real.log_pos (by norm_num)).le
      linarith
    have hpowpos : 0 < x ^ (1 - 1 / d - 1) := Real.rpow_pos_of_pos hx0 _
    have hpow : x ^ (1 - 1 / d) = x ^ (1 - 1 / d - 1) * x := by
      rw [Real.rpow_sub_one (ne_of_gt hx0)]
      field_simp
    rw [hpow]
    have hnum : 0 ≤
        ((1 - 1 / d) * x ^ (1 - 1 / d - 1)) *
              Real.log (Real.log 27 + x) -
          (x ^ (1 - 1 / d - 1) * x) *
              (Real.log 27 + x)⁻¹ := by
      rw [show ((1 - 1 / d) * x ^ (1 - 1 / d - 1)) *
              Real.log (Real.log 27 + x) -
          (x ^ (1 - 1 / d - 1) * x) * (Real.log 27 + x)⁻¹ =
          x ^ (1 - 1 / d - 1) *
            ((1 - 1 / d) * Real.log (Real.log 27 + x) -
              x / (Real.log 27 + x)) by ring]
      exact mul_nonneg hpowpos.le (sub_nonneg.mpr (hfrac.trans hbig))
    exact div_nonneg hnum (sq_nonneg _)

private theorem sourceSigma_log_form {X d : ℝ} (hX : 0 < X) :
    sourceSigma X d =
      (Real.log X) ^ (1 / d) * Real.log (Real.log 27 + Real.log X) := by
  unfold sourceSigma
  rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hX)]

private theorem sourceRatio_mul_sourceSigma {X d : ℝ}
    (hd : 1 < d) (hX : 1 < X)
    (hloglog : 0 < Real.log (Real.log 27 + Real.log X)) :
    sourceRatio d (Real.log X) * sourceSigma X d = Real.log X := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hden : Real.log (Real.log 27 + Real.log X) ≠ 0 := ne_of_gt hloglog
  rw [sourceRatio, sourceSigma_log_form (zero_lt_one.trans hX)]
  field_simp [hden]
  have hd0 : d ≠ 0 := ne_of_gt (zero_lt_one.trans hd)
  have he : (d - 1) / d + 1 / d = 1 := by
    field_simp
    ring
  rw [← Real.rpow_add hlogX, he, Real.rpow_one]

/-- Pointwise form, independent of any finite support. -/
theorem recursiveCoordinate_le_quotient_sourceSigma
    {d : ℝ} (hd : 1 < d) {D p : ℕ}
    (hD : (Real.exp (sourceRatioStart d)) ^ 2 ≤ (D : ℝ))
    (hp : p.Prime) {s : ℝ} (hs : 2 ≤ s)
    (hlower : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (p : ℝ))
    (hupper : (p : ℝ) < (D : ℝ) ^ (1 / s)) :
    recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hstart0 : 0 < sourceRatioStart d := by
    unfold sourceRatioStart
    positivity
  have hD1R : (1 : ℝ) < (D : ℝ) := by
    have : 1 < (Real.exp (sourceRatioStart d)) ^ 2 := by
      have := Real.one_lt_exp_iff.mpr hstart0
      nlinarith
    exact this.trans_le hD
  have hD0 : 0 < D := by exact_mod_cast (zero_lt_one.trans hD1R)
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := hD1R.le
  have hrootOrder : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 / (2 : ℝ)) :=
    rpow_one_div_mono_of_le hD1 (by norm_num) hs
  have hpRoot : (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) :=
    hupper.trans_le hrootOrder
  have hsquareR : (p : ℝ) ^ (2 : ℕ) < (D : ℝ) := by
    have hiff := Real.lt_rpow_inv_iff_of_pos
      (x := (p : ℝ)) (y := (D : ℝ)) (z := (2 : ℝ))
      (by positivity) (by positivity) (by norm_num)
    norm_num [one_div] at hiff hpRoot ⊢
    exact hiff.mp hpRoot
  have hsquare : p ^ 2 < D := by exact_mod_cast hsquareR
  let q : ℕ := D ⌈/⌉ p
  have hmul := ceilDiv_mul_bounds (D := D) (p := p) hp0
  have hpq : p < q := by
    dsimp [q]
    nlinarith [hmul.1]
  have hq2 : 2 ≤ q := by omega
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hqD : q ≤ D := by
    dsimp [q]
    apply (ceilDiv_le_iff_le_mul hp0).2
    nlinarith
  have hDqSquare : D < q ^ 2 := by
    calc
      D ≤ q * p := by simpa [q] using hmul.1
      _ < q * q := (Nat.mul_lt_mul_left hq0).2 hpq
      _ = q ^ 2 := by ring
  have hqStartR : Real.exp (sourceRatioStart d) < (q : ℝ) := by
    have hqSquareR : (D : ℝ) < (q : ℝ) ^ 2 := by exact_mod_cast hDqSquare
    nlinarith [sq_nonneg ((q : ℝ) - Real.exp (sourceRatioStart d))]
  have hlogqStart : sourceRatioStart d < Real.log (q : ℝ) := by
    rw [← Real.log_exp (sourceRatioStart d)]
    exact Real.strictMonoOn_log (Real.exp_pos _) hqR hqStartR
  have hlogOrder : Real.log (q : ℝ) ≤ Real.log (D : ℝ) :=
    Real.log_le_log hqR (by exact_mod_cast hqD)
  have hloglogq : 0 < Real.log (Real.log 27 + Real.log (q : ℝ)) := by
    apply Real.log_pos
    have hstart1 : 1 < sourceRatioStart d := by
      unfold sourceRatioStart
      exact Real.one_lt_exp_iff.mpr (by
        have hb : 0 < 1 - 1 / d := by
          have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd
          norm_num at h ⊢
          linarith
        positivity)
    have hlog27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hloglogD : 0 < Real.log (Real.log 27 + Real.log (D : ℝ)) := by
    apply Real.log_pos
    have hlog27 : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
    have : 1 < Real.log (q : ℝ) := by
      have hstart1 : 1 < sourceRatioStart d := by
        unfold sourceRatioStart
        exact Real.one_lt_exp_iff.mpr (by
          have hb : 0 < 1 - 1 / d := by
            have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hd
            norm_num at h ⊢
            linarith
          positivity)
      linarith
    linarith
  have hmono : sourceRatio d (Real.log (q : ℝ)) ≤
      sourceRatio d (Real.log (D : ℝ)) :=
    sourceRatio_monotoneOn hd hlogqStart.le
      (hlogqStart.le.trans hlogOrder) hlogOrder
  have hsigDpos : 0 < sourceSigma (D : ℝ) d := by
    rw [sourceSigma_log_form (by positivity)]
    exact mul_pos (Real.rpow_pos_of_pos (Real.log_pos hD1R) _) hloglogD
  have hcarrierLog : Real.log (D : ℝ) / sourceSigma (D : ℝ) d ≤
      Real.log (p : ℝ) := by
    have h := Real.log_le_log
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (D : ℝ)) _) hlower
    rw [Real.log_rpow (by positivity)] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have hratioD : sourceRatio d (Real.log (D : ℝ)) =
      Real.log (D : ℝ) / sourceSigma (D : ℝ) d := by
    apply (eq_div_iff (ne_of_gt hsigDpos)).2
    exact sourceRatio_mul_sourceSigma hd hD1R hloglogD
  have hratioLog : sourceRatio d (Real.log (q : ℝ)) ≤ Real.log (p : ℝ) := by
    rw [hratioD] at hmono
    exact hmono.trans hcarrierLog
  have hsigqpos : 0 < sourceSigma (q : ℝ) d := by
    rw [sourceSigma_log_form hqR]
    exact mul_pos (Real.rpow_pos_of_pos (Real.log_pos (by
      exact_mod_cast (show 1 < q by omega)) ) _) hloglogq
  have hproduct : Real.log (q : ℝ) ≤
      Real.log (p : ℝ) * sourceSigma (q : ℝ) d := by
    rw [← sourceRatio_mul_sourceSigma hd (by
      exact_mod_cast (show 1 < q by omega)) hloglogq]
    exact mul_le_mul_of_nonneg_right hratioLog hsigqpos.le
  unfold recursiveCoordinate
  dsimp [q] at hproduct ⊢
  exact (div_le_iff₀ hlogp).2 (by simpa [mul_comm] using hproduct)

/-- Uniform Case-I carrier actualization with the threshold chosen before
any sieve.  The proof and cutoff depend only on `d`. -/
theorem eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform
    {d : ℝ} (hd : 1 < d) :
    ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve) (s : ℝ), 2 ≤ s →
      ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        recursiveCoordinate D p ≤
          sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (Real.exp (sourceRatioStart d))
  filter_upwards [eventually_ge_atTop (M ^ 2)] with D hD
  intro S s hs p hpCarrier
  have hp' := Finset.mem_filter.mp hpCarrier
  apply recursiveCoordinate_le_quotient_sourceSigma hd
  · have hcast : (M : ℝ) ^ 2 ≤ (D : ℝ) := by exact_mod_cast hD
    have hstart0 : 0 < Real.exp (sourceRatioStart d) := Real.exp_pos _
    nlinarith
  · exact Nat.prime_of_mem_primeFactors hp'.1
  · exact hs
  · exact hp'.2.1
  · exact hp'.2.2

/-- Compatibility wrapper for the original sieve-first API. -/
theorem eventually_recursiveCoordinate_le_quotient_sourceSigma
    (S : BoundingSieve) {d : ℝ} (hd : 1 < d) :
    ∀ᶠ D : ℕ in atTop, ∀ (s : ℝ), 2 ≤ s →
      ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D
          (sourceSigma (D : ℝ) d) s,
        recursiveCoordinate D p ≤
          sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d :=
  (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd).mono
    (fun _ hD => hD S)


end MathlibNt.SieveTheory
