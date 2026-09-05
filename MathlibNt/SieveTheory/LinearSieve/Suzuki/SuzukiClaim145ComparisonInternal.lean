import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143FullTail
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma143LogExponent
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition131iiLowerInternal

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.3 / Claim 14.5 comparison: internal quantitative bridge

This file keeps the Proposition 13.1(ii) lower estimate independent of every
Claim-14.5 assertion.  It also records explicitly the loss caused by replacing
the real power cutoff by its natural ceiling.
-/

/-- For `D ≥ 2` and `s ≥ 2`, the natural ceiling of `D^(1/s)` is still at most
`D`.  Thus the ceiling does not force the Lemma-14.1 logarithmic parameter to be
evaluated beyond `D`. -/
theorem claim145_natCeil_rpow_le
    {D : ℕ} {s : ℝ} (hD : 2 ≤ D) (hs : 2 ≤ s) :
    ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤ D := by
  have hDR : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by omega)
  have hs0 : 0 < s := by linarith
  have hexp : 1 / s ≤ (1 : ℝ) := by
    have : 1 ≤ s := by linarith
    simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) this)
  have hrpow : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hDR hexp
  have hrpowD : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    simpa using hrpow
  exact Nat.ceil_le.mpr hrpowD

/-- Monotonicity of the explicit Lemma-14.1 source parameter on the range where
both inner logarithms are positive. -/
theorem suzukiSourceL_mono
    {x y K : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    suzukiSourceL x K ≤ suzukiSourceL y K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hx0 hy0 hxy
  have hquotxy : Real.log x / Real.log 2 ≤ Real.log y / Real.log 2 := by
    exact div_le_div_of_nonneg_right hlogxy hlog2.le
  have hquotx : 0 < Real.log x / Real.log 2 :=
    div_pos (Real.log_pos hx) hlog2
  have hquoty : 0 < Real.log y / Real.log 2 := hquotx.trans_le hquotxy
  unfold suzukiSourceL
  gcongr

/-- The actual ceiling cutoff has no larger Lemma-14.1 logarithmic parameter
than the unrounded ambient cutoff `D`.  This is the ceiling-sensitive estimate
needed before any asymptotic comparison. -/
theorem suzukiSourceL_natCeil_rpow_le
    {D : ℕ} {s K : ℝ} (hD : 2 ≤ D) (hs : 2 ≤ s) :
    suzukiSourceL (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) K ≤
      suzukiSourceL (D : ℝ) K := by
  have hpow : (1 : ℝ) < (D : ℝ) ^ (1 / s) := by
    have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
    exact Real.one_lt_rpow hD1 (one_div_pos.mpr (by linarith))
  have hz1 : (1 : ℝ) < (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℕ) := by
    have hpow' : ((1 : ℕ) : ℝ) < (D : ℝ) ^ (1 / s) := by simpa using hpow
    exact_mod_cast ((Nat.lt_ceil).mpr hpow' : 1 < ⌈(D : ℝ) ^ (1 / s)⌉₊)
  apply suzukiSourceL_mono hz1
  exact_mod_cast claim145_natCeil_rpow_le hD hs

/-- The Proposition-13.1(ii) lower profile gives a literal lower bound for the
Claim-14.5 scale.  This step is uniform in the parity/depth `N`; the only use of
`N` is to select one of the two signs covered by the source theorem. -/
theorem claim14_5Scale_lower_of_proposition131ii
    (S : BoundingSieve) (H : Section13HatLayers)
    {N : ℕ} {D d Δ σ K C M s : ℝ}
    (hD : 1 < D) (hσ : 0 < σ) (hs : 0 < s)
    (hM : M ≤ s)
    (hprop : ∀ (sign : ErrorSign) (t : ℝ), M ≤ t →
      proposition131iiLowerProfile C t ≤ H.T sign t) :
    claim14_5VProduct S D * (Real.exp (Real.sqrt K) / (Real.log D * σ)) *
          ((1 + s ^ d / Real.log D) ^ s * s *
            proposition131iiLowerProfile C s) *
          (Real.log D) ^ (-Δ) ≤
      claim14_5Scale S H N D d Δ σ K s := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hbase : 0 < 1 + s ^ d / Real.log D := by
    have hpow : 0 ≤ s ^ d := Real.rpow_nonneg hs.le _
    have : 0 ≤ s ^ d / Real.log D := div_nonneg hpow hlogD.le
    linarith
  have hV : 0 ≤ claim14_5VProduct S D := by
    unfold claim14_5VProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
  have hfront : 0 ≤
      claim14_5VProduct S D *
        (Real.exp (Real.sqrt K) / (Real.log D * σ)) := by
    positivity
  have htail : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlogD.le _
  have hpowbase : 0 ≤ (1 + s ^ d / Real.log D) ^ s :=
    Real.rpow_nonneg hbase.le _
  have hT := hprop (ErrorSign.ofDepth N) s hM
  unfold claim14_5Scale errorEnvelope
  norm_num [Section13HatLayers.kappaHat, Real.rpow_one]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hT (mul_nonneg hpowbase hs.le)) hfront)
    htail

/-- Pointwise closure of Lemma 14.3 against the explicit Proposition-13.1(ii)
lower profile.  The final numerical premise is stated entirely in elementary
real functions and contains neither `Claim14_5Bound`, `claim14_5Scale`, nor the
discrete object.  It is the scalar large-logarithm inequality to be discharged
by the eventual asymptotic calculation. -/
theorem suzukiLemma14_3_le_claim145Scale_of_scalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ σ K C M C145 : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hσ : 2 ≤ σ) (hM : M ≤ σ)
    (hKpos : 0 < K) (hC145 : 0 ≤ C145)
    (hprop : ∀ (sign : ErrorSign) (t : ℝ), M ≤ t →
      proposition131iiLowerProfile C t ≤ H.T sign t)
    (hsourceLarge : Real.exp 1 * suzukiSourceL (D : ℝ) K ≤ σ - 2)
    (hscalar :
      Real.exp
          (suzukiSourceL (D : ℝ) K +
            (σ - 2) *
              (1 + Real.log (suzukiSourceL (D : ℝ) K) - Real.log (σ - 2))) ≤
        C145 *
          (claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) / (Real.log (D : ℝ) * σ)) *
            ((1 + σ ^ d / Real.log (D : ℝ)) ^ σ * σ *
              proposition131iiLowerProfile C σ) *
            (Real.log (D : ℝ)) ^ (-Δ))) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / σ)⌉₊ ≤
      C145 * claim14_5Scale S H N (D : ℝ) d Δ σ K σ := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / σ)⌉₊
  let LD : ℝ := suzukiSourceL (D : ℝ) K
  let Lz : ℝ := suzukiSourceL (z : ℝ) K
  have hD1 : 1 < D := by omega
  have hLzle : Lz ≤ LD := by
    simpa [z, Lz, LD] using suzukiSourceL_natCeil_rpow_le (D := D) (s := σ) (K := K) hD hσ
  have hLz0 : 0 < Lz := by
    have hz2 : 2 ≤ z := by
      have hp : (1 : ℝ) < (D : ℝ) ^ (1 / σ) :=
        Real.one_lt_rpow (by exact_mod_cast hD1)
          (one_div_pos.mpr (by linarith))
      have hz1nat : 1 < z := by
        dsimp [z]
        apply (Nat.lt_ceil).mpr
        simpa using hp
      omega
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogz : Real.log 2 ≤ Real.log (z : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < (z : ℝ) by positivity) (by exact_mod_cast hz2)
    have hfirst : 0 ≤ Real.log (Real.log (z : ℝ) / Real.log 2) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hlog2).2 (by simpa using hlogz)
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos hKpos hlog2
      linarith
    dsimp [Lz, suzukiSourceL]
    linarith
  have hlargeZ : Real.exp 1 * Lz ≤ σ - 2 :=
    (mul_le_mul_of_nonneg_left hLzle (Real.exp_pos 1).le).trans hsourceLarge
  have htail := suzukiLemma14_3_natCeil_uniform_explicit
    (S := S) (N := N) (D := D) (z := z) (s := σ) (K := K)
    hlocal hD1 hσ rfl
  have hlog := floorTail_le_claim145_logExponent hLz0 hlargeZ htail
  have hlogmono :
      Real.exp
          (Lz + (σ - 2) * (1 + Real.log Lz - Real.log (σ - 2))) ≤
        Real.exp
          (LD + (σ - 2) * (1 + Real.log LD - Real.log (σ - 2))) := by
    apply Real.exp_le_exp.mpr
    have hLD0 : 0 < LD := hLz0.trans_le hLzle
    have hlogs : Real.log Lz ≤ Real.log LD :=
      Real.strictMonoOn_log.monotoneOn hLz0 hLD0 hLzle
    have hsnonneg : 0 ≤ σ - 2 := sub_nonneg.mpr hσ
    nlinarith [mul_le_mul_of_nonneg_left hlogs hsnonneg]
  have hlower := claim14_5Scale_lower_of_proposition131ii
    S H (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ) (σ := σ)
      (K := K) (C := C) (M := M) (s := σ)
      (by exact_mod_cast hD1) (by linarith) (by linarith) hM hprop
  change suzukiActualT S N D z ≤ _
  exact hlog.trans (hlogmono.trans (hscalar.trans
    (mul_le_mul_of_nonneg_left hlower hC145)))

/-- Two-parameter Case-B closure of Lemma 14.3.  Here `σ` is Suzuki's
`(log D)^(1/d) log log (27D)` (and remains in the denominator of (14.6)),
whereas `s` is an arbitrary coordinate with `s ≥ σ`.  The former endpoint
lemma identified these parameters and therefore did not state the full Case-B
range. -/
theorem suzukiLemma14_3_le_claim145Scale_of_scalar_at
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ σ K C M C145 s : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hσ : 0 < σ) (hs : 2 ≤ s) (hM : M ≤ s)
    (hKpos : 0 < K) (hC145 : 0 ≤ C145)
    (hprop : ∀ (sign : ErrorSign) (t : ℝ), M ≤ t →
      proposition131iiLowerProfile C t ≤ H.T sign t)
    (hsourceLarge : Real.exp 1 * suzukiSourceL (D : ℝ) K ≤ s - 2)
    (hscalar :
      Real.exp
          (suzukiSourceL (D : ℝ) K +
            (s - 2) *
              (1 + Real.log (suzukiSourceL (D : ℝ) K) - Real.log (s - 2))) ≤
        C145 *
          (claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) / (Real.log (D : ℝ) * σ)) *
            ((1 + s ^ d / Real.log (D : ℝ)) ^ s * s *
              proposition131iiLowerProfile C s) *
            (Real.log (D : ℝ)) ^ (-Δ))) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      C145 * claim14_5Scale S H N (D : ℝ) d Δ σ K s := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let LD : ℝ := suzukiSourceL (D : ℝ) K
  let Lz : ℝ := suzukiSourceL (z : ℝ) K
  have hD1 : 1 < D := by omega
  have hLzle : Lz ≤ LD := by
    simpa [z, Lz, LD] using
      suzukiSourceL_natCeil_rpow_le (D := D) (s := s) (K := K) hD hs
  have hLz0 : 0 < Lz := by
    have hz2 : 2 ≤ z := by
      have hp : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
        Real.one_lt_rpow (by exact_mod_cast hD1)
          (one_div_pos.mpr (by linarith))
      have hz1nat : 1 < z := by
        dsimp [z]
        apply (Nat.lt_ceil).mpr
        simpa using hp
      omega
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogz : Real.log 2 ≤ Real.log (z : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < (z : ℝ) by positivity) (by exact_mod_cast hz2)
    have hfirst : 0 ≤ Real.log (Real.log (z : ℝ) / Real.log 2) := by
      apply Real.log_nonneg
      exact (le_div_iff₀ hlog2).2 (by simpa using hlogz)
    have hsecond : 0 < Real.log (1 + K / Real.log 2) := by
      apply Real.log_pos
      have : 0 < K / Real.log 2 := div_pos hKpos hlog2
      linarith
    dsimp [Lz, suzukiSourceL]
    linarith
  have hlargeZ : Real.exp 1 * Lz ≤ s - 2 :=
    (mul_le_mul_of_nonneg_left hLzle (Real.exp_pos 1).le).trans hsourceLarge
  have htail := suzukiLemma14_3_natCeil_uniform_explicit
    (S := S) (N := N) (D := D) (z := z) (s := s) (K := K)
    hlocal hD1 hs rfl
  have hlog := floorTail_le_claim145_logExponent hLz0 hlargeZ htail
  have hlogmono :
      Real.exp
          (Lz + (s - 2) * (1 + Real.log Lz - Real.log (s - 2))) ≤
        Real.exp
          (LD + (s - 2) * (1 + Real.log LD - Real.log (s - 2))) := by
    apply Real.exp_le_exp.mpr
    have hLD0 : 0 < LD := hLz0.trans_le hLzle
    have hlogs : Real.log Lz ≤ Real.log LD :=
      Real.strictMonoOn_log.monotoneOn hLz0 hLD0 hLzle
    have hsnonneg : 0 ≤ s - 2 := sub_nonneg.mpr hs
    nlinarith [mul_le_mul_of_nonneg_left hlogs hsnonneg]
  have hlower := claim14_5Scale_lower_of_proposition131ii
    S H (N := N) (D := (D : ℝ)) (d := d) (Δ := Δ) (σ := σ)
      (K := K) (C := C) (M := M) (s := s)
      (by exact_mod_cast hD1) hσ (by linarith) hM hprop
  change suzukiActualT S N D z ≤ _
  exact hlog.trans (hlogmono.trans (hscalar.trans
    (mul_le_mul_of_nonneg_left hlower hC145)))

/-- The same comparison with the quantifier over the discrete depth moved after
all analytic data.  In particular one scalar estimate and one Proposition
13.1(ii) pair of signwise bounds work for every `N`. -/
theorem suzukiLemma14_3_le_claim145Scale_uniformN_of_scalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {D : ℕ} {d Δ σ K C M C145 : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 2 ≤ D) (hσ : 2 ≤ σ) (hM : M ≤ σ)
    (hKpos : 0 < K) (hC145 : 0 ≤ C145)
    (hprop : ∀ (sign : ErrorSign) (t : ℝ), M ≤ t →
      proposition131iiLowerProfile C t ≤ H.T sign t)
    (hsourceLarge : Real.exp 1 * suzukiSourceL (D : ℝ) K ≤ σ - 2)
    (hscalar :
      Real.exp
          (suzukiSourceL (D : ℝ) K +
            (σ - 2) *
              (1 + Real.log (suzukiSourceL (D : ℝ) K) - Real.log (σ - 2))) ≤
        C145 *
          (claim14_5VProduct S (D : ℝ) *
            (Real.exp (Real.sqrt K) / (Real.log (D : ℝ) * σ)) *
            ((1 + σ ^ d / Real.log (D : ℝ)) ^ σ * σ *
              proposition131iiLowerProfile C σ) *
            (Real.log (D : ℝ)) ^ (-Δ))) :
    ∀ N : ℕ,
      suzukiActualT S N D ⌈(D : ℝ) ^ (1 / σ)⌉₊ ≤
        C145 * claim14_5Scale S H N (D : ℝ) d Δ σ K σ := by
  intro N
  exact suzukiLemma14_3_le_claim145Scale_of_scalar S H hlocal hD hσ hM
    hKpos hC145 hprop hsourceLarge hscalar


end MathlibNt.SieveTheory
