import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAFixedDRange

open scoped Classical BigOperators

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Claim 14.5, Case A: bounded `K`

This is the bounded-parameter branch suppressed by the source `O(1)` notation.
There is no numerical search: the quotient range follows from exponentiating
`log D ≤ C₁ K^Θ`, and monotonicity replaces every local-product parameter by the
single upper endpoint `Kmax`.
-/

lemma hasDimensionOneLocalProductBound_mono_K
    {S : BoundingSieve} {K K' : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hKK' : K ≤ K') :
    HasDimensionOneLocalProductBound S K' := by
  intro w z hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  have hratio : 0 ≤ Real.log z / Real.log w := div_nonneg hlogz hlogw.le
  have hinside : 1 + K / Real.log w ≤ 1 + K' / Real.log w :=
    add_le_add_right (div_le_div_of_nonneg_right hKK' hlogw.le) 1
  exact (hlocal w z hw hwz).trans
    (mul_le_mul_of_nonneg_left hinside hratio)

lemma claim14_5Scale_upperK_le
    (S : BoundingSieve) (H : Section13HatLayers) (N : ℕ)
    {D d Δ σ K Kmax s : ℝ}
    (hD : 1 < D) (hσ : 0 < σ) (hs : 0 < s)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth N) s) :
    claim14_5Scale S H N D d Δ σ Kmax s ≤
      Real.exp (Real.sqrt Kmax) * claim14_5Scale S H N D d Δ σ K s := by
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hV : 0 ≤ claim14_5VProduct S D := by
    unfold claim14_5VProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hpS) (Nat.mem_primeFactors.mp hpS).2.1).le
  have hE : 0 ≤ errorEnvelope H N D d s :=
    errorEnvelope_nonneg H N hD hs.le hT
  have hpow : 0 ≤ (Real.log D) ^ (-Δ) := Real.rpow_nonneg hlogD.le _
  have hexpK : 1 ≤ Real.exp (Real.sqrt K) := by
    simpa using Real.exp_one_le_iff.mpr (Real.sqrt_nonneg K)
  unfold claim14_5Scale
  have hcommon : 0 ≤ claim14_5VProduct S D /
      (Real.log D * σ) * errorEnvelope H N D d s *
        (Real.log D) ^ (-Δ) := by positivity
  have he : Real.exp (Real.sqrt Kmax) ≤
      Real.exp (Real.sqrt Kmax) * Real.exp (Real.sqrt K) := by
    nlinarith [Real.exp_pos (Real.sqrt Kmax)]
  calc
    claim14_5VProduct S D *
          (Real.exp (Real.sqrt Kmax) / (Real.log D * σ)) *
          errorEnvelope H N D d s * (Real.log D) ^ (-Δ) =
        Real.exp (Real.sqrt Kmax) *
          (claim14_5VProduct S D / (Real.log D * σ) *
            errorEnvelope H N D d s * (Real.log D) ^ (-Δ)) := by ring
    _ ≤ (Real.exp (Real.sqrt Kmax) * Real.exp (Real.sqrt K)) *
          (claim14_5VProduct S D / (Real.log D * σ) *
            errorEnvelope H N D d s * (Real.log D) ^ (-Δ)) :=
      mul_le_mul_of_nonneg_right he hcommon
    _ = Real.exp (Real.sqrt Kmax) *
        (claim14_5VProduct S D *
          (Real.exp (Real.sqrt K) / (Real.log D * σ)) *
          errorEnvelope H N D d s * (Real.log D) ^ (-Δ)) := by ring

/-- One Claim-14.5 constant works simultaneously for every
`1 ≤ K ≤ Kmax`, every natural quotient and depth, and every `s ≥ 2` in
Case A.  The lower edge `1 ≤ K` is stronger than necessary here (`0 < K`
would suffice), but is the legal source range and avoids any hidden `K < 1`
branch. -/
theorem exists_claim14_5Bound_caseA_boundedK_uniform_in_S
    (H : Section13HatLayers)
    (hH : Section13HatSourceContract H)
    {d Δ C1 Θ Kmax : ℝ}
    (hd : 2 < d) (hC1 : 0 ≤ C1) (hΘ : 0 ≤ Θ) (hKmax : 1 ≤ Kmax) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∀ (S : BoundingSieve) (N D z : ℕ) (K s : ℝ),
        1 ≤ K → K ≤ Kmax → HasDimensionOneLocalProductBound S K →
        2 ≤ D → z = ⌈(D : ℝ) ^ (1 / s)⌉₊ → 2 ≤ s →
        Real.log (D : ℝ) ≤ C1 * K ^ Θ →
        Claim14_5Bound
          (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
          S H N (D : ℝ) (z : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s C145 := by
  let A : ℝ := C1 * Kmax ^ Θ
  let Dmin : ℕ := ⌈Real.exp A⌉₊ + 1
  have hKmax0 : 0 < Kmax := lt_of_lt_of_le zero_lt_one hKmax
  have hrange : ∀ q : ℕ, 2 ≤ q →
      Real.log (q : ℝ) ≤ C1 * Kmax ^ Θ → q < Dmin := by
    intro q hq hlog
    have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
    have hqexp : (q : ℝ) ≤ Real.exp A := by
      rw [← Real.exp_log hq0]
      exact Real.exp_le_exp.mpr (by simpa [A] using hlog)
    have hqceil : q ≤ ⌈Real.exp A⌉₊ := by
      exact_mod_cast hqexp.trans (Nat.le_ceil (Real.exp A))
    simpa [Dmin] using Nat.lt_succ_iff.mpr hqceil
  obtain ⟨C0, hC0, hscalar⟩ :=
    exists_claim145SmallDCaseAScalarComparison_of_fixedDmin_uniform_in_S
      H hH Dmin hd hKmax0 hrange
  let C145 : ℝ := C0 * Real.exp (Real.sqrt Kmax)
  have hC145 : 0 < C145 := by dsimp [C145]; positivity
  refine ⟨C145, hC145, ?_⟩
  intro S N D z K s hK hKK hlocal hD hz hs hsmall
  have hlocal' := hasDimensionOneLocalProductBound_mono_K hlocal hKK
  have hpow : K ^ Θ ≤ Kmax ^ Θ :=
    Real.rpow_le_rpow (by linarith) hKK hΘ
  have hsmall' : Real.log (D : ℝ) ≤ C1 * Kmax ^ Θ :=
    hsmall.trans (mul_le_mul_of_nonneg_left hpow hC1)
  have htail := suzukiLemma14_3_natCeil_uniform_explicit
    (S := S) (N := N) (D := D) (z := z) (s := s) (K := Kmax)
    hlocal' (by omega) hs hz
  have hscalar' := hscalar S hlocal' N D z s hD hz hs hsmall'
  have hupper : suzukiActualT S N D z ≤
      C0 * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) Kmax s := htail.trans hscalar'
  have hscale := claim14_5Scale_upperK_le S H N
    (D := (D : ℝ)) (d := d) (Δ := Δ)
    (σ := sourceSigma (D : ℝ) d) (K := K) (Kmax := Kmax) (s := s)
    (by exact_mod_cast (show 1 < D by omega))
    (sourceSigma_pos_of_nat_two_le hD) (by linarith)
    (hH.toSection13HatContract.positive _ s (by linarith)).le
  have hfinal : suzukiActualT S N D z ≤
      C145 * claim14_5Scale S H N (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K s := hupper.trans (by
    dsimp [C145]
    nlinarith [mul_le_mul_of_nonneg_left hscale hC0.le])
  simpa [Claim14_5Bound] using hfinal

/-- Compatibility specialization of the sieve-uniform bounded-`K` producer. -/
theorem exists_claim14_5Bound_caseA_boundedK
    (S : BoundingSieve) (H : Section13HatLayers)
    (hH : Section13HatSourceContract H)
    {d Δ C1 Θ Kmax : ℝ}
    (hd : 2 < d) (hC1 : 0 ≤ C1) (hΘ : 0 ≤ Θ) (hKmax : 1 ≤ Kmax) :
    ∃ C145 : ℝ, 0 < C145 ∧
      ∀ (N D z : ℕ) (K s : ℝ),
        1 ≤ K → K ≤ Kmax → HasDimensionOneLocalProductBound S K →
        2 ≤ D → z = ⌈(D : ℝ) ^ (1 / s)⌉₊ → 2 ≤ s →
        Real.log (D : ℝ) ≤ C1 * K ^ Θ →
        Claim14_5Bound
          (fun m D' z' => suzukiActualT S m ⌈D'⌉₊ ⌈z'⌉₊)
          S H N (D : ℝ) (z : ℝ) d Δ
            (sourceSigma (D : ℝ) d) K s C145 := by
  obtain ⟨C145, hC145, hall⟩ :=
    exists_claim14_5Bound_caseA_boundedK_uniform_in_S
      H hH hd hC1 hΘ hKmax
  exact ⟨C145, hC145, hall S⟩


end MathlibNt.SieveTheory
