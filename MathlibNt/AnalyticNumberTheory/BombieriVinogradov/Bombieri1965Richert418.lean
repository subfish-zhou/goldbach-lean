

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVFinalNonprincipalOnly

/-!
 # Richert (4.18) normalization and a modern large-sieve producer

Richert's 1969 paper defines

`E*(N,q) = max_{2 <= x <= N} max_{(l,q)=1} |pi(x;q,l) - li(x)/phi(q)|`

and cites Bombieri's Theorem 4 for its mean-value estimate.  This module
formalizes that exact displayed normalization from Richert.

The recovered Bombieri original was inspected separately.  Its Theorem 4 is
stated for the maximal von-Mangoldt error
`psi(z;q,a) - z / phi(q)`, not directly for Richert's prime-counting error.
Thus the declarations below are deliberately labelled as Richert's
partial-summation normalization rather than a verbatim Bombieri statement.

The final theorem is a modern replacement producer.  It uses the project's
large-sieve/Vaughan chain and retains only its genuine low-conductor
nonprincipal primitive Siegel--Walfisz input.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators Topology

noncomputable section

namespace Bombieri1965Richert418

open MathlibNt.SieveTheory

/-- Richert's `li x` normalization in (4.18): the literal integral from `2`
to `x`, with no added constant. -/
noncomputable def logarithmicIntegral (x : ℝ) : ℝ :=
  LiuWeight.liuLogarithmicIntegral 0 x

/-- Richert's ordinary prime-AP error `E(x;q,l)` from (4.18). -/
noncomputable def primeAPError (x q l : ℕ) : ℝ :=
  (BombieriVinogradov.primesInAP x q l : ℝ) -
    logarithmicIntegral x / Nat.totient q

/-- The inner maximum in Richert's `E*`, over canonical reduced residues.
The inserted zero makes the definition total at `q = 0`; for every modulus
in (4.18), the absolute-value family is nonempty and nonnegative. -/
noncomputable def primeAPResidueMaxError (x q : ℕ) : ℝ :=
  (insert 0 ((AnalyticNumberTheory.Sieve.unitResidues q).image
    (fun l => |primeAPError x q l|))).max' (by simp)

/-- Richert's exact outer maximum in (4.18), over integer endpoints
`2 <= x <= N`.  The inserted zero makes the definition total when `N < 2`. -/
noncomputable def primeAPPrefixMaxError (N q : ℕ) : ℝ :=
  (insert 0 ((Finset.Icc 2 N).image
    (fun x => primeAPResidueMaxError x q))).max'
    (by simp)

theorem abs_primeAPError_le_residueMax {x q l : ℕ}
    (hl : l ∈ AnalyticNumberTheory.Sieve.unitResidues q) :
    |primeAPError x q l| ≤ primeAPResidueMaxError x q := by
  unfold primeAPResidueMaxError
  apply Finset.le_max'
  simp only [Finset.mem_insert]
  right
  exact Finset.mem_image.mpr ⟨l, hl, rfl⟩

theorem primeAPResidueMaxError_nonneg (x q : ℕ) :
    0 ≤ primeAPResidueMaxError x q := by
  unfold primeAPResidueMaxError
  exact Finset.le_max' _ 0 (by simp)

theorem primeAPResidueMaxError_le_prefixMax {N x q : ℕ}
    (hx : x ∈ Finset.Icc 2 N) :
    primeAPResidueMaxError x q ≤ primeAPPrefixMaxError N q := by
  unfold primeAPPrefixMaxError
  apply Finset.le_max'
  simp only [Finset.mem_insert]
  right
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem primeAPPrefixMaxError_nonneg (N q : ℕ) :
    0 ≤ primeAPPrefixMaxError N q := by
  unfold primeAPPrefixMaxError
  exact Finset.le_max' _ 0 (by simp)

/-- The exact additive shift between Richert's literal integral and the
project's domination-friendly Standard-BV normalization. -/
theorem primeAPError_eq_standard_add (x q l : ℕ) :
    primeAPError x q l =
      BombieriVinogradov.standardPrimeAPError x q l +
        (2 / Real.log 2) / Nat.totient q := by
  simp only [primeAPError, BombieriVinogradov.standardPrimeAPError,
    logarithmicIntegral, BombieriVinogradov.trueLogarithmicIntegral,
    LiuWeight.liuLogarithmicIntegral]
  ring

private theorem standardPrimeAPMaxError_le_prefixMax_of_le
    {N x q : ℕ} (hx : x ≤ N) :
    BombieriVinogradov.standardPrimeAPMaxError x q ≤
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
  unfold BombieriVinogradov.standardPrimeAPPrefixMaxError
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hx), rfl⟩

/-- Changing from the project's Standard-BV normalization to Richert's literal
integral costs exactly one positive constant divided by `phi(q)`. -/
theorem primeAPResidueMaxError_le_standard_add
    (x q : ℕ) (hq : 1 ≤ q) :
    primeAPResidueMaxError x q ≤
      BombieriVinogradov.standardPrimeAPMaxError x q +
        (2 / Real.log 2) / Nat.totient q := by
  unfold primeAPResidueMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨l, hl, rfl⟩
  · exact add_nonneg
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg x q) (by positivity)
  · rw [primeAPError_eq_standard_add]
    have hqPos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
    have hshift : 0 ≤ (2 / Real.log 2) / (q.totient : ℝ) := by
      exact div_nonneg (by positivity)
        (by exact_mod_cast (Nat.totient_pos.mpr hqPos).le)
    calc
      |BombieriVinogradov.standardPrimeAPError x q l +
          (2 / Real.log 2) / Nat.totient q| ≤
          |BombieriVinogradov.standardPrimeAPError x q l| +
            |(2 / Real.log 2) / Nat.totient q| := abs_add_le _ _
      _ = |BombieriVinogradov.standardPrimeAPError x q l| +
            (2 / Real.log 2) / Nat.totient q := by
          rw [abs_of_nonneg hshift]
      _ ≤ BombieriVinogradov.standardPrimeAPMaxError x q +
            (2 / Real.log 2) / Nat.totient q := by
          exact add_le_add
            (BombieriVinogradov.abs_standardPrimeAPError_le_max hl) (le_refl _)

/-- Richert's exact nested maximum is bounded by the existing Standard-BV
prefix maximum plus the explicit normalization shift. -/
theorem primeAPPrefixMaxError_le_standard_add
    (N q : ℕ) (hq : 1 ≤ q) :
    primeAPPrefixMaxError N q ≤
      BombieriVinogradov.standardPrimeAPPrefixMaxError N q +
        (2 / Real.log 2) / Nat.totient q := by
  unfold primeAPPrefixMaxError
  apply Finset.max'_le
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_image] at hz
  rcases hz with rfl | ⟨x, hx, rfl⟩
  · exact add_nonneg
      (BombieriVinogradov.standardPrimeAPPrefixMaxError_nonneg N q)
      (by positivity)
  · exact (primeAPResidueMaxError_le_standard_add x q hq).trans
      (add_le_add
        (standardPrimeAPMaxError_le_prefixMax_of_le
          (Finset.mem_Icc.mp hx).2) (le_refl _))

/-- Summed normalization comparison on an arbitrary initial modulus range. -/
theorem sum_primeAPPrefixMaxError_le_standard_add (N Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, primeAPPrefixMaxError N q) ≤
      (∑ q ∈ Finset.Icc 1 Q,
        BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
        (Q : ℝ) * (2 / Real.log 2) := by
  calc
    (∑ q ∈ Finset.Icc 1 Q, primeAPPrefixMaxError N q) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          (BombieriVinogradov.standardPrimeAPPrefixMaxError N q +
            (2 / Real.log 2) / Nat.totient q) := by
      exact Finset.sum_le_sum fun q hq =>
        primeAPPrefixMaxError_le_standard_add N q (Finset.mem_Icc.mp hq).1
    _ = (∑ q ∈ Finset.Icc 1 Q,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
          ∑ q ∈ Finset.Icc 1 Q, (2 / Real.log 2) / Nat.totient q := by
      simp only [Finset.sum_add_distrib]
    _ ≤ (∑ q ∈ Finset.Icc 1 Q,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
          ∑ _q ∈ Finset.Icc 1 Q, (2 / Real.log 2) := by
      apply add_le_add (le_refl _)
      exact Finset.sum_le_sum fun q hq => by
        have hqPos : 0 < q :=
          lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1
        have hphiNat : 1 ≤ q.totient :=
          Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hqPos)
        have hphi : (1 : ℝ) ≤ q.totient := by exact_mod_cast hphiNat
        exact div_le_self (by positivity) hphi
    _ = (∑ q ∈ Finset.Icc 1 Q,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
          (Q : ℝ) * (2 / Real.log 2) := by simp

private theorem one_le_log_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    1 ≤ Real.log (N : ℝ) := by
  have he1 : Real.exp 1 < (3 : ℝ) :=
    Real.exp_one_lt_d9.trans (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
    (he1.trans_le (by exact_mod_cast hN)) |>.le

private theorem panModulusCutoff_add_one_le
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) :
    LiuWeight.panModulusCutoff N (B + 1) ≤
      LiuWeight.panModulusCutoff N B := by
  have hlog : 1 ≤ Real.log (N : ℝ) := one_le_log_of_three_le hN
  have hlogPos : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hpow :
      Real.log (N : ℝ) ^ B ≤ Real.log (N : ℝ) ^ (B + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
  unfold LiuWeight.panModulusCutoff
  apply Nat.floor_mono
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_pos_of_pos hlogPos B) hpow

private theorem panModulusCutoff_cast_le_sqrt
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    (LiuWeight.panModulusCutoff N B : ℝ) ≤ Real.sqrt N := by
  have hlog : 1 ≤ Real.log (N : ℝ) := one_le_log_of_three_le hN
  have hden : 1 ≤ Real.log (N : ℝ) ^ B :=
    Real.one_le_rpow hlog hB
  unfold LiuWeight.panModulusCutoff
  calc
    ((Nat.floor ((N : ℝ) ^ (1 / 2 : ℝ) /
        Real.log N ^ B) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B :=
      Nat.floor_le (by positivity)
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      div_le_self (Real.rpow_nonneg (by positivity) _) hden
    _ = Real.sqrt N := by rw [Real.sqrt_eq_rpow]

private theorem eventually_log_rpow_le_sqrt (U : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ U ≤ Real.sqrt N := by
  have hreal :
      ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ U ≤ Real.sqrt x := by
    have hbound :=
      (isLittleO_log_rpow_rpow_atTop U
        (show 0 < (1 / 2 : ℝ) by norm_num)).bound
        (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) U),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) (1 / 2 : ℝ)),
      one_mul] at hx
    simpa [Real.sqrt_eq_rpow] using hx
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- The exact proposition displayed as Richert (4.18), with the Vinogradov
symbol expanded into an explicit positive multiplicative constant. -/
def Richert418BombieriVinogradov : Prop :=
  ∀ U : ℝ, 0 < U →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
        ∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N C),
          primeAPPrefixMaxError N q ≤
            K * (N : ℝ) / Real.log N ^ U

/-- Normalization adapter from the project's Standard-BV endpoint to the exact
Richert (4.18) statement.  The exponent is increased by one to remain positive;
the smaller modulus range and the fixed `li` shift are paid explicitly. -/
theorem richert418_of_standardBombieriVinogradov
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    Richert418BombieriVinogradov := by
  intro U hU
  obtain ⟨B, hB, K, hK, hstandard⟩ := hBV U hU
  let C : ℝ := B + 1
  let kappa : ℝ := 2 / Real.log 2
  refine ⟨C, by dsimp [C]; linarith, K + kappa, by
    dsimp [kappa]
    positivity, ?_⟩
  filter_upwards [hstandard, eventually_log_rpow_le_sqrt U,
    eventually_ge_atTop (3 : ℕ)] with N hstandardN hlogSqrt hN
  intro hN2
  let Qsmall := LiuWeight.panModulusCutoff N C
  let Qlarge := LiuWeight.panModulusCutoff N B
  have hQ : Qsmall ≤ Qlarge := by
    dsimp [Qsmall, Qlarge, C]
    exact panModulusCutoff_add_one_le N B hN
  have hstandardSmall :
      (∑ q ∈ Finset.Icc 1 Qsmall,
        BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        ∑ q ∈ Finset.Icc 1 Qlarge,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right hQ
    · intro q hq hnot
      exact BombieriVinogradov.standardPrimeAPPrefixMaxError_nonneg N q
  have hstandardBound :
      (∑ q ∈ Finset.Icc 1 Qlarge,
        BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        K * (N : ℝ) / Real.log N ^ U := by
    exact hstandardN hN2
  have hcut :
      (Qsmall : ℝ) ≤ Real.sqrt N := by
    dsimp [Qsmall, C]
    exact panModulusCutoff_cast_le_sqrt N (B + 1) hN (by linarith)
  have hlogPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrtPay :
      Real.sqrt N ≤ (N : ℝ) / Real.log N ^ U := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogPos U)).2
    calc
      Real.sqrt N * Real.log N ^ U ≤ Real.sqrt N * Real.sqrt N :=
        mul_le_mul_of_nonneg_left hlogSqrt (Real.sqrt_nonneg _)
      _ = (N : ℝ) := Real.mul_self_sqrt (by positivity)
  have hkappaNonneg : 0 ≤ kappa := by
    dsimp [kappa]
    positivity
  have hkappaPay :
      (Qsmall : ℝ) * kappa ≤
        kappa * (N : ℝ) / Real.log N ^ U := by
    calc
      (Qsmall : ℝ) * kappa ≤ Real.sqrt N * kappa := by gcongr
      _ ≤ ((N : ℝ) / Real.log N ^ U) * kappa := by gcongr
      _ = kappa * (N : ℝ) / Real.log N ^ U := by ring
  calc
    (∑ q ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N C),
        primeAPPrefixMaxError N q) ≤
        (∑ q ∈ Finset.Icc 1 Qsmall,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
          (Qsmall : ℝ) * kappa := by
      simpa [Qsmall, kappa] using
        sum_primeAPPrefixMaxError_le_standard_add N Qsmall
    _ ≤ (∑ q ∈ Finset.Icc 1 Qlarge,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N q) +
          (Qsmall : ℝ) * kappa :=
      add_le_add hstandardSmall (le_refl _)
    _ ≤ K * (N : ℝ) / Real.log N ^ U +
          kappa * (N : ℝ) / Real.log N ^ U :=
      add_le_add hstandardBound hkappaPay
    _ = (K + kappa) * (N : ℝ) / Real.log N ^ U := by ring

/-- Modern large-sieve producer for Richert's exact (4.18) endpoint.

This is not presented as a transcription of Bombieri 1965.  Its sole
hypothesis is the pointwise nonprincipal primitive Siegel--Walfisz input; the
high-conductor Vaughan and large-sieve work is supplied by the checked modern
producer chain. -/
theorem richert418_of_nonprincipalPrimitivePsi
    (hSW : NonprincipalPrimitivePsiSiegelWalfiszSource) :
    Richert418BombieriVinogradov :=
  richert418_of_standardBombieriVinogradov
    (standardBombieriVinogradov_of_nonprincipalPrimitivePsi hSW)

end Bombieri1965Richert418

end

end AnalyticNumberTheory.LargeSieve
