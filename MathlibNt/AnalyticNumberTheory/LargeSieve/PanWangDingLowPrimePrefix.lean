import MathlibNt.AnalyticNumberTheory.LargeSieve.FourFactorUnconditionalEndpoints
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCorrection
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEarlySourceReduction

/-! Actual prime-character prefixes for the nonprincipal low-conductor lane.
No assertion is made about the unpunctured `panIymLow` (which contains q = 1).
Only finite Abel summation and the existing prime-power correction are used. -/
namespace AnalyticNumberTheory.LargeSieve.PanLow
open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology
open MathlibNt.SieveTheory.LiuWeight
noncomputable section

/-- The literal unweighted prime character sum. -/
def primePrefix {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ range (y + 1), if n.Prime then χ (n : ZMod q) else 0

/-- Finite complex Abel identity; the production real kernel is unchanged. -/
theorem complex_abel (c : ℕ → ℂ) (w : ℕ → ℝ) (y : ℕ) :
    (∑ n ∈ range (y + 1), (w n : ℂ) * c n) =
      (w y : ℂ) * (∑ n ∈ range (y + 1), c n) +
        ∑ n ∈ range y, ((w n - w (n + 1) : ℝ) : ℂ) *
          (∑ k ∈ range (n + 1), c k) := by
  induction y with
  | zero => simp
  | succ y ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- Bounded total variation of the already proved reciprocal-log kernel. -/
theorem norm_abel_le (c : ℕ → ℂ) (y : ℕ) (M : ℝ)
    (h : ∀ n ≤ y, ‖∑ k ∈ range (n + 1), c k‖ ≤ M) :
    ‖∑ n ∈ range (y + 1), (reciprocalLogWeight n : ℂ) * c n‖ ≤
      discreteAbelAmplifier y * M := by
  rw [complex_abel]
  calc
    _ ≤ ‖(reciprocalLogWeight y : ℂ) * (∑ n ∈ range (y + 1), c n)‖ +
        ∑ n ∈ range y, ‖((reciprocalLogWeight n - reciprocalLogWeight (n + 1) : ℝ) : ℂ) *
          (∑ k ∈ range (n + 1), c k)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ |reciprocalLogWeight y| * M +
        ∑ n ∈ range y, |reciprocalLogWeight n - reciprocalLogWeight (n + 1)| * M := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left (h y le_rfl) (abs_nonneg _))
        (sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
          (h n (Nat.le_of_lt (mem_range.mp hn))) (abs_nonneg _))
    _ = discreteAbelAmplifier y * M := by
      simp only [discreteAbelAmplifier, add_mul, sum_mul]

private theorem weight_lambda (n : ℕ) :
    reciprocalLogWeight n * ArithmeticFunction.vonMangoldt n =
      ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) := by
  by_cases hn : 2 ≤ n
  · simp [reciprocalLogWeight, hn, div_eq_mul_inv, mul_comm]
  · have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl <;> simp [reciprocalLogWeight]

/-- Exact removal of the nonprime von Mangoldt terms after Abel. -/
theorem primePrefix_eq_abel_sub_correction {q : ℕ}
    (χ : DirichletCharacter ℂ q) (y : ℕ) :
    primePrefix χ y =
      (∑ n ∈ range (y + 1), (reciprocalLogWeight n : ℂ) *
        (lambdaNatCoeff n * χ (n : ZMod q))) -
      ∑ n ∈ range (y + 1),
        ((if n.Prime then 0 else ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ) *
          χ (n : ZMod q) := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  have hw : (reciprocalLogWeight n : ℂ) * lambdaNatCoeff n =
      ((ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ) := by
    unfold lambdaNatCoeff
    exact_mod_cast weight_lambda n
  rw [← mul_assoc, hw]
  by_cases hp : n.Prime
  · have hl : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp, hl]
  · simp [hp]

/-- The twisted correction is dominated by the existing untwisted one. -/
theorem norm_correction_le {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℕ) :
    ‖∑ n ∈ range (y + 1),
        ((if n.Prime then 0 else ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) : ℂ) *
          χ (n : ZMod q)‖ ≤ globalPrimePowerCorrection y := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  have hnon : 0 ≤ (if n.Prime then 0 else
      ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) : ℝ) := by
    split_ifs <;> positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon]
  exact (mul_le_mul_of_nonneg_left (χ.norm_le_one _) hnon).trans_eq (mul_one _)

/-- Pointwise lambda prefix bounded by the established primitive maximum. -/
theorem lambda_le_primitive {N y q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖lambdaCharacterPrefix y q χ.1‖ ≤ primitivePrefixAmplitude vonMangoldtIntegerCoeff N q χ := by
  have hs := norm_lambdaCharacterPrefix_sq_le_characterPrefixMaxSquare N y q hy χ.1
  have he : characterPrefixMaxSquare χ.1 vonMangoldtIntegerCoeff 0 N =
      primitiveCharacterPrefixMaxSquare vonMangoldtIntegerCoeff 0 N q χ := rfl
  rw [he, ← primitivePrefixAmplitude_sq] at hs
  nlinarith [primitivePrefixAmplitude_nonneg vonMangoldtIntegerCoeff N q χ,
    norm_nonneg (lambdaCharacterPrefix y q χ.1)]

/-- Finite psi-to-prime bridge: no AP or BV premise. -/
theorem primePrefix_le_psi_add_correction {N y q : ℕ}
    (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    ‖primePrefix χ.1 y‖ ≤
      (2 * (Real.log 2)⁻¹) * primitivePrefixAmplitude vonMangoldtIntegerCoeff N q χ +
        globalPrimePowerCorrection y := by
  rw [primePrefix_eq_abel_sub_correction]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (norm_correction_le χ.1 y))
  refine (norm_abel_le (fun n => lambdaNatCoeff n * χ.1 (n : ZMod q)) y _
    (fun n hn => lambda_le_primitive (hn.trans hy) χ)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (primitivePrefixAmplitude_nonneg _ _ _ _)
  exact (show discreteAbelAmplifier y ≤ discreteAbelAmplifierPrefixMax y from
    Finset.le_max' _ _ (mem_image.mpr ⟨y, mem_range.mpr (Nat.lt_succ_self y), rfl⟩)).trans
      (discreteAbelAmplifierPrefixMax_le_two_inv_log_two y)

/-- Elementary parameter bridge, obtained from Mathlib's log-versus-power limit. -/
theorem eventually_sqrt_le_log_budget (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, Real.sqrt (N : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ D := by
  have h := (isLittleO_log_rpow_rpow_atTop (D : ℝ)
    (show (0 : ℝ) < 1 / 2 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlog : Real.log (N : ℝ) ^ D ≤ Real.sqrt (N : ℝ) := by
    simpa only [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hl.le D), abs_of_nonneg (Real.sqrt_nonneg _),
      one_mul] using hN
  apply (le_div_iff₀ (pow_pos hl D)).2
  exact (mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg _)).trans_eq
    (Real.mul_self_sqrt (by positivity))

/-- Unconditional SW for actual unweighted prime prefixes.  Constants and the
threshold precede the modulus, character and prefix.  No prime-BV hypothesis. -/
theorem primePrefix_siegelWalfisz (C D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, 2 ≤ N →
      ∀ q ∈ Icc 2 (logConductorThreshold N C), ∀ χ : PrimitiveCharacter q,
        χ.1 ≠ 1 → ∀ y ≤ N,
          ‖primePrefix χ.1 y‖ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  obtain ⟨K, hK, hSW⟩ := fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource C D
  obtain ⟨J, hJ, hPP⟩ := exists_globalPrimePowerCorrection_le_sqrt
  let B : ℝ := 2 * (Real.log 2)⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B * K + J, by positivity, ?_⟩
  filter_upwards [hSW, eventually_sqrt_le_log_budget D] with N hSWN hpay
  intro hN q hq χ hχ y hy
  have hPPN : globalPrimePowerCorrection y ≤ J * ((N : ℝ) / Real.log (N : ℝ) ^ D) :=
    (hPP y).trans (mul_le_mul_of_nonneg_left
      ((Real.sqrt_le_sqrt (by exact_mod_cast hy)).trans hpay) hJ)
  calc
    ‖primePrefix χ.1 y‖ ≤ B * primitivePrefixAmplitude vonMangoldtIntegerCoeff N q χ +
        globalPrimePowerCorrection y := primePrefix_le_psi_add_correction hy χ
    _ ≤ B * (K * (N : ℝ) / Real.log (N : ℝ) ^ D) +
        J * ((N : ℝ) / Real.log (N : ℝ) ^ D) :=
      add_le_add (mul_le_mul_of_nonneg_left (hSWN hN q hq χ hχ) hB.le) hPPN
    _ = (B * K + J) * (N : ℝ) / Real.log (N : ℝ) ^ D := by ring

/-- The same endpoint with an arbitrary fixed real logarithmic conductor exponent. -/
theorem primePrefix_siegelWalfisz_real_conductor (b : ℝ) (D : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
        ∀ χ : PrimitiveCharacter q, χ.1 ≠ 1 →
          ‖primePrefix χ.1 N‖ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ D := by
  obtain ⟨K, hK, hSW⟩ := primePrefix_siegelWalfisz ⌈b⌉₊ D
  refine ⟨K, hK, ?_⟩
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hSW, hlog, eventually_ge_atTop (2 : ℕ)] with N hS hL hN
  intro q hq hqb χ hχ
  apply hS hN q (mem_Icc.mpr ⟨hq, ?_⟩) χ hχ N le_rfl
  apply Nat.le_floor
  exact hqb.trans (by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil b))

/-- Endpoint-only version with real saving exponent, in the paper's notation. -/
theorem primePrefix_siegelWalfisz_endpoint (b A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
        ∀ χ : PrimitiveCharacter q, χ.1 ≠ 1 →
          ‖primePrefix χ.1 N‖ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  obtain ⟨K, hK, hSW⟩ := primePrefix_siegelWalfisz_real_conductor b ⌈A⌉₊
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hbound : ∀ᶠ N : ℕ in atTop,
      ∀ q : ℕ, 2 ≤ q → (q : ℝ) ≤ Real.log (N : ℝ) ^ b →
        ∀ χ : PrimitiveCharacter q, χ.1 ≠ 1 →
          ‖primePrefix χ.1 N‖ ≤ K * (N : ℝ) / Real.log (N : ℝ) ^ A := by
    filter_upwards [hSW, hlog] with N hS hL
    intro q hq hqb χ hχ
    refine (hS q hq hqb χ hχ).trans ?_
    apply div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL) A)
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil A)
  exact ⟨K, hK, eventually_atTop.mp hbound⟩

end
end AnalyticNumberTheory.LargeSieve.PanLow