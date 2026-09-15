import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentAsymptotic

/-!
# The actual ninth upper sieve with all additive errors paid

The accepted R1 estimate is used at log exponent three, then its unknown
constant is absorbed by a further threshold. The main coefficient still
multiplies actual X9; no main-integral estimate is asserted.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical
open MathlibNt.SieveTheory.SingularSeries

/-- Actual R1, with an arbitrarily small log-square budget, uniformly in Z. -/
theorem ninthSieveR1_error_paid {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z ≤
        ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨C, hC, T1, hT1, hR1⟩ := ninthSieveR1_source_bound 3 (by norm_num) hδ
  obtain ⟨T2, _, hpay⟩ := ninth_log_cube_error_budget hC hε
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN Z
  have h := hR1 N ((le_max_left _ _).trans hN) Z
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at h
  exact h.trans (hpay N ((le_max_right _ _).trans hN))

/-- Every additive error from the physical sieve is paid. There is no
evenness hypothesis in this error estimate. -/
theorem ninth_all_sieve_errors_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
          ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨T1, hT1, hR1⟩ := ninthSieveR1_error_paid hδ (show 0 < ε / 2 by positivity)
  obtain ⟨T2, _, herrors⟩ :=
    ninthR2_smallOutput_error_paid hδ hδhi (show 0 < ε / 2 by positivity)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN
  have h1 := hR1 N ((le_max_left _ _).trans hN) (sqrt ((N : ℝ) ^ (1 / 2 - δ)))
  have h2 := herrors N ((le_max_right _ _).trans hN)
  calc
    _ = ninthSieveR1 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        (ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
          ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ)))) := by ring
    _ ≤ ε / 2 * N / log N ^ 2 + ε / 2 * N / log N ^ 2 := add_le_add h1 h2
    _ = _ := by ring

/-- The concrete error-paid T9 theorem. The source density factor is
literal, and X9 remains the actual prime-profile mass. -/
theorem T9_upper_source_error_paid {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((T9 N (ninthProfileW N) (ninthProfileU N)).card : ℝ) ≤
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
          (8 / (1 - 2 * δ))) * wuSingularSeries N / log N) * X9 N +
        ε * N / log N ^ (2 : ℕ) := by
  obtain ⟨C, hC, T1, hT1, hupper⟩ :=
    T9_upper_source_with_R1 3 (by norm_num) hδ hδhi hρ
  obtain ⟨T2, _, hR1pay⟩ := ninth_log_cube_error_budget hC (show 0 < ε / 2 by positivity)
  obtain ⟨T3, _, hother⟩ :=
    ninthR2_smallOutput_error_paid hδ hδhi (show 0 < ε / 2 by positivity)
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN1 := (le_max_left T1 _).trans hN
  have hN2 := (le_max_left T2 T3).trans ((le_max_right T1 _).trans hN)
  have hN3 := (le_max_right T2 T3).trans ((le_max_right T1 _).trans hN)
  have hu := hupper N hN1 he
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_natCast] at hu
  have h1 := hR1pay N hN2
  have h2 := hother N hN3
  have herr :
      C * N / log N ^ (3 : ℕ) +
        (ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
          ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ)))) ≤
        ε * N / log N ^ (2 : ℕ) := by
    calc
      _ ≤ ε / 2 * N / log N ^ 2 + ε / 2 * N / log N ^ 2 := add_le_add h1 h2
      _ = _ := by ring
  linarith

end Wu2008DoubleSieve
