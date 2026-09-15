import MathlibNt.Wu2008DoubleSieve.NinthErrorPaymentFinite
import MathlibNt.Wu2008DoubleSieve.BoxMassUniform

/-!
# Paying the actual ninth R2 and small-output errors

The existing logarithmic-power budget is used directly against N/log^2 N,
without any boxTheta wrapper or artificial source box.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem ninth_power_log_error_budget (m : ℕ) {C α ε : ℝ}
    (hC : 0 < C) (hα : 0 < α) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      C * N * log N ^ m / (N : ℝ) ^ α ≤ ε * N / log N ^ 2 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget (m + 2) (show 0 < C / ε by positivity) hα)
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN
  have hN512 : 512 ≤ N := (le_max_right _ _).trans hN
  have hlog : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ C * N * log N ^ m / ((C / ε) * log N ^ (m + 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (hT N ((le_max_left _ _).trans hN))
    _ = ε * N / log N ^ 2 := by
      rw [pow_add]
      field_simp

/-- The threshold is even uniform over all source delta in (0,1/2).
The constant in the finite Euler estimate is absorbed only after it has
been obtained from the accepted producer. -/
theorem ninthSieveR2_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ : ℝ,
      0 < δ → δ < 1 / 2 →
      ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
        (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤ ε * N / log N ^ 2 := by
  obtain ⟨C, hC, hfinite⟩ := ninthSieveR2_source_finite_bound
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 5
    (show 0 < 2 * C / log 2 by positivity)
    (show 0 < ninthProfileK2 by norm_num [ninthProfileK2]) hε
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlogT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN δ hδ hδhi
  have hN1 : T1 ≤ N := (le_max_left _ _).trans hN
  have hlog1 := hlogT N ((le_max_right _ _).trans hN)
  have hN512 := hT1.trans hN1
  have hw : 0 < ninthProfileW N := rpow_pos_of_pos (by positivity) _
  calc
    _ ≤ C * N * ((1 + log N) * log N ^ 4 / (ninthProfileW N * log 2)) :=
      hfinite N hN512 δ hδ hδhi
    _ ≤ C * N * ((2 * log N) * log N ^ 4 / (ninthProfileW N * log 2)) := by
      gcongr
      linarith
    _ = (2 * C / log 2) * N * log N ^ 5 / (N : ℝ) ^ ninthProfileK2 := by
      unfold ninthProfileW
      ring
    _ ≤ _ := hpay N hN1

theorem ninthSmallOutput_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ δ : ℝ, 0 < δ →
      ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
        ε * N / log N ^ 2 := by
  have hk : 0 < ninthProfileK2 := by norm_num [ninthProfileK2]
  obtain ⟨T, hT, hpay⟩ := ninth_power_log_error_budget 0
    (show 0 < 2 / ninthProfileK2 ^ 2 by positivity)
    (show (0 : ℝ) < 3 / 4 by norm_num) hε
  refine ⟨T, hT, ?_⟩
  intro N hN δ hδ
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (2 / ninthProfileK2 ^ 2) * (N : ℝ) ^ (1 / 4 : ℝ) :=
      ninthSmallOutputBudget_source_le (hT.trans hN) hδ
    _ = (2 / ninthProfileK2 ^ 2) * N * log N ^ (0 : ℕ) /
        (N : ℝ) ^ (3 / 4 : ℝ) := by
      rw [show (1 / 4 : ℝ) = 1 - 3 / 4 by norm_num,
        rpow_sub hNR, rpow_one, pow_zero]
      ring
    _ ≤ _ := hpay N hN

/-- Both actual errors are paid, on the literal source moduli and cutoff.
Evenness is not needed; the threshold precedes N. -/
theorem ninthR2_smallOutput_error_paid {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ninthSieveR2 N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1)
          (sqrt ((N : ℝ) ^ (1 / 2 - δ))) +
        ninthSmallOutputBudget (sqrt ((N : ℝ) ^ (1 / 2 - δ))) ≤
          ε * N / log N ^ 2 := by
  obtain ⟨T1, hT1, hR2⟩ := ninthSieveR2_error_paid (show 0 < ε / 2 by positivity)
  obtain ⟨T2, _, hsmall⟩ := ninthSmallOutput_error_paid (show 0 < ε / 2 by positivity)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN
  have h1 := hR2 N ((le_max_left _ _).trans hN) δ hδ hδhi
  have h2 := hsmall N ((le_max_right _ _).trans hN) δ hδ
  calc
    _ ≤ ε / 2 * N / log N ^ 2 + ε / 2 * N / log N ^ 2 := add_le_add h1 h2
    _ = _ := by ring

/-- An unknown positive constant at log exponent three is paid by a
threshold, not identified with the requested epsilon. -/
theorem ninth_log_cube_error_budget {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      C * N / log N ^ (3 : ℕ) ≤ ε * N / log N ^ (2 : ℕ) := by
  have hlogTop : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (C / ε)))
  refine ⟨max T 512, le_max_right _ _, ?_⟩
  intro N hN
  have hlog : 0 < log (N : ℝ) :=
    (div_pos hC hε).trans_le (hT N ((le_max_left _ _).trans hN))
  have hCle : C ≤ ε * log N := by
    have h := (div_le_iff₀ hε).mp (hT N ((le_max_left _ _).trans hN))
    nlinarith
  calc
    C * N / log N ^ (3 : ℕ) ≤ (ε * log N) * N / log N ^ (3 : ℕ) := by
      gcongr
    _ = ε * N / log N ^ (2 : ℕ) := by field_simp

end Wu2008DoubleSieve
