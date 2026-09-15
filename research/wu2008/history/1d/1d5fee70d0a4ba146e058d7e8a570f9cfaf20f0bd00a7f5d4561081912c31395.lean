import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform separation of the sieve cutoff from the source prime

The logarithmic modulus cutoff is at most `sqrt x`, uniformly in every
nonnegative real logarithmic exponent. Its square root is therefore at most
`x^(1/4)`. Any fixed larger real power, with any fixed positive coefficient,
eventually dominates this bound. All thresholds precede the logarithmic
exponent, the modulus, and the source prime.

The dyadic block uses the actual scale `2 * H` but the source bound `H^τ`.
These statements only provide cutoff separation; they do not assert a
distribution estimate or define a source support.
-/

namespace Wu2004MeanValue

open Filter

/-- The elementary fourth-root bound, uniformly over `B ≥ 0`. -/
theorem sqrt_modulus_le_quarter_power {x B : ℝ} {Q : ℕ}
    (hx : 0 ≤ x) (hlog : 1 ≤ Real.log x) (hB : 0 ≤ B)
    (hQ : (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B) :
    Real.sqrt (Q : ℝ) ≤ x ^ (1 / 4 : ℝ) := by
  have hQroot : (Q : ℝ) ≤ Real.sqrt x :=
    hQ.trans (div_le_self (Real.sqrt_nonneg x) (Real.one_le_rpow hlog hB))
  calc
    Real.sqrt (Q : ℝ) ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_le_sqrt hQroot
    _ = x ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
      norm_num

private theorem eventually_quarter_power_le (c τ : ℝ) (hc : 0 < c)
    (hτ : 1 / 4 < τ) :
    ∀ᶠ x : ℝ in atTop, x ^ (1 / 4 : ℝ) ≤ c * x ^ τ := by
  have hgrowth : ∀ᶠ x : ℝ in atTop, 1 / c ≤ x ^ (τ - 1 / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ - 1 / 4)).eventually
      (eventually_ge_atTop (1 / c))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hgrowth] with x hx hpower
  have hxpos : 0 < x := by linarith
  have hcprod : 1 ≤ c * x ^ (τ - 1 / 4) := by
    exact (div_le_iff₀ hc).mp hpower |>.trans_eq (mul_comm _ _)
  have hfactor : x ^ τ = x ^ (1 / 4 : ℝ) * x ^ (τ - 1 / 4) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  rw [hfactor]
  nlinarith [mul_le_mul_of_nonneg_left hcprod
    (Real.rpow_nonneg hxpos.le (1 / 4 : ℝ))]

/-- Tail cutoff separation with a threshold independent of `B`, `Q`, and `x`.
The manuscript's `τ > 1/3` is stronger than the hypothesis needed here. -/
theorem tail_sieve_cutoff_separation (c τ : ℝ) (hc : 0 < c)
    (hτ : 1 / 4 < τ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ B : ℝ, 0 ≤ B → ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      Real.sqrt (Q : ℝ) ≤ c * x ^ τ := by
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_quarter_power_le c τ hc hτ).and hlog)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro x hx B hB Q hQ
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  obtain ⟨hpower, hlogx⟩ := hT x ((le_max_right _ _).trans hx)
  exact (sqrt_modulus_le_quarter_power (by linarith) hlogx hB hQ).trans hpower

/-- Every source prime satisfying the tail's strict lower bound lies above
the sieve cutoff, with the threshold chosen before the source. -/
theorem tail_sieve_cutoff_lt_source (c τ : ℝ) (hc : 0 < c)
    (hτ : 1 / 4 < τ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ B : ℝ, 0 ≤ B → ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ r : ℕ, c * x ^ τ < (r : ℝ) → Real.sqrt (Q : ℝ) < (r : ℝ) := by
  obtain ⟨x₀, hx₀, hbound⟩ := tail_sieve_cutoff_separation c τ hc hτ
  exact ⟨x₀, hx₀, fun x hx B hB Q hQ r hr => (hbound x hx B hB Q hQ).trans_lt hr⟩

/-- Dyadic cutoff separation at scale `2H`, with source power `H^τ`.
In particular, the threshold does not depend on the logarithmic exponent. -/
theorem block_sieve_cutoff_separation (τ : ℝ) (hτ : 1 / 4 < τ) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ B : ℝ, 0 ≤ B → ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      Real.sqrt (Q : ℝ) ≤ H ^ τ := by
  have htwo : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) τ
  obtain ⟨H₀, hH₀, hbound⟩ :=
    tail_sieve_cutoff_separation (1 / (2 : ℝ) ^ τ) τ (by positivity) hτ
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH B hB Q hQ
  have hHpos : 0 < H := by linarith
  have hmain := hbound (2 * H) (by linarith) B hB Q hQ
  have hscale : (1 / (2 : ℝ) ^ τ) * (2 * H) ^ τ = H ^ τ := by
    rw [Real.mul_rpow (by norm_num) hHpos.le]
    field_simp
  simpa only [hscale] using hmain

/-- The block's strict source bound gives strict cutoff separation. -/
theorem block_sieve_cutoff_lt_source (τ : ℝ) (hτ : 1 / 4 < τ) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ B : ℝ, 0 ≤ B → ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      ∀ r : ℕ, H ^ τ < (r : ℝ) → Real.sqrt (Q : ℝ) < (r : ℝ) := by
  obtain ⟨H₀, hH₀, hbound⟩ := block_sieve_cutoff_separation τ hτ
  exact ⟨H₀, hH₀, fun H hH B hB Q hQ r hr => (hbound H hH B hB Q hQ).trans_lt hr⟩

/-- The manuscript exponent `τ_a = (a - 1) / a` lies in `(1/3, 1/2)`. -/
theorem block_source_exponent_range {a : ℝ} (ha : 3 / 2 < a) (ha2 : a < 2) :
    1 / 3 < (a - 1) / a ∧ (a - 1) / a < 1 / 2 := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply (lt_div_iff₀ ha0).mpr
    linarith
  · apply (div_lt_iff₀ ha0).mpr
    linarith

/-- Cutoff separation directly in the manuscript's block parameter `a`. -/
theorem block_sieve_cutoff_lt_source_of_a (a : ℝ) (ha : 3 / 2 < a) (ha2 : a < 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ B : ℝ, 0 ≤ B → ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      ∀ r : ℕ, H ^ ((a - 1) / a) < (r : ℝ) →
      Real.sqrt (Q : ℝ) < (r : ℝ) := by
  have hτ := (block_source_exponent_range ha ha2).1
  exact block_sieve_cutoff_lt_source ((a - 1) / a) (by linarith)

/-- The real sieve level is not rounded before taking its square root. -/
theorem tail_real_sieve_cutoff_separation (c τ : ℝ) (hc : 0 < c)
    (hτ : 1 / 4 < τ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ B : ℝ, 0 ≤ B → ∀ D : ℝ,
      D ≤ Real.sqrt x / Real.log x ^ B →
      Real.sqrt D ≤ c * x ^ τ := by
  have hlog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_quarter_power_le c τ hc hτ).and hlog)
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro x hx B hB D hD
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  obtain ⟨hpower, hlogx⟩ := hT x ((le_max_right _ _).trans hx)
  have hDroot : D ≤ Real.sqrt x :=
    hD.trans (div_le_self (Real.sqrt_nonneg x) (Real.one_le_rpow hlogx hB))
  calc
    Real.sqrt D ≤ Real.sqrt (Real.sqrt x) := Real.sqrt_le_sqrt hDroot
    _ = x ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ x)]
      norm_num
    _ ≤ _ := hpower

theorem block_real_sieve_cutoff_separation (τ : ℝ) (hτ : 1 / 4 < τ) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H →
      ∀ B : ℝ, 0 ≤ B → ∀ D : ℝ,
      D ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      Real.sqrt D ≤ H ^ τ := by
  have htwo : 0 < (2 : ℝ) ^ τ := Real.rpow_pos_of_pos (by norm_num) τ
  obtain ⟨H₀, hH₀, hbound⟩ :=
    tail_real_sieve_cutoff_separation (1 / (2 : ℝ) ^ τ) τ (by positivity) hτ
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH B hB D hD
  have hHpos : 0 < H := by linarith
  have hmain := hbound (2 * H) (by linarith) B hB D hD
  have hscale : (1 / (2 : ℝ) ^ τ) * (2 * H) ^ τ = H ^ τ := by
    rw [Real.mul_rpow (by norm_num) hHpos.le]
    field_simp
  simpa only [hscale] using hmain

end Wu2004MeanValue
