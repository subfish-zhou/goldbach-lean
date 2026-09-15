import Wu18938Campaign.M6.LowOutputConsumer
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Finset Filter
open scoped Classical

namespace Wu18938Campaign.M6
open U8Literal

theorem sqrt_error_log_payment (A : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 * Real.sqrt N + 2 ≤ σ * (N : ℝ) / (Real.log N) ^ A := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (A : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).def (show 0 < σ / 4 by positivity)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hsmall
  refine ⟨max 2 ⌈T⌉₊, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log N := Real.log_pos hNr
  have hNT : T ≤ (N : ℝ) :=
    (Nat.le_ceil T).trans (by exact_mod_cast (le_max_right 2 ⌈T⌉₊).trans hN)
  have hb : (Real.log N) ^ A ≤ (σ / 4) * Real.sqrt N := by
    have hh := hT (N : ℝ) hNT
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog.le A),
      ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg (N : ℝ))] using hh
  have hs : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hNr.le
  calc
    2 * Real.sqrt N + 2 ≤ 4 * Real.sqrt N := by linarith
    _ ≤ σ * (N : ℝ) / (Real.log N) ^ A := by
      apply (le_div_iff₀ (pow_pos hlog A)).mpr
      have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * Real.sqrt (N : ℝ) by positivity)
      nlinarith [Real.sq_sqrt hN0]

theorem lowRectangle_log_paid (A : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ρ : ℝ, 1 < ρ →
      ∀ k : Key, ∀ z : ℝ, z ≤ Real.sqrt N →
        lowRectangle N ρ k z ≤ σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨N₀, hN₀, hpay⟩ := sqrt_error_log_payment A hσ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ρ hρ k z hz
  exact (lowRectangle_sqrt_upper (by omega) hρ k hz).trans (hpay N hN)

theorem labels_le_rectangle_log_paid (A : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ρ : ℝ, 1 < ρ →
      ∀ k : Key, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) < Real.sqrt N) →
      ∀ S : Finset Label,
      (∀ x ∈ S, x.1.1 ∈ shortPrimeSupport N ρ k ∧
        (x.1.2, x.2) ∈ longLabels N ρ k ∧ x.1.1.Prime ∧ x.1.1.Coprime N ∧
        (output N x.1.1 (x.1.2 * x.2)).Prime) →
      (S.card : ℝ) ≤ rectangleSifted N ρ k P + σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨N₀, hN₀, hpay⟩ := sqrt_error_log_payment A hσ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN ρ hρ k P hP hcut S hS
  have hcount := labels_le_rectangle_add_sqrt (by omega) hρ hP hcut S hS
  have herr := hpay N hN
  linarith

end Wu18938Campaign.M6
