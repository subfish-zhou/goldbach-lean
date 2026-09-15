import MathlibNt.Wu2008DoubleSieve.InclusiveRoughUniform

open Finset Real LiLiuPrereqBuchstab

namespace Wu2008DoubleSieve.InclusiveRoughUniform

/-- A positive natural denominator never enlarges the global size scale. -/
theorem quotient_le (N D : ℕ) (hD : 0 < D) : (N : ℝ) / D ≤ N := by
  exact div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)

/-- Exact natural gate for the unit atom. -/
theorem unit_gate_iff (N D : ℕ) (hD : 0 < D) :
    1 ≤ (N : ℝ) / D ↔ D ≤ N := by
  rw [one_le_div (by exact_mod_cast hD : (0 : ℝ) < D)]
  exact_mod_cast Iff.rfl

/-- Exact natural product gate, with the equality endpoint included. -/
theorem nonunit_gate_iff (N D q : ℕ) (hD : 0 < D) :
    (q : ℝ) ≤ (N : ℝ) / D ↔ D * q ≤ N := by
  rw [le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)]
  simpa only [mul_comm] using
    (show (q : ℝ) * D ≤ N ↔ q * D ≤ N by exact_mod_cast Iff.rfl)

/-- The source scale itself supplies positive logarithms, without a product gate. -/
theorem cutoff_one_lt {η : ℝ} (hη : 0 < η) {N q : ℕ}
    (hN : 4 ≤ N) (hq : (N : ℝ) ^ η ≤ q) : 1 < (q : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (Real.one_lt_rpow hN1 hη).trans_le hq

theorem cutoff_log_pos {η : ℝ} (hη : 0 < η) {N q : ℕ}
    (hN : 4 ≤ N) (hq : (N : ℝ) ^ η ≤ q) : 0 < log (q : ℝ) := by
  exact log_pos (cutoff_one_lt hη hN hq)

/-- A denominator above N leaves no positive residual integer. -/
theorem product_count_zero {N D q : ℕ} (hD : 0 < D) (hND : N < D) :
    (roughNumbers ((N : ℝ) / D) q).card = 0 := by
  have hx : (N : ℝ) / D < 1 :=
    lt_of_not_ge (fun h => (Nat.not_le_of_lt hND) ((unit_gate_iff N D hD).mp h))
  rw [roughNumbers_empty_of_lt_one hx, card_empty]

/-- Failing the nonunit gate does not remove a unit whose own gate holds. -/
theorem product_count_eq_unit {N D q : ℕ} (hD : 0 < D) (hq : 1 ≤ q)
    (hgate : ¬ D * q ≤ N) :
    (roughNumbers ((N : ℝ) / D) q).card = if D ≤ N then 1 else 0 := by
  have hx : (N : ℝ) / D < q :=
    lt_of_not_ge (fun h => hgate ((nonunit_gate_iff N D q hD).mp h))
  simpa only [unit_gate_iff N D hD] using
    count_eq_unit_of_lt (by exact_mod_cast hq : (1 : ℝ) ≤ q) hx

/-- Natural-product specialization on the full physical domain: no D*q <= N premise.
The threshold is selected before N, D and q; tau never multiplies the unit. -/
theorem uniform_product_upper {η τ : ℝ} (hη : 0 < η) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ D q : ℕ,
      0 < D → (N : ℝ) ^ η ≤ q →
      ((roughNumbers ((N : ℝ) / D) q).card : ℝ) ≤
        (if D ≤ N then 1 else 0) +
        (if D * q ≤ N then
          (buchstab (log ((N : ℝ) / D) / log q) + τ) * ((N : ℝ) / D) / log q
         else 0) := by
  obtain ⟨T, hT, hscalar⟩ := uniform_upper hη hτ
  refine ⟨T, hT, ?_⟩
  intro N hN D q hD hq
  have h := hscalar N hN ((N : ℝ) / D) q (quotient_le N D hD) hq
  simpa only [unit_gate_iff N D hD, nonunit_gate_iff N D q hD] using h

end Wu2008DoubleSieve.InclusiveRoughUniform
