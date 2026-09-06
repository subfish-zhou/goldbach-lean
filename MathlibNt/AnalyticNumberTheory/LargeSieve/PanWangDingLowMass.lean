import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowCarrierCorrection
import Mathlib.NumberTheory.Harmonic.Bounds

namespace AnalyticNumberTheory.LargeSieve.PanLow
open Classical Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem low_harmonic_le {N A₁ A₂ : ℕ} (hA : A₂ ≤ N) :
    (∑ a ∈ Ioc A₁ A₂, (a : ℝ)⁻¹) ≤ 1 + Real.log N := by
  calc
    _ ≤ ∑ a ∈ Icc 1 N, (a : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        rcases mem_Ioc.mp ha with ⟨ha, hb⟩
        exact mem_Icc.mpr ⟨by omega, hb.trans hA⟩
      · intros; positivity
    _ = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ _ := harmonic_le_one_add_log N

/-- Low-lane only: the whole-a norm is kept until triangle is paid by the
explicit actual-prime prefix premise. No SW transport is asserted here. -/
theorem nonprincipalLow_le_prime_budget
    (g : ℕ → ℂ) (N A₁ A₂ Q m : ℕ) (K s : ℝ)
    (hN : 3 ≤ N) (hA : A₂ ≤ N) (hm : 0 < m) (hK : 0 ≤ K)
    (hg : ∀ a ∈ Ioc A₁ A₂, ‖g a‖ ≤ 1)
    (hprefix : ∀ a ∈ Ioc A₁ A₂, ∀ q ∈ Icc 2 Q,
      ∀ χ : PrimitiveCharacter q,
      ‖primePrefix χ.1 (N / a)‖ ≤ (K * N / Real.log N ^ s) / a) :
    nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
      N A₁ A₂ Q ≤
      (Q : ℝ) * ((K * N / Real.log N ^ s) * (1 + Real.log N) +
        (A₂ : ℝ) * (m.primeFactors.card : ℝ)) := by
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let B : ℝ := K * N / Real.log N ^ s
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let M : ℝ := B * (1 + Real.log N) + (A₂ : ℝ) * m.primeFactors.card
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hamp : ∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q,
      ‖panSourceCharacterAmplitude g
        (fun n => if n.Prime ∧ n.Coprime m then 1 else 0) N A₁ A₂ χ‖ ≤ M := by
    intro q hq χ
    let primeSum : ℂ := ∑ a ∈ Ioc A₁ A₂,
      g a * χ.1 (a : ZMod q) * primePrefix χ.1 (N / a)
    have hmain : ‖primeSum‖ ≤ B * (1 + Real.log N) := by
      calc
        _ ≤ ∑ a ∈ Ioc A₁ A₂, ‖g a * χ.1 (a : ZMod q) * primePrefix χ.1 (N / a)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ a ∈ Ioc A₁ A₂, B / a := by
          apply sum_le_sum
          intro a ha
          rw [norm_mul]
          have hc : ‖g a * χ.1 (a : ZMod q)‖ ≤ 1 := by
            rw [norm_mul]
            exact (mul_le_mul (hg a ha) (χ.1.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq
              (one_mul _)
          exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hprefix a ha q hq χ)
        _ = B * ∑ a ∈ Ioc A₁ A₂, (a : ℝ)⁻¹ := by simp [div_eq_mul_inv, mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (low_harmonic_le hA) hB
    have hd := source_prime_coprime_difference_le g N A₁ A₂ m hm hg χ
    have hcard : ((Ioc A₁ A₂).card : ℝ) ≤ A₂ := by
      exact_mod_cast (show (Ioc A₁ A₂).card ≤ A₂ by simp)
    -- Split the source amplitude into the actual-prime sum and its coprimality error.
    have ht := norm_le_norm_sub_add
      (panSourceCharacterAmplitude g
        (fun n => if n.Prime ∧ n.Coprime m then 1 else 0) N A₁ A₂ χ) primeSum
    rw [norm_sub_rev, add_comm] at ht
    exact ht.trans (add_le_add hmain (hd.trans
      (mul_le_mul_of_nonneg_right hcard (by positivity))))
  -- The reciprocal-totient weight cancels the upper bound on primitive-character mass.
  rw [nonprincipalLow_eq_two_le]
  calc
    _ ≤ ∑ _q ∈ Icc 2 Q, M := by
      apply sum_le_sum
      intro q hq
      have hqpos : 0 < q := by have := (mem_Icc.mp hq).1; omega
      have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
      have hc : (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ q.totient := by
        exact_mod_cast card_primitiveCharacter_le_totient q hqpos
      calc
        _ ≤ (q.totient : ℝ)⁻¹ * ∑ _χ : PrimitiveCharacter q, M :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hamp q hq χ) (by positivity)
        _ = (q.totient : ℝ)⁻¹ * ((Fintype.card (PrimitiveCharacter q) : ℝ) * M) := by simp
        _ ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hM) (by positivity)
        _ = M := by field_simp
    _ ≤ (Q : ℝ) * M := by
      simp only [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast (show (Icc 2 Q).card ≤ Q by simp)

end
end AnalyticNumberTheory.LargeSieve.PanLow