import MathlibNt.Wu2004MeanValue.LowPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPayment

/-! Low primitive conductor source with independent `(q, χ, a)` endpoints.
The whole coefficient sum remains inside the norm in the exported estimate. -/

namespace Wu2004MeanValue
open Classical Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped BigOperators
noncomputable section

/-- Conductor one is deliberately absent. Every character on this carrier is
primitive and nonprincipal. The prime cofactor is fixed, not averaged. -/
def lowMovingSource (f : ℕ → ℂ)
    (t : (q : ℕ) → PrimitiveCharacter q → ℕ → ℕ) (S : Finset ℕ) (h Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖∑ a ∈ S, f a * χ.1 (a : ZMod q) * coprimePrimePrefix χ.1 (t q χ a) h‖

private theorem lowMovingSource_le_budget
    (f : ℕ → ℂ) (t : (q : ℕ) → PrimitiveCharacter q → ℕ → ℕ)
    (S : Finset ℕ) (N U h Q : ℕ) (J s F : ℝ)
    (hN : 3 ≤ N) (hU : U ≤ N) (hS : S ⊆ Icc 1 U)
    (hh : 0 < h) (hJ : 0 ≤ J) (hF : 0 ≤ F)
    (hf : ∀ a ∈ S, ‖f a‖ ≤ F)
    (hp : ∀ a ∈ S, ∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q,
      ‖primePrefix χ.1 (t q χ a)‖ ≤ (J * N / Real.log N ^ s) / a) :
    lowMovingSource f t S h Q ≤
      F * ((Q : ℝ) * ((J * N / Real.log N ^ s) * (1 + Real.log N) +
        (U : ℝ) * (h.primeFactors.card : ℝ))) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let B : ℝ := J * N / Real.log N ^ s
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let M : ℝ := F * (B * (1 + Real.log N) + (U : ℝ) * h.primeFactors.card)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcard : (S.card : ℝ) ≤ U := by
    exact_mod_cast ((card_le_card hS).trans (by simp : (Icc 1 U).card ≤ U))
  have hharm : (∑ a ∈ S, (a : ℝ)⁻¹) ≤ 1 + Real.log N := by
    calc
      _ ≤ ∑ a ∈ Ioc 0 U, (a : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro a ha
          obtain ⟨ha1, haU⟩ := mem_Icc.mp (hS ha)
          exact mem_Ioc.mpr ⟨by omega, haU⟩
        · intros; positivity
      _ ≤ _ := low_harmonic_le hU
  have hamp : ∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q,
      ‖∑ a ∈ S, f a * χ.1 (a : ZMod q) *
        coprimePrimePrefix χ.1 (t q χ a) h‖ ≤ M := by
    intro q hq χ
    calc
      _ ≤ ∑ a ∈ S, ‖f a * χ.1 (a : ZMod q) *
          coprimePrimePrefix χ.1 (t q χ a) h‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ S, F * (B / a + (h.primeFactors.card : ℝ)) := by
        apply sum_le_sum
        intro a ha
        have hc : ‖f a * χ.1 (a : ZMod q)‖ ≤ F := by
          rw [norm_mul]
          exact (mul_le_mul (hf a ha) (χ.1.norm_le_one _)
            (norm_nonneg _) hF).trans_eq (mul_one _)
        have hd : ‖coprimePrimePrefix χ.1 (t q χ a) h‖ ≤
            B / a + (h.primeFactors.card : ℝ) := by
          have ht := norm_sub_le (primePrefix χ.1 (t q χ a))
            (primePrefix χ.1 (t q χ a) - coprimePrimePrefix χ.1 (t q χ a) h)
          rw [sub_sub_cancel] at ht
          exact ht.trans (add_le_add (hp a ha q hq χ)
            (norm_primePrefix_sub_coprimePrimePrefix_le χ.1 (t q χ a) h hh))
        rw [norm_mul]
        exact mul_le_mul hc hd (norm_nonneg _) hF
      _ = F * (B * (∑ a ∈ S, (a : ℝ)⁻¹) +
          (S.card : ℝ) * (h.primeFactors.card : ℝ)) := by
        rw [← mul_sum, sum_add_distrib]
        simp only [div_eq_mul_inv, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ M := by
        apply mul_le_mul_of_nonneg_left _ hF
        exact add_le_add (mul_le_mul_of_nonneg_left hharm hB)
          (mul_le_mul_of_nonneg_right hcard (by positivity))
  calc
    lowMovingSource f t S h Q ≤ ∑ _q ∈ Icc 2 Q, M := by
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
    _ = _ := by dsimp [M, B]; ring

/-- Unconditional low-conductor estimate for arbitrary bounded coefficients,
arbitrary finite support, and independently moving natural prime endpoints.
All analytic constants precede the support, cofactor, weights and endpoints.
The support may extend to `N^(2/3)`; there is no logarithmic lower cutoff. -/
theorem low_source_nat_moving (A b F : ℝ) (hA : 0 < A) (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (h U Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (t : (q : ℕ) → PrimitiveCharacter q → ℕ → ℕ),
      1 ≤ h → (h : ℝ) ≤ Real.sqrt N →
      (U : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) → S ⊆ Icc 1 U →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S, t q χ a ≤ N / a) →
      lowMovingSource f t S h Q ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨J, hJ, Nsw, hsw⟩ := low_primePrefix_nat_div_max b (A + b + 2) hb
    (by linarith)
  obtain ⟨C, hC, Npay, hpay⟩ := exists_low_budget_payment A b J hA hb hJ
  refine ⟨(F + 1) * C, by positivity, max 3 (max Nsw Npay), ?_⟩
  intro N hN h U Q S f t hh hhN hU hS hQ hf ht
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hBoth : max Nsw Npay ≤ N := (le_max_right _ _).trans hN
  have hNsw : Nsw ≤ N := (le_max_left _ _).trans hBoth
  have hNpay : Npay ≤ N := (le_max_right _ _).trans hBoth
  have hUN : U ≤ N := by
    have hroot : (N : ℝ) ^ (2 / 3 : ℝ) ≤ N :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    exact_mod_cast hU.trans hroot
  have hbound := lowMovingSource_le_budget f t S N U h Q J (A + b + 2) F
    hN3 hUN hS (by omega) hJ.le hF hf (by
      intro a ha q hq χ
      obtain ⟨ha1, haU⟩ := mem_Icc.mp (hS ha)
      obtain ⟨hq2, hqQ⟩ := mem_Icc.mp hq
      exact hsw N hNsw a ha1 ((by exact_mod_cast haU : (a : ℝ) ≤ U).trans hU)
        q hq2 ((by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQ)
        χ (t q χ a) (ht q hq χ a ha))
  refine hbound.trans ((mul_le_mul_of_nonneg_left
    (hpay N hNpay h U Q hh hhN hU hQ) hF).trans ?_)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    F * (C * N / Real.log (N : ℝ) ^ A) ≤
        (F + 1) * (C * N / Real.log (N : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end
end Wu2004MeanValue