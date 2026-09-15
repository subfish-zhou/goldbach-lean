import MathlibNt.Wu2004MeanValue.BalancedLowPrefix
import MathlibNt.Wu2004MeanValue.LowRealEndpoints

/-! Low conductors on every fixed balanced cofactor range. -/

namespace Wu2004MeanValue
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped BigOperators Topology
noncomputable section

theorem balanced_lowMovingSource_le_budget
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

theorem balanced_low_source_nat_moving (A b eta F : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (h U Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (t : (q : ℕ) → PrimitiveCharacter q → ℕ → ℕ),
      1 ≤ h → h ≤ N →
      (U : ℝ) ≤ (N : ℝ) ^ (1 - eta) → S ⊆ Icc 1 U →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S, t q χ a ≤ N / a) →
      lowMovingSource f t S h Q ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨J, hJ, Nsw, hsw⟩ :=
    balanced_low_primePrefix_nat_div_max b (A + b + 1) eta hb (by linarith) heta
  have hlim := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (A + b + 1) heta).bound
      (show (0 : ℝ) < 1 by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  refine ⟨(F + 1) * (2 * J + (Real.log 2)⁻¹), by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlim, hlog, eventually_ge_atTop (max 3 Nsw)] with N hlim hlog hN
  dsimp only [Function.comp_apply] at hlog
  intro h U Q S f t hh hhN hU hS hQ hf ht
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNsw : Nsw ≤ N := (le_max_right _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog0 : 0 < Real.log (N : ℝ) := by linarith
  have hUN : U ≤ N := by
    have hr : (N : ℝ) ^ (1 - eta) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : 1 - eta ≤ 1)
    exact_mod_cast hU.trans hr
  have hp := balanced_lowMovingSource_le_budget f t S N U h Q J (A + b + 1) F
    hN3 hUN hS hh hJ.le hF hf (by
      intro a ha q hq χ
      obtain ⟨ha1, haU⟩ := mem_Icc.mp (hS ha)
      obtain ⟨hq2, hqQ⟩ := mem_Icc.mp hq
      exact hsw N hNsw a ha1 ((by exact_mod_cast haU : (a : ℝ) ≤ U).trans hU)
        q hq2 ((by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQ)
        χ (t q χ a) (ht q hq χ a ha))
  have hpay : Real.log (N : ℝ) ^ (A + b + 1) ≤ (N : ℝ) ^ eta := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0.le _),
      abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] using hlim
  have hmain :
      Real.log (N : ℝ) ^ b *
        ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) * (1 + Real.log N)) ≤
      2 * J * N / Real.log (N : ℝ) ^ A := by
    calc
      _ ≤ Real.log (N : ℝ) ^ b *
          ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) * (2 * Real.log N)) := by
        gcongr; linarith
      _ = _ := by
        rw [show A + b + 1 = A + (b + 1) by ring,
          Real.rpow_add hlog0, Real.rpow_add hlog0, Real.rpow_one]
        field_simp
  have hdel :
      Real.log (N : ℝ) ^ b * ((U : ℝ) * h.primeFactors.card) ≤
      (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 A)).mpr
    calc
      _ ≤ Real.log (N : ℝ) ^ b *
          ((N : ℝ) ^ (1 - eta) * ((Real.log 2)⁻¹ * Real.log N)) *
          Real.log (N : ℝ) ^ A := by
        gcongr
        exact primeFactors_card_le_log_of_le hh (by exact_mod_cast hhN)
      _ = (Real.log 2)⁻¹ * (N : ℝ) ^ (1 - eta) *
          Real.log (N : ℝ) ^ (A + b + 1) := by
        rw [show A + b + 1 = A + (b + 1) by ring,
          Real.rpow_add hlog0, Real.rpow_add hlog0, Real.rpow_one]
        ring
      _ ≤ (Real.log 2)⁻¹ * (N : ℝ) ^ (1 - eta) * (N : ℝ) ^ eta := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hN0]; simp
  calc
    _ ≤ F * ((Q : ℝ) * ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) *
        (1 + Real.log N) + (U : ℝ) * h.primeFactors.card)) := hp
    _ ≤ F * (Real.log (N : ℝ) ^ b * ((J * N / Real.log (N : ℝ) ^ (A + b + 1)) *
        (1 + Real.log N) + (U : ℝ) * h.primeFactors.card)) := by gcongr
    _ ≤ F * (2 * J * N / Real.log (N : ℝ) ^ A +
        (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A) := by
      rw [mul_add]
      exact mul_le_mul_of_nonneg_left (add_le_add hmain hdel) hF
    _ ≤ (F + 1) * (2 * J * N / Real.log (N : ℝ) ^ A +
        (Real.log 2)⁻¹ * N / Real.log (N : ℝ) ^ A) := by gcongr; linarith
    _ = _ := by ring

theorem balanced_low_source_real_moving (A b eta F : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (heta : 0 < eta) (hF : 0 ≤ F) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (h Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (r : (q : ℕ) → PrimitiveCharacter q → ℕ → ℝ),
      1 ≤ h → h ≤ N →
      (∀ a ∈ S, 1 ≤ a ∧ (a : ℝ) ≤ (N : ℝ) ^ (1 - eta)) →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S,
        0 ≤ r q χ a ∧ (a : ℝ) * r q χ a ≤ N) →
      lowRealMovingSource f r S h Q ≤ C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨C, hC, N₀, hbound⟩ := balanced_low_source_nat_moving A b eta F hA hb heta hF
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN h Q S f r hh hhN hS hQ hf hr
  rw [lowRealMovingSource_eq_natural]
  apply hbound N hN h ⌊(N : ℝ) ^ (1 - eta)⌋₊ Q S f
    (fun q χ a => ⌊r q χ a⌋₊) hh hhN
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (fun a ha => mem_Icc.mpr ⟨(hS a ha).1, Nat.le_floor (hS a ha).2⟩) hQ hf
  intro q hq χ a ha
  apply (Nat.le_div_iff_mul_le (hS a ha).1).mpr
  have hp := (mul_le_mul_of_nonneg_left (Nat.floor_le (hr q hq χ a ha).1)
    (Nat.cast_nonneg a)).trans (hr q hq χ a ha).2
  have hp' : a * ⌊r q χ a⌋₊ ≤ N := by exact_mod_cast hp
  simpa only [Nat.mul_comm] using hp'

end
end Wu2004MeanValue