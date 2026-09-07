import MathlibNt.SieveTheory.LiuPanActualCountCharacters
import MathlibNt.SieveTheory.LiuPanPrincipalRemainder

/-! Bounded-coefficient principal remainder estimates for Pan's actual source
sum, reusing the production moving-prefix and scalar-budget theorems. -/

noncomputable section

open scoped BigOperators Topology
open Classical Finset Filter

namespace AnalyticNumberTheory.LargeSieve.PanPrincipal

open MathlibNt.SieveTheory.LiuWeight

/-- The finite principal budget in `LiuPanPrincipalRemainder` only used the
Liu weight through `|f a| ≤ 1`, so the same estimate holds for any bounded
coefficient on the window. -/
theorem boundedPrincipalRaw_le_budget (N A₁ A₂ d : ℕ) (f : ℕ → ℝ) (T : ℝ)
    (hd : 0 < d) (hA : A₂ ≤ N) (hT : 0 ≤ T)
    (hf : ∀ a ∈ Ioc A₁ A₂, |f a| ≤ 1)
    (hp : ∀ a ∈ Ioc A₁ A₂,
      |primeCount (N / a) -
          liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤ T / a) :
    |liuPanActualPrincipalRaw (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d f| ≤
      T * (1 + Real.log N) + (A₂ : ℝ) * (d.primeFactors.card : ℝ) := by
  have hpoint (a : ℕ) (ha : a ∈ Ioc A₁ A₂) :
      |coprimePrimeCount (N / a) d -
          liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤
        T / a + (d.primeFactors.card : ℝ) := by
    have hdel := abs_primeCount_sub_coprimePrimeCount_le (N / a) d hd
    calc
      _ ≤ |coprimePrimeCount (N / a) d - primeCount (N / a)| +
          |primeCount (N / a) -
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| :=
        abs_sub_le _ _ _
      _ ≤ (d.primeFactors.card : ℝ) + T / a := by
        rw [abs_sub_comm (coprimePrimeCount _ _) (primeCount _)]
        exact add_le_add hdel (hp a ha)
      _ = _ := add_comm _ _
  unfold MathlibNt.SieveTheory.LiuWeight.liuPanActualPrincipalRaw
  calc
    _ ≤ ∑ a ∈ Ioc A₁ A₂, |if a.Coprime d then
        f a * (coprimePrimeCount (N / a) d -
          liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Ioc A₁ A₂, (T / a + (d.primeFactors.card : ℝ)) := by
      apply sum_le_sum
      intro a ha
      split_ifs with hcop
      · rw [abs_mul]
        exact (mul_le_mul (hf a ha) (hpoint a ha) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      · simp only [abs_zero]
        positivity
    _ = T * (∑ a ∈ Ioc A₁ A₂, (a : ℝ)⁻¹) +
        ((Ioc A₁ A₂).card : ℝ) * (d.primeFactors.card : ℝ) := by
      simp [sum_add_distrib, div_eq_mul_inv, mul_sum]
    _ ≤ _ := by
      apply add_le_add (mul_le_mul_of_nonneg_left (PanLow.low_harmonic_le hA) hT)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show (Ioc A₁ A₂).card ≤ A₂ by simp)

/-- The production moving-prefix PNT and low scalar payment already eliminate
the only external inputs needed by the finite bounded-coefficient budget. -/
theorem boundedPrincipalRaw_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d A₁ A₂ : ℕ, ∀ f : ℕ → ℝ,
      1 ≤ d → (d : ℝ) ≤ Real.sqrt N →
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (∀ a ∈ Ioc A₁ A₂, |f a| ≤ 1) →
        |liuPanActualPrincipalRaw (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d f| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨K, hK, M, hprefix⟩ := primeCount_li_moving_prefix (U + 2) (by linarith)
  obtain ⟨C, hC, M', hpay⟩ := PanLow.exists_low_budget_payment U 0 K hU (by norm_num) hK
  refine ⟨C, hC, max 3 (max M M'), ?_⟩
  intro N hN d A₁ A₂ f hd hdN hA hf
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNM : M ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNM' : M' ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hAN : A₂ ≤ N := by
    exact_mod_cast hA.trans
      (Real.rpow_le_self_of_one_le hN1 (by norm_num : (2 / 3 : ℝ) ≤ 1))
  have hb :=
    boundedPrincipalRaw_le_budget N A₁ A₂ d f
      (K * N / Real.log (N : ℝ) ^ (U + 2))
      (by omega) hAN (by positivity) hf (by
        intro a ha
        rcases mem_Ioc.mp ha with ⟨ha₁, ha₂⟩
        apply hprefix N hNM a (by omega)
        exact (show (a : ℝ) ≤ A₂ by exact_mod_cast ha₂).trans hA)
  refine hb.trans ?_
  have hpaid := hpay N hNM' d A₂ 1 hd hdN hA (by simp)
  simpa only [Nat.cast_one, one_mul, add_zero] using hpaid

end AnalyticNumberTheory.LargeSieve.PanPrincipal

namespace MathlibNt.SieveTheory.LiuWeight

open AnalyticNumberTheory.LargeSieve.PanPrincipal

/-- Pan's exact actual-character decomposition plus the bounded principal
payment gives the same paid-principal inequality for any window-bounded
real coefficient. The nonprincipal mass is left untouched. -/
theorem liuMainPanCoprimeIntervalMaxL_le_actualCharacterMass_with_paid_principal
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d A₁ A₂ : ℕ, ∀ f : ℕ → ℝ,
      1 ≤ d → (d : ℝ) ≤ Real.sqrt N →
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (∀ a ∈ Ioc A₁ A₂, |f a| ≤ 1) →
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N A₁ A₂ d f ≤
        (liuPanActualNonprincipalMass N A₁ A₂ d f +
          C * N / Real.log (N : ℝ) ^ U) / d.totient := by
  obtain ⟨C, hC, N₀, hprincipal⟩ := boundedPrincipalRaw_log_saving U hU
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN d A₁ A₂ f hd hdN hA hf
  have hd0 : 0 < d := by omega
  have hp := hprincipal N hN d A₁ A₂ f hd hdN hA hf
  exact (liuMainPanCoprimeIntervalMaxL_le_actualCharacterMass
      (liuLogarithmicIntegral (2 / Real.log 2)) N A₁ A₂ d f hd0).trans
    (div_le_div_of_nonneg_right (add_le_add le_rfl hp) (Nat.cast_nonneg _))

end MathlibNt.SieveTheory.LiuWeight