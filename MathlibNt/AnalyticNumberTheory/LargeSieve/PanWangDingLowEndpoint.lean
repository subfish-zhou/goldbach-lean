import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowMovingPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowPayment
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanWangDingSource

namespace AnalyticNumberTheory.LargeSieve.PanLow
open Classical Finset
open MathlibNt.SieveTheory.LiuWeight
noncomputable section

/-- The needed y=N specialization of Pan (2.12), with all prefix and scalar
payments internal. This is the explicitly nonprincipal carrier, not raw panIymLow. -/
theorem nonprincipalLow_endpoint (U b : ℝ) (hU : 0 < U) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m A₁ A₂ Q : ℕ,
      ∀ g : ℕ → ℂ,
      1 ≤ m → (m : ℝ) ≤ Real.sqrt N →
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
      (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      (∀ a ∈ Ioc A₁ A₂, ‖g a‖ ≤ 1) →
      nonprincipalLow g (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
        N A₁ A₂ Q ≤ C * N / Real.log (N : ℝ) ^ U := by
  obtain ⟨K, hK, Nsw, hsw⟩ := primePrefix_siegelWalfisz_nat_div b (U + b + 2) hb
    (by linarith)
  obtain ⟨C, hC, Npay, hpay⟩ := exists_low_budget_payment U b K hU hb hK
  refine ⟨C, hC, max 3 (max Nsw Npay), ?_⟩
  intro N hN m A₁ A₂ Q g hm hmN hA hQ hg
  rcases max_le_iff.mp hN with ⟨hN3, hBoth⟩
  rcases max_le_iff.mp hBoth with ⟨hNsw, hNpay⟩
  have hAN : A₂ ≤ N := by
    have hroot : (N : ℝ) ^ (2 / 3 : ℝ) ≤ N :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    exact_mod_cast hA.trans hroot
  -- Supply the actual-prime prefix estimate before applying the scalar payment.
  have hprefix : ∀ a ∈ Ioc A₁ A₂, ∀ q ∈ Icc 2 Q,
      ∀ χ : PrimitiveCharacter q,
      ‖primePrefix χ.1 (N / a)‖ ≤
        (K * N / Real.log N ^ (U + b + 2)) / a := by
    intro a ha q hq χ
    obtain ⟨ha₁, ha₂⟩ := mem_Ioc.mp ha
    obtain ⟨hq₂, hqQ⟩ := mem_Icc.mp hq
    exact hsw N hNsw a (by omega)
      ((by exact_mod_cast ha₂ : (a : ℝ) ≤ A₂).trans hA) q hq₂
      ((by exact_mod_cast hqQ : (q : ℝ) ≤ Q).trans hQ) χ
      (primitiveCharacter_ne_one_of_two_le hq₂ χ)
  exact (nonprincipalLow_le_prime_budget g N A₁ A₂ Q m K (U + b + 2)
    hN3 hAN (by omega) hK.le hg hprefix).trans
    (hpay N hNpay m A₂ Q hm hmN hA hQ)

/-- Literal Liu coefficient and Pan source window; the threshold is independent
of the window exponent B. No claim about the high-conductor part is made. -/
theorem nonprincipalLow_liuSource_endpoint (U b : ℝ) (hU : 0 < U) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (B : ℝ) (m Q : ℕ),
      1 ≤ m → (m : ℝ) ≤ Real.sqrt N → (Q : ℝ) ≤ Real.log (N : ℝ) ^ b →
      nonprincipalLow
        (fun a => if a.Coprime m then
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ) else 0)
        (fun n => if n.Prime ∧ n.Coprime m then 1 else 0)
        N (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) Q ≤
          C * N / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, N₀, h⟩ := nonprincipalLow_endpoint U b hU hb
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN B m Q hm hmN hQ
  refine h N hN m _ _ Q _ hm hmN ?_ hQ ?_
  · exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · intro a _
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
        liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
    · simp

end
end AnalyticNumberTheory.LargeSieve.PanLow