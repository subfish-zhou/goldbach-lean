import MathlibNt.Wu2004MeanValue.PrincipalWeighted
import MathlibNt.AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418Unconditional
import MathlibNt.SieveTheory.Richert1969Ordinary418Specialization

/-!
# Frozen ordinary BV in the exact Wu modulus norm

The ordinary producer is the frozen, unconditional Richert (4.18) theorem.
Its integral starts at 2 without an additive constant. Only its already proved
Richert weight payment is specialized here; no BV analytic input is reproved.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.Richert1969
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable section

theorem wu_weighted_sum_eq_squarefree (S : Finset ℕ) (E : ℕ → ℝ) :
    (∑ d ∈ S, wuModulusWeight d * E d) =
      threeOmegaErrorMass (S.filter Squarefree) E := by
  unfold threeOmegaErrorMass
  rw [sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : Squarefree d
  · simp only [hd, if_true, wuModulusWeight,
      SwitchingPrinciple.moebius_sq_eq_one_of_squarefree hd, one_mul]
  · simp [hd, wuModulusWeight, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]

/-- Constants precede the endpoint and the modulus cutoff. The maximum is
inside the weighted modulus sum and includes every reduced residue and
every integer prime endpoint from 2 to `N`. -/
theorem small_weighted_prime_prefix_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * primeAPPrefixMaxError N d) ≤
        C * N / Real.log N ^ A := by
  obtain ⟨B, hB, K, hK, hBV⟩ := richert418 (2 * A + 10) (by linarith)
  obtain ⟨L, hL, hmass⟩ := lemma3NineOmegaMass_le_polylog
  let D := L * 2 ^ (10 : ℕ) * richert418PointwiseEnvelopeConstant * K
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg hL.le (by positivity))
      richert418PointwiseEnvelopeConstant_pos.le) hK.le
  refine ⟨B, Real.sqrt D + 1, hB, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hBV, eventually_ge_atTop (3 : ℕ)] with N hBV hN
  intro Q hQ
  have hN2 : 2 ≤ N := by omega
  have hQN : Q ≤ N :=
    hQ.trans (panModulusCutoff_le_endpoint N B hN hB.le)
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    apply le_of_lt
    apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
    have he : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact he.trans_le (by exact_mod_cast hN)
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  let S := (Icc 1 Q).filter Squarefree
  let E := primeAPPrefixMaxError N
  let X := richert418PointwiseEnvelopeConstant * (N : ℝ) * (1 + Real.log N)
  have hS : S ⊆ range (Q + 1) := by
    intro d hd
    exact mem_range.mpr (by have := (mem_Icc.mp (mem_filter.mp hd).1).2; omega)
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg
      (mul_nonneg richert418PointwiseEnvelopeConstant_pos.le (by positivity))
      (by linarith)
  have hord : (∑ d ∈ S, E d) ≤ K * N / Real.log N ^ (2 * A + 10) := by
    refine (sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hBV hN2)
    · intro d hd
      exact Icc_subset_Icc_right hQ (mem_filter.mp hd).1
    · intro d _ _
      exact primeAPPrefixMaxError_nonneg N d
  have hc := weightedError_sq_le_lemma3Mass_mul_ordinary S
    (fun d => (3 : ℝ) ^ d.primeFactors.card) E X
    (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
    (fun d _ => primeAPPrefixMaxError_nonneg N d)
    (fun d hd => modulus_mul_primeAPPrefixMaxError_le hN2
      (mem_Icc.mp (mem_filter.mp hd).1).1
      ((mem_Icc.mp (mem_filter.mp hd).1).2.trans hQN))
  have heq : (∑ d ∈ S, ((3 : ℝ) ^ d.primeFactors.card) ^ 2 / d) =
      lemma3NineOmegaMass S := by
    unfold lemma3NineOmegaMass
    apply sum_congr rfl
    intro d _
    rw [pow_two, ← mul_pow]
    norm_num
  rw [heq] at hc
  have hlogQ : Real.log (Q + 2 : ℝ) ≤ 2 * Real.log N := by
    calc
      _ ≤ Real.log ((N : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by
          have : (Q : ℝ) ≤ N := by exact_mod_cast hQN
          have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
          nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlogQ0 : 0 ≤ Real.log (Q + 2 : ℝ) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) Q; linarith)
  have henv0 := richert418PointwiseEnvelopeConstant_pos.le
  have hmajor : threeOmegaErrorMass S E ^ 2 ≤
      D * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
    calc
      _ ≤ lemma3NineOmegaMass S * (X * ∑ d ∈ S, E d) := hc
      _ ≤ (L * Real.log (Q + 2) ^ (9 : ℝ)) *
          (X * (K * N / Real.log N ^ (2 * A + 10))) := by
        apply mul_le_mul
          (hmass Q S hS (fun d hd => (mem_filter.mp hd).2))
          (mul_le_mul_of_nonneg_left hord hX)
          (mul_nonneg hX (sum_nonneg fun d _ => primeAPPrefixMaxError_nonneg N d))
        positivity
      _ ≤ (L * (2 * Real.log N) ^ (9 : ℝ)) *
          ((richert418PointwiseEnvelopeConstant * N * (2 * Real.log N)) *
            (K * N / Real.log N ^ (2 * A + 10))) := by
        dsimp [X]
        gcongr
        linarith
      _ = _ := by
        dsimp [D]
        rw [Real.rpow_add hlog, mul_comm 2 A, Real.rpow_mul hlog.le]
        norm_cast
        field_simp [hlog.ne', (Real.rpow_pos_of_pos hlog A).ne']
        ring
  rw [wu_weighted_sum_eq_squarefree]
  have hratio : 0 ≤ (N : ℝ) / Real.log N ^ A := by positivity
  have hsqrt := Real.sq_sqrt hD
  have hbound : threeOmegaErrorMass S E ≤
      (Real.sqrt D + 1) * ((N : ℝ) / Real.log N ^ A) := by
    have hs : threeOmegaErrorMass S E ^ 2 ≤
        (Real.sqrt D * ((N : ℝ) / Real.log N ^ A)) ^ 2 := by
      rw [mul_pow, hsqrt]
      exact hmajor
    exact (le_of_sq_le_sq hs (mul_nonneg (Real.sqrt_nonneg D) hratio)).trans
      (by nlinarith)
  simpa only [mul_div_assoc] using hbound

end
end Wu2004MeanValue