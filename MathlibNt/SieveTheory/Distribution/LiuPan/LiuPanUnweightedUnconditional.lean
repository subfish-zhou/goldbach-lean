import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPaidPrincipalReduction
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCanonicalWeightTransfer

noncomputable section
open Finset Filter
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

namespace MathlibNt.SieveTheory.LiuWeight

/-- The strict ceil carrier is only enlarged to the closed floor carrier;
the q=0 term vanishes separately. There is no false carrier equality. -/
theorem liuPanUnweightedTheorem2Sum_le_closed (κ : ℝ) (N : ℕ) (B : ℝ) :
    liuPanUnweightedTheorem2Sum κ N B ≤
      ∑ q ∈ Icc 1 (panModulusCutoff N B), liuPanActualError κ N B q := by
  classical
  have hsub : range (panSourceStrictModulusCutoff N B) ⊆
      insert 0 (Icc 1 (panModulusCutoff N B)) := by
    intro q hq
    by_cases hq0 : q = 0
    · subst q; exact mem_insert_self _ _
    · apply mem_insert_of_mem
      refine mem_Icc.mpr ⟨by omega, ?_⟩
      exact Nat.le_floor ((mem_range_panSourceStrictModulusCutoff_iff q N B).mp hq).le
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun q _ _ => liuPanActualError_nonneg κ N B q)
  simpa only [liuPanUnweightedTheorem2Sum, sum_insert (by simp : 0 ∉ Icc 1 (panModulusCutoff N B)),
    liuPanActualError, liuMainPanCoprimeIntervalMaxL_modulus_zero, zero_add] using h

/-- Two logarithms pay a reciprocal-totient cofactor (or principal-modulus) sum. -/
theorem pan_log_sq_payment (N : ℕ) (A K : ℝ) (hK : 0 ≤ K)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    (K * N / Real.log (N : ℝ) ^ (A + 2)) * (1 + Real.log (N : ℝ)) ^ 2 ≤
      (4 * K) * N / Real.log (N : ℝ) ^ A := by
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hpow : 0 < Real.log (N : ℝ) ^ A := Real.rpow_pos_of_pos hl _
  have hsq : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]
  calc
    _ ≤ (K * N / Real.log (N : ℝ) ^ (A + 2)) * (4 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by
      rw [Real.rpow_add hl, Real.rpow_two]
      field_simp

/-- Actual unweighted distribution at the fixed principal normalization.
All low, high, cofactor and principal estimates are consumed internally. -/
theorem liuPanUnweightedTheorem2Specialization_proved :
    LiuPanUnweightedTheorem2Specialization := by
  refine ⟨2 / Real.log 2, ?_⟩
  intro A hA
  obtain ⟨K, hK, B, hB, Nk, hk⟩ := liuPanPrimitiveCofactorLedger_log_saving (A + 2) (by linarith)
  obtain ⟨P, hP, Np, hp⟩ := liuPanActualError_le_nonprincipal_with_paid_principal
    (A + 2) (by linarith)
  have he : ∀ᶠ N : ℕ in atTop,
      liuPanUnweightedTheorem2Sum (2 / Real.log 2) N B ≤
        (4 * (K + P)) * N / Real.log (N : ℝ) ^ A := by
    filter_upwards [eventually_pan_conductor_bounds B hB,
      eventually_ge_atTop Nk, eventually_ge_atTop Np] with N hb hNk hNp
    obtain ⟨hlog, _, _, hDroot, hDN⟩ := hb
    let D := panModulusCutoff N B
    let M := K * N / Real.log (N : ℝ) ^ (A + 2)
    let T := P * N / Real.log (N : ℝ) ^ (A + 2)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hmass := liuPanActualNonprincipal_sum_le_log_sq N (liuPanSourceIntervalLower N B)
      (liuPanSourceIntervalUpper N) D (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
      M hM hDN (hk N hNk)
    have hprincipal : T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ ≤
        T * (1 + Real.log (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (PanCofactor.reciprocal_totient_mass_le_log_sq hDN) hT
    calc
      _ ≤ ∑ q ∈ Icc 1 D, liuPanActualError (2 / Real.log 2) N B q :=
        liuPanUnweightedTheorem2Sum_le_closed _ _ _
      _ ≤ ∑ q ∈ Icc 1 D,
          (liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
            (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) + T) /
              q.totient := by
        apply sum_le_sum
        intro q hq
        exact hp N hNp B q (mem_Icc.mp hq).1
          ((by exact_mod_cast (mem_Icc.mp hq).2 : (q : ℝ) ≤ D).trans hDroot)
      _ = (∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ *
          liuPanActualNonprincipalMass N (liuPanSourceIntervalLower N B)
            (liuPanSourceIntervalUpper N) q (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) +
          T * ∑ q ∈ Icc 1 D, (q.totient : ℝ)⁻¹ := by
        simp only [add_div, sum_add_distrib, mul_sum]
        congr 1
        apply sum_congr rfl
        intro q _
        ring
      _ ≤ M * (1 + Real.log (N : ℝ)) ^ 2 + T * (1 + Real.log (N : ℝ)) ^ 2 :=
        add_le_add hmass hprincipal
      _ = ((K + P) * N / Real.log (N : ℝ) ^ (A + 2)) * (1 + Real.log (N : ℝ)) ^ 2 := by
        dsimp [M, T]
        ring
      _ ≤ _ := pan_log_sq_payment N A (K + P) (by positivity) hlog
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  exact ⟨4 * (K + P), by positivity, B, hB, N₀, hN₀⟩

/-- Existing finite modern weight payment applied to the actual proved source. -/
theorem liuPanWangDingCorollary230_proved : LiuPanWangDingCorollary230 :=
  liuPanUnweightedTheorem2Specialization_proved.to_corollary230

/-- Existing source/normalization transport, with no distribution hypothesis. -/
theorem liuPanCanonicalCoprimeTheorem_proved : LiuPanCanonicalCoprimeTheorem :=
  liuPanUnweightedTheorem2Specialization_proved.to_canonicalCoprimeTheorem

end MathlibNt.SieveTheory.LiuWeight