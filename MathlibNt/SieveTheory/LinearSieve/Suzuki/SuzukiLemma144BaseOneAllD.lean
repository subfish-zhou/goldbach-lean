import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBaseOneSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ActualRecurrenceStrictCeil
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NoDminMovingBridge

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- An explicit constant which absorbs the depth-one local-product remainder
uniformly for every natural source coordinate `D ≥ 2`. -/
noncomputable def lemma144BaseOneUniformConstant (K Δ : ℝ) : ℝ :=
  9 * K * (Real.log 2) ^ (Δ - 1) / Real.exp (Real.sqrt K)

/-- A depth-one constant independent of the dimension bound `K`. -/
noncomputable def lemma144BaseOneGlobalConstant (Δ : ℝ) : ℝ :=
  18 * (Real.log 2) ^ (Δ - 1)

theorem lemma144BaseOneUniformConstant_le_global
    {K Δ : ℝ} (hK : 0 ≤ K) :
    lemma144BaseOneUniformConstant K Δ ≤ lemma144BaseOneGlobalConstant Δ := by
  have hsqrt : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hsquare : (Real.sqrt K) ^ 2 = K := Real.sq_sqrt hK
  have hseries := Real.pow_div_factorial_le_exp (Real.sqrt K) hsqrt 2
  norm_num [Nat.factorial] at hseries
  rw [hsquare] at hseries
  have hexp : 0 < Real.exp (Real.sqrt K) := Real.exp_pos _
  have hratio : K / Real.exp (Real.sqrt K) ≤ 2 := by
    apply (div_le_iff₀ hexp).2
    linarith
  have hpow : 0 ≤ (Real.log 2) ^ (Δ - 1) := Real.rpow_nonneg (Real.log_pos (by norm_num)).le _
  unfold lemma144BaseOneUniformConstant lemma144BaseOneGlobalConstant
  calc
    9 * K * (Real.log 2) ^ (Δ - 1) / Real.exp (Real.sqrt K) =
        9 * (Real.log 2) ^ (Δ - 1) * (K / Real.exp (Real.sqrt K)) := by ring
    _ ≤ 9 * (Real.log 2) ^ (Δ - 1) * 2 := by gcongr
    _ = 18 * (Real.log 2) ^ (Δ - 1) := by ring

private theorem baseOne_localError_le_uniformEnvelope
    {H : Section13HatLayers} (hH : Section13HatContract H 2)
    {D : ℕ} {d Δ C K s : ℝ}
    (hD : 2 ≤ D) (hΔ1 : Δ < 1) (hC : lemma144BaseOneUniformConstant K Δ ≤ C)
    (hK : 2 ≤ K) (hs : 1 < s) (hs3 : s ≤ 3) :
    9 * K / (s * Real.log (D : ℝ)) ≤
      C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
        (Real.log (D : ℝ)) ^ (-Δ) := by
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogmono : Real.log (2 : ℝ) ≤ Real.log (D : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < 2 by norm_num) (zero_lt_one.trans hD1)
      (by exact_mod_cast hD)
  have hexp0 : 0 < Real.exp (Real.sqrt K) := Real.exp_pos _
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hpow :
      (Real.log (D : ℝ)) ^ (Δ - 1) ≤ (Real.log 2) ^ (Δ - 1) :=
    Real.rpow_le_rpow_of_nonpos hlog2 hlogmono (by linarith)
  have hcoef0 :
      9 * K * (Real.log 2) ^ (Δ - 1) ≤
        C * Real.exp (Real.sqrt K) := by
    have hm := mul_le_mul_of_nonneg_right hC hexp0.le
    simpa [lemma144BaseOneUniformConstant, div_eq_mul_inv] using hm
  have hcoef :
      9 * K * (Real.log (D : ℝ)) ^ (Δ - 1) ≤
        C * Real.exp (Real.sqrt K) := by
    exact (mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hK0)).trans hcoef0
  have hraw :
      9 * K / (s * Real.log (D : ℝ)) ≤
        C * Real.exp (Real.sqrt K) * (1 / s) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
    rw [div_le_iff₀ (mul_pos (zero_lt_one.trans hs) hlog)]
    have hp := mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg hlog.le (1 - Δ))
    have hpowcancel :
        (Real.log (D : ℝ)) ^ (Δ - 1) *
          (Real.log (D : ℝ)) ^ (1 - Δ) = 1 := by
      rw [← Real.rpow_add hlog]
      norm_num
    calc
      9 * K ≤
          (9 * K * (Real.log (D : ℝ)) ^ (Δ - 1)) *
            (Real.log (D : ℝ)) ^ (1 - Δ) := by
              rw [mul_assoc, hpowcancel, mul_one]
      _ ≤ (C * Real.exp (Real.sqrt K)) *
            (Real.log (D : ℝ)) ^ (1 - Δ) := hp
      _ = (C * Real.exp (Real.sqrt K) * (1 / s) *
            (Real.log (D : ℝ)) ^ (-Δ)) *
              (s * Real.log (D : ℝ)) := by
            rw [show (1 - Δ : ℝ) = -Δ + 1 by ring, Real.rpow_add hlog,
              Real.rpow_one]
            field_simp [ne_of_gt (zero_lt_one.trans hs)]
  have hE : 1 / s ≤ errorEnvelope H 1 (D : ℝ) d s :=
    one_div_le_errorEnvelope_one_lowStrip hH hD1 (zero_lt_one.trans hs) hs3
  have hC0 : 0 ≤ C := by
    have hconst0 : 0 ≤ lemma144BaseOneUniformConstant K Δ := by
      unfold lemma144BaseOneUniformConstant
      positivity
    exact hconst0.trans hC
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (mul_nonneg hC0 hexp0.le))
    (Real.rpow_nonneg hlog.le _))

/-- The genuine depth-one, odd low-strip base at every `D ≥ 2`.  Unlike the
previous eventual theorem, this has no `Dmin` and no abstract Case-II premise:
the explicit `K,Δ`-uniform constant absorbs the local-product loss. -/
theorem lemma14_4_base_one_odd_low_allD
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ1 : Δ < 1)
    (hC : lemma144BaseOneUniformConstant K Δ ≤ C)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 1 →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ → ¬ 2 ≤ s →
      suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 1 s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) := by
  intro D s hD hs hz2 hs2
  have hs1 : 1 < s := by
    norm_num [KappaOneModel.parityDomain] at hs ⊢
    exact hs
  have hs3 : s ≤ 3 := by linarith [le_of_not_ge hs2]
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  by_cases hroot : 2 ≤ (D : ℝ) ^ (1 / s)
  · have hdom : s ∈ suzukiParityDomainOne 2 1 := by
      simpa [suzukiParityDomainOne] using hs
    have hbase := lemma14_4_base_one_natCeil
      (S := S) (D := D) (z := ⌈(D : ℝ) ^ (1 / s)⌉₊)
      (s := s) (K := K) rfl hD1 hdom hs3 hroot
      (le_trans (by norm_num) hK) hlocal
    have habs := baseOne_localError_le_uniformEnvelope
      (d := d) hH hD hΔ1 hC hK hs1 hs3
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) habs) (suzukiVProduct_nonneg S _))
  · have hrootlt : (D : ℝ) ^ (1 / s) < 2 := lt_of_not_ge hroot
    have hzle : ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤ 2 := Nat.ceil_le.mpr hrootlt.le
    have hzEq : ⌈(D : ℝ) ^ (1 / s)⌉₊ = 2 := by omega
    rw [suzukiActualT_one]
    rw [suzukiSourceV_one_eq_zero_of_cube_lt_below S (by
      intro p hp
      rw [hzEq] at hp
      interval_cases p <;> norm_num <;> omega)]
    apply mul_nonneg (suzukiVProduct_nonneg S _)
    have hmain : 0 ≤ finiteSourceLayer 1 2 1 s := by
      rw [finiteSourceLayer_one_eq_lowStrip hs3]
      positivity
    have hE : 0 ≤ errorEnvelope H 1 (D : ℝ) d s :=
      errorEnvelope_nonneg H 1 hD1 hs0.le
        (hH.positive _ s hs0).le
    have hC0 : 0 ≤ C := by
      have hconst0 : 0 ≤ lemma144BaseOneUniformConstant K Δ := by
        unfold lemma144BaseOneUniformConstant
        positivity
      exact hconst0.trans hC
    exact add_nonneg hmain (by positivity)

/-- `K`-uniform version of the odd low-strip base. -/
theorem lemma14_4_base_one_odd_low_allD_global
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ1 : Δ < 1)
    (hC : lemma144BaseOneGlobalConstant Δ ≤ C)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 1 →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ → ¬ 2 ≤ s →
      suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 1 s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) := by
  exact lemma14_4_base_one_odd_low_allD hH hΔ1
    ((lemma144BaseOneUniformConstant_le_global (by linarith : 0 ≤ K)).trans hC)
    hK hlocal

/-- The complete depth-one estimate on the source low strip `1 < s ≤ 3`,
for all `D ≥ 2`, with a constant independent of `K`. -/
theorem lemma14_4_base_one_lowStrip_global_allD
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ1 : Δ < 1)
    (hC : lemma144BaseOneGlobalConstant Δ ≤ C)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 1 → s ≤ 3 →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 1 s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) := by
  intro D s hD hs hs3 hz2
  have hs1 : 1 < s := by
    norm_num [KappaOneModel.parityDomain] at hs ⊢
    exact hs
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  by_cases hroot : 2 ≤ (D : ℝ) ^ (1 / s)
  · have hdom : s ∈ suzukiParityDomainOne 2 1 := by
      simpa [suzukiParityDomainOne] using hs
    have hbase := lemma14_4_base_one_natCeil
      (S := S) (D := D) (z := ⌈(D : ℝ) ^ (1 / s)⌉₊)
      (s := s) (K := K) rfl hD1 hdom hs3 hroot
      (le_trans (by norm_num) hK) hlocal
    have habs := baseOne_localError_le_uniformEnvelope
      (d := d) hH hD hΔ1
      ((lemma144BaseOneUniformConstant_le_global (by linarith : 0 ≤ K)).trans hC)
      hK hs1 hs3
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) habs) (suzukiVProduct_nonneg S _))
  · have hrootlt : (D : ℝ) ^ (1 / s) < 2 := lt_of_not_ge hroot
    have hzEq : ⌈(D : ℝ) ^ (1 / s)⌉₊ = 2 := by
      have hzle : ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤ 2 := Nat.ceil_le.mpr hrootlt.le
      omega
    rw [suzukiActualT_one]
    rw [suzukiSourceV_one_eq_zero_of_cube_lt_below S (by
      intro p hp
      rw [hzEq] at hp
      interval_cases p <;> norm_num <;> omega)]
    apply mul_nonneg (suzukiVProduct_nonneg S _)
    have hmain : 0 ≤ finiteSourceLayer 1 2 1 s := by
      rw [finiteSourceLayer_one_eq_lowStrip hs3]
      positivity
    have hE : 0 ≤ errorEnvelope H 1 (D : ℝ) d s :=
      errorEnvelope_nonneg H 1 hD1 hs0.le (hH.positive _ s hs0).le
    have hC0 : 0 ≤ C := by
      exact (by unfold lemma144BaseOneGlobalConstant; positivity :
        0 ≤ lemma144BaseOneGlobalConstant Δ) |>.trans hC
    exact add_nonneg hmain (by positivity)


end MathlibNt.SieveTheory
