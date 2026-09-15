import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOne
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDiscreteParityRecurrence

open scoped Classical BigOperators Interval
open MeasureTheory Set Finset

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- For every odd source layer of index at least three, the weighted layer
`s f_n(s)` is constant on Suzuki's short initial interval. -/
theorem odd_layer_weighted_eq_at_beta_add_one
    {β s : ℝ} {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    (hs : 0 < s) (hsβ : s ≤ β + 1) :
    s * suzukiLayer 1 β n s =
      (β + 1) * suzukiLayer 1 β n (β + 1) := by
  obtain ⟨k, hk⟩ := hn
  have hkpos : 0 < k := by omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  subst k
  subst n
  let m : ℕ := 2 * j + 1
  have hnform : 2 * (j + 1) + 1 = m + 2 := by dsimp [m]; omega
  rw [hnform]
  have hbpos : 0 < β + 1 := hs.trans_le hsβ
  have hlower_s : recursionLower β s (m + 2) = β + 1 := by
    unfold recursionLower sourceEpsilon
    have hmod : (m + 2) % 2 = 1 := by dsimp [m]; omega
    rw [hmod]
    norm_num only [Nat.cast_one]
    rw [max_eq_right hsβ]
    apply min_eq_left
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    linarith
  have hlower_b : recursionLower β (β + 1) (m + 2) = β + 1 := by
    unfold recursionLower sourceEpsilon
    have hmod : (m + 2) % 2 = 1 := by dsimp [m]; omega
    rw [hmod]
    norm_num only [Nat.cast_one, max_self]
    apply min_eq_left
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    push_cast
    linarith
  calc
    s * suzukiLayer 1 β (m + 2) s =
        s ^ (1 : ℝ) * suzukiLayer 1 β (m + 2) s := by norm_num
    _ = suzukiLayerNumerator 1 β (m + 2) s :=
      rpow_mul_suzukiLayer 1 β (m + 2) hs
    _ = suzukiLayerNumerator 1 β (m + 2) (β + 1) := by
      rw [suzukiLayerNumerator_succ_succ, suzukiLayerNumerator_succ_succ,
        hlower_s, hlower_b]
    _ = (β + 1) ^ (1 : ℝ) * suzukiLayer 1 β (m + 2) (β + 1) :=
      (rpow_mul_suzukiLayer 1 β (m + 2) hbpos).symm
    _ = (β + 1) * suzukiLayer 1 β (m + 2) (β + 1) := by norm_num

/-- Exact κ=1 continuous identity used in Suzuki Case II:
`((β+1)/s) T_N(β+1) + T_1(s) = T_N(s)` for odd `N`. -/
theorem finiteSourceLayer_caseII_identity
    {β s : ℝ} {N : ℕ} (hN : Odd N)
    (hs : 0 < s) (hsβ : s ≤ β + 1) :
    ((β + 1) / s) * finiteSourceLayer 1 β N (β + 1) +
        finiteSourceLayer 1 β 1 s = finiteSourceLayer 1 β N s := by
  classical
  have hN1 : 1 ≤ N := by rcases hN with ⟨k, rfl⟩; omega
  have hpar : N % 2 = 1 := Nat.odd_iff.mp hN
  have hrepr (x : ℝ) : finiteSourceLayer 1 β N x =
      ∑ n ∈ sourceParityIndices N, suzukiLayer 1 β n x := by
    unfold finiteSourceLayer sourceParityIndices
    rw [hpar]
    simp only [Finset.sum_filter]
  have hone_mem : 1 ∈ sourceParityIndices N := by
    simp [sourceParityIndices, hN1, hpar]
  rw [hrepr, hrepr, finiteSourceLayer_one_eq_suzukiLayer]
  have hsplit_s := Finset.sum_erase_add (sourceParityIndices N)
    (fun n => suzukiLayer 1 β n s) hone_mem
  have hsplit_b := Finset.sum_erase_add (sourceParityIndices N)
    (fun n => suzukiLayer 1 β n (β + 1)) hone_mem
  rw [← hsplit_s, ← hsplit_b]
  have hbase_b : suzukiLayer 1 β 1 (β + 1) = 0 := by
    apply suzukiLayer_eq_zero_of_le 1 β 1
    norm_num
  rw [hbase_b, add_zero]
  have hsum : s * (∑ x ∈ (sourceParityIndices N).erase 1, suzukiLayer 1 β x s) =
      (β + 1) * (∑ x ∈ (sourceParityIndices N).erase 1,
        suzukiLayer 1 β x (β + 1)) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnmem
    have hnidx := Finset.mem_of_mem_erase hnmem
    have hnrange : 1 ≤ n ∧ n ≤ N := by
      exact Finset.mem_Icc.mp (Finset.mem_filter.mp hnidx).1
    have hnpar : n % 2 = 1 := (Finset.mem_filter.mp hnidx).2.trans hpar
    have hnodd : Odd n := Nat.odd_iff.mpr hnpar
    have hnneq : n ≠ 1 := (Finset.mem_erase.mp hnmem).1
    exact odd_layer_weighted_eq_at_beta_add_one hnodd (by omega) hs hsβ
  have hsne : s ≠ 0 := ne_of_gt hs
  field_simp [hsne]
  nlinarith

/-- T4 converts the elementary base-case loss exactly into the unperturbed
odd error scale.  This is the only use of the Section-13 initial data in Case II. -/
theorem caseII_T4_base_error_exact
    {H : Section13HatLayers} {β D K s : ℝ}
    (hH : Section13HatContract H β) (hs : 0 < s) (hsβ : s ≤ β + 1)
    (hβ1 : β ≠ 1) (hlog : Real.log D ≠ 0) :
    K * (β + 1) ^ 2 / (s * Real.log D) =
      (K * (β + 1) ^ 2 / (β - 1)) *
        (s * H.T .plus s) / Real.log D := by
  have hinit : s ^ 2 * H.T .plus s = β - 1 := by
    simpa [weightedHat] using hH.initial_plus s hs hsβ
  have hT : s * H.T .plus s = (β - 1) / s := by
    apply (eq_div_iff (ne_of_gt hs)).2
    nlinarith [hinit]
  rw [hT]
  field_simp [sub_ne_zero.mpr hβ1, hlog, ne_of_gt hs]

/-- The elementary `(log D)⁻¹` base loss is absorbed into the literal odd
`E_N(D,s)(log D)^(-Δ)` normalization. -/
theorem caseII_base_error_le_errorEnvelope
    {H : Section13HatLayers} {β D d Δ K s : ℝ} {N : ℕ}
    (hH : Section13HatContract H β) (hN : Odd N)
    (hD : Real.exp 1 ≤ D) (_hd : 0 ≤ d) (_hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hs : 0 < s) (hsβ : s ≤ β + 1) (hK : 0 ≤ K) :
    K * (β + 1) ^ 2 / (s * Real.log D) ≤
      (K * (β + 1) ^ 2 / (β - 1)) *
        errorEnvelope H N D d s * (Real.log D) ^ (-Δ) := by
  have hD1 : 1 < D := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hD
  have hlog1 : 1 ≤ Real.log D := by simpa using Real.log_le_log (by positivity) hD
  have hβm : 0 < β - 1 := sub_pos.mpr hH.beta_gt_one
  have hC0 : 0 ≤ K * (β + 1) ^ 2 / (β - 1) := by positivity
  have hTpos : 0 < H.T .plus s := hH.positive .plus s hs
  have hbase0 : 0 ≤ s * H.T .plus s := mul_nonneg hs.le hTpos.le
  have hperturb : 1 ≤ (1 + s ^ d / Real.log D) ^ s := by
    apply Real.one_le_rpow
    · have : 0 ≤ s ^ d / Real.log D :=
        div_nonneg (Real.rpow_nonneg hs.le d) (Real.log_pos hD1).le
      linarith
    · exact hs.le
  have henv : s * H.T .plus s ≤ errorEnvelope H N D d s := by
    rw [errorEnvelope_odd hN]
    calc
      s * H.T .plus s ≤ (1 + s ^ d / Real.log D) ^ s * (s * H.T .plus s) :=
        by simpa only [one_mul] using mul_le_mul_of_nonneg_right hperturb hbase0
      _ = (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s := by
        simp [Section13HatLayers.T]
        ring
  have hpow : 1 / Real.log D ≤ (Real.log D) ^ (-Δ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
  rw [caseII_T4_base_error_exact hH hs hsβ (ne_of_gt hH.beta_gt_one) (ne_of_gt (Real.log_pos hD1))]
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul henv hpow (one_div_nonneg.mpr (Real.log_pos hD1).le)
      (hbase0.trans henv)) hC0
  simpa [div_eq_mul_inv, mul_assoc] using hmul

/-- Maximal source-faithful finite Case-II inequality currently expressible with
production objects.  `hcut` is precisely (14.24), and `hendpoint` is the already
proved Case-I estimate transported from the cutoff `β+1`.  Everything after
those two interfaces—including the exact continuous parity identity and the
T4/error normalization of the base term—is proved here. -/
theorem claim14_5_caseII_finite_assembly
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D _d _Δ K s Vz endpointErr : ℝ} {N Dnat znat ynat : ℕ}
    (_hH : Section13HatContract H β) (hN : Odd N)
    (hs : 0 < s) (hsβ : s ≤ β + 1)
    (hcut : section14ExtendedT S N Dnat znat =
      section14ExtendedT S N Dnat ynat + section14ExtendedV S 1 Dnat znat)
    (hendpoint : section14ExtendedT S N Dnat ynat ≤
      Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr)
    (hbase : section14ExtendedV S 1 Dnat znat ≤
      Vz * (finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 / (s * Real.log D))) :
    section14ExtendedT S N Dnat znat ≤
      Vz * finiteSourceLayer 1 β N s + endpointErr +
        Vz * (K * (β + 1) ^ 2 / (s * Real.log D)) := by
  rw [hcut]
  calc
    section14ExtendedT S N Dnat ynat + section14ExtendedV S 1 Dnat znat ≤
        Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr +
          Vz * (finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 / (s * Real.log D)) :=
      add_le_add hendpoint hbase
    _ = Vz * finiteSourceLayer 1 β N s + endpointErr +
          Vz * (K * (β + 1) ^ 2 / (s * Real.log D)) := by
      calc
        _ = Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1) +
              finiteSourceLayer 1 β 1 s) + endpointErr +
              Vz * (K * (β + 1) ^ 2 / (s * Real.log D)) := by ring
        _ = _ := by rw [finiteSourceLayer_caseII_identity hN hs hsβ]

/-- Case-II assembly with the base loss fully normalized to the same literal
`E_N(D,s)(log D)^(-Δ)` used by the induction error. -/
theorem claim14_5_caseII_finite_assembly_normalized
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D d Δ K s Vz endpointErr : ℝ} {N Dnat znat ynat : ℕ}
    (hH : Section13HatContract H β) (hN : Odd N)
    (hD : Real.exp 1 ≤ D) (hd : 0 ≤ d) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hs : 0 < s) (hsβ : s ≤ β + 1) (hK : 0 ≤ K) (hVz : 0 ≤ Vz)
    (hcut : section14ExtendedT S N Dnat znat =
      section14ExtendedT S N Dnat ynat + section14ExtendedV S 1 Dnat znat)
    (hendpoint : section14ExtendedT S N Dnat ynat ≤
      Vz * (((β + 1) / s) * finiteSourceLayer 1 β N (β + 1)) + endpointErr)
    (hbase : section14ExtendedV S 1 Dnat znat ≤
      Vz * (finiteSourceLayer 1 β 1 s + K * (β + 1) ^ 2 / (s * Real.log D))) :
    section14ExtendedT S N Dnat znat ≤
      Vz * finiteSourceLayer 1 β N s + endpointErr +
        Vz * ((K * (β + 1) ^ 2 / (β - 1)) *
          errorEnvelope H N D d s * (Real.log D) ^ (-Δ)) := by
  have hassembly := claim14_5_caseII_finite_assembly
    (_d := d) (_Δ := Δ) hH hN hs hsβ hcut hendpoint hbase
  have hnorm := mul_le_mul_of_nonneg_left
    (caseII_base_error_le_errorEnvelope hH hN hD hd hΔ0 hΔ1 hs hsβ hK) hVz
  nlinarith [hassembly, hnorm]


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
