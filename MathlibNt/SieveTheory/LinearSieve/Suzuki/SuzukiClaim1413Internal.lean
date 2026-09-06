import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorObjects

open scoped Classical BigOperators
open Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

/-- The logarithmic coordinate of a natural carrier lies in the source range
needed in (14.13). -/
theorem carrier_logRatio_range {D p : ℕ} (hp : 2 ≤ p) (hDp : 2 * p ≤ D) :
    1 < Real.log (D : ℝ) / Real.log (p : ℝ) ∧
      Real.log (D : ℝ) / Real.log (p : ℝ) ≤
        Real.log (D : ℝ) / Real.log 2 := by
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (0 : ℝ) < (p : ℝ) := zero_lt_one.trans hp1
  have hDp' : (p : ℝ) < (D : ℝ) := by
    exact_mod_cast (show p < D by omega)
  have hD1 : 1 < (D : ℝ) := hp1.trans hDp'
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hlogpD : Real.log (p : ℝ) < Real.log (D : ℝ) :=
    Real.strictMonoOn_log (show (p : ℝ) ∈ Ioi 0 from hp0)
      (show (D : ℝ) ∈ Ioi 0 from zero_lt_one.trans hD1) hDp'
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2p : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (show (2 : ℝ) ∈ Ioi 0 by norm_num)
      (show (p : ℝ) ∈ Ioi 0 from hp0)
      (by exact_mod_cast hp)
  constructor
  · exact (one_lt_div hlogp).2 hlogpD
  · exact div_le_div_of_nonneg_left hlogD.le hlog2 hlog2p

/-- The real-variable algebra and monotonicity immediately preceding source
(14.13).  The two logarithm identities say `log D = s log p` and
`log x = (s-1) log p`; they are kept abstract here so the natural carrier
specialization below does not hide the source calculation. -/
theorem claim14_13_pointwise_of_log_coordinates
    (H : Section13HatLayers) {N : ℕ} (hN : 1 ≤ N)
    {D d Δ s x ℓ : ℝ}
    (hℓ : 0 < ℓ) (hs : 1 < s) (hd : 1 < d) (_hΔ : 0 < Δ)
    (hlogD : Real.log D = ℓ * s)
    (hlogx : Real.log x = ℓ * (s - 1))
    (hT : 0 ≤ H.T (ErrorSign.ofDepth N).opposite (s - 1)) :
    Claim14_13PointwisePremise H N D d Δ s x := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have ht : 0 < s - 1 := sub_pos.mpr hs
  have hd0 : 0 ≤ d - 1 := by linarith
  have hlogD0 : 0 < Real.log D := by rw [hlogD]; positivity
  have hlogx0 : 0 < Real.log x := by rw [hlogx]; positivity
  have htpow : (s - 1) ^ (d - 1) ≤ s ^ (d - 1) :=
    Real.rpow_le_rpow ht.le (by linarith) hd0
  have ht_d : (s - 1) ^ d = (s - 1) ^ (d - 1) * (s - 1) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one ht.ne' (d - 1)
  have hs_d : s ^ d = s ^ (d - 1) * s := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hs0.ne' (d - 1)
  have hquot :
      (s - 1) ^ d / Real.log x ≤ s ^ d / Real.log D := by
    rw [div_le_div_iff₀ hlogx0 hlogD0, ht_d, hs_d, hlogD, hlogx]
    have hcommon : 0 ≤ (s - 1) * ℓ * s := by positivity
    nlinarith [mul_le_mul_of_nonneg_right htpow hcommon]
  have hbase :
      1 + (s - 1) ^ d / Real.log x ≤ 1 + s ^ d / Real.log D := by
    linarith
  have hbase0 : 0 ≤ 1 + (s - 1) ^ d / Real.log x := by
    have : 0 ≤ (s - 1) ^ d / Real.log x :=
      div_nonneg (Real.rpow_nonneg ht.le _) hlogx0.le
    linarith
  have hbasePow :
      (1 + (s - 1) ^ d / Real.log x) ^ (s - 1) ≤
        (1 + s ^ d / Real.log D) ^ (s - 1) :=
    Real.rpow_le_rpow hbase0 hbase ht.le
  have hcore :
      (1 + (s - 1) ^ d / Real.log x) ^ (s - 1) *
          ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) ≤
        (1 + s ^ d / Real.log D) ^ (s - 1) *
          ((s - 1) * H.T (ErrorSign.ofDepth N).opposite (s - 1)) :=
    mul_le_mul_of_nonneg_right hbasePow (mul_nonneg ht.le hT)
  have hlog_relation :
      Real.log x = Real.log D * ((s - 1) / s) := by
    rw [hlogD, hlogx]
    field_simp
  have hratio0 : 0 ≤ (s - 1) / s := (div_pos ht hs0).le
  have hfactor :
      (Real.log x) ^ (-Δ) =
        (Real.log D) ^ (-Δ) * (s / (s - 1)) ^ Δ := by
    rw [hlog_relation, Real.mul_rpow hlogD0.le hratio0]
    congr 1
    rw [Real.rpow_neg hratio0, Real.div_rpow ht.le hs0.le,
      Real.div_rpow hs0.le ht.le]
    have htΔ : 0 < (s - 1) ^ Δ := Real.rpow_pos_of_pos ht _
    have hsΔ : 0 < s ^ Δ := Real.rpow_pos_of_pos hs0 _
    field_simp
  have hrest :
      0 ≤ (Real.log D) ^ (-Δ) * (s / (s - 1)) ^ Δ :=
    mul_nonneg (Real.rpow_nonneg hlogD0.le _) (Real.rpow_nonneg (div_pos hs0 ht).le _)
  unfold Claim14_13PointwisePremise
  rw [equation14_13_source_normalization H hN, hfactor]
  unfold qD Section13HatLayers.kappaHat
  norm_num [Real.rpow_one]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hcore hrest

/-- Source (14.13), internalized for a natural carrier prime/cutoff `p` before
any natural-ceiling displacement is introduced. -/
theorem claim14_13_pointwise_carrier
    (H : Section13HatLayers) {N D p : ℕ} {d Δ : ℝ}
    (hN : 1 ≤ N) (hp : 2 ≤ p) (hDp : 2 * p ≤ D)
    (hd : 1 < d) (hΔ : 0 < Δ)
    (hT : 0 ≤ H.T (ErrorSign.ofDepth (N - 1))
      (Real.log (D : ℝ) / Real.log (p : ℝ) - 1)) :
    Claim14_13PointwisePremise H N (D : ℝ) d Δ
      (Real.log (D : ℝ) / Real.log (p : ℝ)) ((D : ℝ) / (p : ℝ)) := by
  have hrange := carrier_logRatio_range hp hDp
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hD0 : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast (show 0 < D by omega)
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < p by omega))
  have hlogDcoord :
      Real.log (D : ℝ) = Real.log (p : ℝ) *
        (Real.log (D : ℝ) / Real.log (p : ℝ)) := by
    field_simp
  have hlogxcoord :
      Real.log ((D : ℝ) / (p : ℝ)) = Real.log (p : ℝ) *
        (Real.log (D : ℝ) / Real.log (p : ℝ) - 1) := by
    rw [Real.log_div hD0.ne' hp0.ne']
    field_simp
  have hTopp : 0 ≤ H.T (ErrorSign.ofDepth N).opposite
      (Real.log (D : ℝ) / Real.log (p : ℝ) - 1) := by
    rw [← ErrorSign.ofDepth_pred_eq_opposite hN]
    exact hT
  exact claim14_13_pointwise_of_log_coordinates H hN hlogp hrange.1 hd hΔ
    hlogDcoord hlogxcoord hTopp

end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
