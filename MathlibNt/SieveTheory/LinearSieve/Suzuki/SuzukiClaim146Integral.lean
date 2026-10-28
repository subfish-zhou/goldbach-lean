import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13HatLayersKappaOne

open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- Local continuity of `qD`, using only the Section 13 contract on the positive axis. -/
lemma continuousOn_qD_Icc_of_contract
    {H : Section13HatLayers} {β D d Δ s σ : ℝ}
    (hH : Section13HatContract H β) (sign : ErrorSign)
    (hD : 1 < D) (hs : 1 < s) :
    ContinuousOn (qD H sign D d Δ) (Icc s σ) := by
  unfold qD
  have hlog : 0 < Real.log D := Real.log_pos hD
  have htpos : ∀ t ∈ Icc s σ, 0 < t := fun t ht => (zero_lt_one.trans hs).trans_le ht.1
  have htmpos : ∀ t ∈ Icc s σ, 0 < t - 1 := fun t ht => sub_pos.mpr (hs.trans_le ht.1)
  have htpow : ContinuousOn (fun t : ℝ => t ^ d) (Icc s σ) :=
    continuousOn_id.rpow continuousOn_const (fun t ht => Or.inl (ne_of_gt (htpos t ht)))
  have hbase : ContinuousOn (fun t : ℝ => 1 + t ^ d / Real.log D) (Icc s σ) :=
    continuousOn_const.add (htpow.div_const _)
  have hbasePos : ∀ t ∈ Icc s σ, 0 < 1 + t ^ d / Real.log D := by
    intro t ht
    have : 0 ≤ t ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg (htpos t ht).le _) hlog.le
    linarith
  have houter : ContinuousOn
      (fun t : ℝ => (1 + t ^ d / Real.log D) ^ (t - 1)) (Icc s σ) :=
    hbase.rpow (continuousOn_id.sub continuousOn_const)
      (fun t ht => Or.inl (ne_of_gt (hbasePos t ht)))
  have hshift : ContinuousOn (fun t : ℝ => (t - 1) ^ (H.kappaHat - 1 + 1))
      (Icc s σ) :=
    (continuousOn_id.sub continuousOn_const).rpow continuousOn_const
      (fun t ht => Or.inl (ne_of_gt (htmpos t ht)))
  have hratio : ContinuousOn (fun t : ℝ => t / (t - 1)) (Icc s σ) :=
    continuousOn_id.div (continuousOn_id.sub continuousOn_const)
      (fun t ht => ne_of_gt (htmpos t ht))
  have hratioPow : ContinuousOn (fun t : ℝ => (t / (t - 1)) ^ Δ) (Icc s σ) :=
    hratio.rpow continuousOn_const (fun t ht =>
      Or.inl (ne_of_gt (div_pos (htpos t ht) (htmpos t ht))))
  have hTshift : ContinuousOn (fun t : ℝ => H.T sign (t - 1)) (Icc s σ) := by
    exact (hH.continuous sign).comp (continuousOn_id.sub continuousOn_const) (by
      intro t ht
      exact sub_pos.mpr (hs.trans_le ht.1))
  exact ((houter.mul hshift).mul hTshift).mul hratioPow


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
