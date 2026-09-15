import HighIncrementIntegral

namespace HighIncrement
open Finset Set Real MeasureTheory Wu2008DoubleSieve MixedSixth MixedPayment Filter
open scoped Classical Topology
noncomputable section

theorem mesh_tendsto : Tendsto mesh atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1:ℝ)/(n+1:ℕ)) atTop (𝓝 (0:ℝ))
  simpa only [Nat.cast_add,Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))

/-- One symbolic tail of all coarse resolutions pays both losses, uniformly in delta. -/
theorem mesh_eventually : ∀ᶠ n : ℕ in atTop,
    2*mesh n ≤ truncatedSixthLowerAlpha ∧
    2*mesh n/truncatedSixthLowerAlpha ≤ reserve/2 := by
  have ht1 : Tendsto (fun n => 2*mesh n) atTop (𝓝 0) := by
    simpa only [mul_zero] using mesh_tendsto.const_mul 2
  have ht2 : Tendsto (fun n => 2*mesh n/truncatedSixthLowerAlpha) atTop (𝓝 0) := by
    simpa only [zero_div] using ht1.div_const truncatedSixthLowerAlpha
  have h1 := ht1.eventually_lt_const truncatedSixthLower_parameters.1
  have h2 := ht2.eventually_lt_const (half_pos reserve_pos)
  filter_upwards [h1,h2] with n hn1 hn2
  exact ⟨hn1.le,hn2.le⟩

/-- One common delta cap, then every sufficiently fine original coarse grid.
The final N threshold may depend on delta and n. -/
theorem highGain_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ᶠ N : ℕ in atTop,
        (HighConsumer.highGain-ε)*truncatedSixthMassScale N ≤ E N n δ := by
  obtain ⟨d,hd,hdelta⟩ := MixedRecovery.original_highGain_small_delta (show 0 < ε/3 by linarith)
  refine ⟨d/2,half_pos hd,?_⟩
  intro δ hδ hdδ
  have hdlt : δ < d := by linarith
  have hbase := hdelta δ hδ hdlt
  have hcells := (MixedRecovery.original_highGain_cells δ).eventually_const_lt
    (show HighConsumer.highGain-2*(ε/3) <
      4*∫ v, (highRegion δ).indicator HighConsumer.highGainKernel v by linarith)
  have htail : ∀ᶠ n : ℕ in atTop,
      HighConsumer.highGain-2*(ε/3) < gainScalar δ n ∧
      2*mesh n/truncatedSixthLowerAlpha ≤ reserve/2 := by
    filter_upwards [hcells,mesh_eventually] with n hn hm
    exact ⟨hn.trans_le (cover_gain_le hδ n hm.1),hm.2⟩
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp htail
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨hg,hm⟩ := hn0 n hn
  filter_upwards [gainScalar_lower hδ (show 0 < ε/3 by linarith) n hm,
    eventually_ge_atTop (4:ℕ)] with N hN hN4
  exact (mul_le_mul_of_nonneg_right (by linarith only [hg])
    (truncatedSixthClosure_scale_nonneg hN4)).trans hN

/-- Fully unfolded consumer interface: the actual selected high classical term is subtracted. -/
theorem actual_highGain_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ᶠ N : ℕ in atTop,
        (HighConsumer.highGain-ε)*truncatedSixthMassScale N ≤
          MixedEta.highMain N n δ - truncatedSixthLowerNormalizedMain N δ 0
            (MixedEta.selected N n (MixedSixth.highCells δ n)) :=
  highGain_lower hε

/-- The same delta cap admits a coarse resolution beyond any externally requested threshold. -/
theorem highGain_lower_arbitrarily_fine {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ d →
      ∀ m : ℕ, ∃ n : ℕ, m ≤ n ∧ ∀ᶠ N : ℕ in atTop,
        (HighConsumer.highGain-ε)*truncatedSixthMassScale N ≤ E N n δ := by
  obtain ⟨d,hd,h⟩ := highGain_lower hε
  refine ⟨d,hd,?_⟩
  intro δ hδ hdδ m
  obtain ⟨n0,hn0⟩ := h δ hδ hdδ
  exact ⟨max m n0,le_max_left _ _,hn0 _ (le_max_right _ _)⟩

end
end HighIncrement
