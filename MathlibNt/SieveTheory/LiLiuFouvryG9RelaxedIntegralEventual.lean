import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralFinite

noncomputable section
open scoped BigOperators Topology
open Filter Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open PrimeReciprocalLogRectangle

/-- A fixed boundary strip absorbs the moving curve for every sufficiently large N. -/
theorem fouvryG9RelaxedIntegral_curve_eventually (ρ h : ℝ) (hρ : 1 < ρ) (hh : 0 < h) :
    ∀ᶠ N : ℕ in atTop, 1+3*Real.log ρ/Real.log (N : ℝ) ≤ 1+h := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (3*Real.log ρ/h)),
    eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hln : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc : 0 < 3*Real.log ρ := mul_pos (by norm_num) (Real.log_pos hρ)
  have hmul := (div_le_iff₀ hh).mp hN
  have hdiv : 3*Real.log ρ/Real.log (N : ℝ) ≤ h := (div_le_iff₀ hln).mpr (by nlinarith)
  linarith

/-- Eventual bound by a genuinely fixed finite upper sum. n, h and δ are all
chosen before the threshold, and the only analytic input is the proved
prime reciprocal rectangle limit. -/
theorem fouvryG9RelaxedIntegral_kernel_le_upperSum_eventually
    (n : ℕ) (hn : 0 < n) (ρ h δ η : ℝ) (hρ : 1 < ρ)
    (hh : 0 < h) (hhsmall : h ≤ 1/20) (hδ : δ ≤ 1/4) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      fouvryG9RelaxedPairKernel N ρ δ ≤ fouvryG9RelaxedIntegralUpperSum n h δ + η := by
  have hc := (Metric.tendsto_nhds.1
    (fouvryG9RelaxedIntegral_fixed_grid_tendsto n hn h δ)) η hη
  have he : ∀ᶠ N : ℕ in atTop,
      fouvryG9RelaxedPairKernel N ρ δ ≤ fouvryG9RelaxedIntegralUpperSum n h δ + η := by
    filter_upwards [hc, fouvryG9RelaxedIntegral_curve_eventually ρ h hρ hh,
      eventually_ge_atTop (2 : ℕ)] with N hconv hw hN
    have habs : |fouvryG9RelaxedIntegralGrid n N h δ -
        fouvryG9RelaxedIntegralUpperSum n h δ| < η := by simpa only [Real.dist_eq] using hconv
    exact (fouvryG9RelaxedIntegral_kernel_le_grid n N hn hN hρ hδ hhsmall hw).trans
      (by have := (abs_lt.mp habs).2; linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp he
  exact ⟨max 4 N₁, le_max_left _ _, fun N hN => hN₁ N ((le_max_right _ _).trans hN)⟩

/-- Uniform small-δ control on every corner, independently of grid size. -/
theorem fouvryG9RelaxedIntegral_corner_delta {n : ℕ} (hn : 0 < n)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/8) (q : Fin n × Fin n) :
    fouvryG9RelaxedIntegralCorner n δ q ≤
      (1+6*δ)*fouvryG9RelaxedIntegralCorner n 0 q := by
  let g := 1-goldbachB9AlphaGridPoint n (q.1+1)-goldbachB9BetaGridPoint n (q.2+1)
  let t := (5/9 : ℝ)*(1-goldbachB9AlphaGridPoint n (q.1+1))
  have hg : 0 < g := goldbachB9LogGridCell_cornerGap_pos hn q
  have ha := goldbachB9AlphaGridPoint_succ_le_end hn q.1.isLt
  have ht : (10/27 : ℝ) ≤ t := by dsimp [t]; linarith
  have htd : 0 < t-δ := by linarith
  have htp : 0 < t := by linarith
  have haux : 0 ≤ δ*(6*t-1-6*δ) := mul_nonneg hδ0 (by linarith)
  have hbase : 1/(t-δ) ≤ (1+6*δ)/t := by
    apply (div_le_div_iff₀ htd htp).mpr
    nlinarith
  change 1/(g*(t-δ)) ≤ (1+6*δ)*(1/(g*(t-0)))
  simpa only [sub_zero, one_div, mul_inv, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm, one_mul] using mul_le_mul_of_nonneg_left hbase (inv_pos.mpr hg).le

/-- Uniform corner perturbations propagate through the actual logarithmic masses. -/
theorem fouvryG9RelaxedIntegral_upperSum_delta {n : ℕ} (hn : 0 < n)
    (h : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/8) :
    fouvryG9RelaxedIntegralUpperSum n h δ ≤
      (1+6*δ)*fouvryG9RelaxedIntegralUpperSum n h 0 := by
  unfold fouvryG9RelaxedIntegralUpperSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have ha := goldbachB9AlphaGridPoint_pos n q.1
  have hb := goldbachB9BetaGridPoint_pos n q.2
  have ha' := (goldbachB9AlphaGridPoint_lt_succ (i := q.1) hn).le
  have hb' := (goldbachB9BetaGridPoint_lt_succ (i := q.2) hn).le
  have hm : 0 ≤ logarithmicRectangleMass
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1)) := by
    exact mul_nonneg (Real.log_nonneg ((one_le_div ha).mpr ha'))
      (Real.log_nonneg ((one_le_div hb).mpr hb'))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (fouvryG9RelaxedIntegral_corner_delta hn hδ0 hδ q) hm

#print axioms fouvryG9RelaxedIntegral_kernel_le_grid
#print axioms fouvryG9RelaxedIntegral_kernel_le_upperSum_eventually
#print axioms fouvryG9RelaxedIntegral_upperSum_delta
#print axioms fouvryG9RelaxedIntegralLow_eq_single

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
