import FirstIntegralEnvelope

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu08OriginalFirstSteps
namespace FirstIntegralRecovery

/-- A rational kernel on exactly the original full triangular projection. -/
def cLowerKernel (s u : ℝ) : ℝ := splitL (u-1)/u * splitL ((s-1)/(u+1))
def cExactKernel (s u : ℝ) : ℝ := log (u-1)/u * log ((s-1)/(u+1))
def cLowerMass (s : ℝ) : ℝ := ∫ u in (2:ℝ)..(s-2), cLowerKernel s u

theorem ratio_ge_one {s u : ℝ} (hu : u ∈ Icc 2 (s-2)) :
    1 ≤ (s-1)/(u+1) := by
  apply (le_div_iff₀ (show 0 < u+1 by linarith [hu.1])).2
  linarith [hu.2]

theorem cLowerKernel_continuousOn (s : ℝ) :
    ContinuousOn (cLowerKernel s) (Icc 2 (s-2)) := by
  have hn : ∀ u ∈ Icc (2:ℝ) (s-2), u ≠ 0 := fun u hu => by linarith [hu.1]
  have hn1 : ∀ u ∈ Icc (2:ℝ) (s-2), u+1 ≠ 0 := fun u hu => by linarith [hu.1]
  exact ((splitL_continuousOn.comp (continuousOn_id.sub continuousOn_const)
    (fun u hu => show 1 ≤ u-1 by linarith [hu.1])).div continuousOn_id hn).mul
    (splitL_continuousOn.comp
      (continuousOn_const.div (continuousOn_id.add continuousOn_const) hn1)
      (fun _ hu => ratio_ge_one hu))

theorem cExactKernel_continuousOn (s : ℝ) :
    ContinuousOn (cExactKernel s) (Icc 2 (s-2)) := by
  have hn : ∀ u ∈ Icc (2:ℝ) (s-2), u ≠ 0 := fun u hu => by linarith [hu.1]
  have hn1 : ∀ u ∈ Icc (2:ℝ) (s-2), u+1 ≠ 0 := fun u hu => by linarith [hu.1]
  exact (((continuousOn_id.sub continuousOn_const).log
    (fun u hu => show u-1 ≠ 0 by linarith [hu.1])).div continuousOn_id hn).mul
    ((continuousOn_const.div (continuousOn_id.add continuousOn_const) hn1).log
      (fun _ hu => ne_of_gt (lt_of_lt_of_le zero_lt_one (ratio_ge_one hu))))

theorem cLowerKernel_le {s u : ℝ} (hu : u ∈ Icc 2 (s-2)) :
    cLowerKernel s u ≤ cExactKernel s u := by
  have hu1 : 1 ≤ u-1 := by linarith [hu.1]
  have hu0 : 0 ≤ u := by linarith [hu.1]
  exact mul_le_mul
    (div_le_div_of_nonneg_right (splitL_le_log hu1) hu0)
    (splitL_le_log (ratio_ge_one hu)) (splitL_nonneg (ratio_ge_one hu))
    (div_nonneg (log_nonneg hu1) hu0)

theorem cLowerKernel_lt {s u : ℝ} (hu : u ∈ Ioo 2 (s-2)) :
    cLowerKernel s u < cExactKernel s u := by
  have hu1 : 1 < u-1 := by linarith [hu.1]
  have hu0 : 0 < u := by linarith [hu.1]
  have hr : 1 < (s-1)/(u+1) := by
    apply (lt_div_iff₀ (show 0 < u+1 by linarith [hu.1])).2
    linarith [hu.2]
  exact (mul_le_mul_of_nonneg_left (splitL_le_log hr.le)
    (div_nonneg (splitL_nonneg hu1.le) hu0.le)).trans_lt
    (mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hu0).2 (splitL_lt_log hu1))
      (log_pos hr))

/-- Strict actual C bound: no original interval has been truncated or sampled. -/
theorem cLowerMass_lt_C {s : ℝ} (hs : 4 < s) : cLowerMass s < C s := by
  rw [C_flat hs.le]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith) (cLowerKernel_continuousOn s) (cExactKernel_continuousOn s)
  · intro u hu
    exact cLowerKernel_le ⟨hu.1.le,hu.2⟩
  · obtain ⟨u,hu⟩ := exists_between (show (2:ℝ) < s-2 by linarith)
    exact ⟨u,⟨hu.1.le,hu.2.le⟩,cLowerKernel_lt hu⟩

/-- The fourfold term is retained literally, and paid only once. -/
def firstLower : ℝ := 8*(log (1127/200)+cLowerMass (1327/200)+E (1327/200))

theorem firstLower_lt_actual : firstLower < Wu08TerminalAlignment.firstMain := by
  have h := cLowerMass_lt_C (by norm_num : (4:ℝ) < 1327/200)
  unfold firstLower Wu08TerminalAlignment.firstMain
  linarith only [h]

/-- Actual first sieve count, consuming the new original-domain lower bound. -/
theorem firstLower_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (firstLower-ε)*Wu2008DoubleSieve.wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (Wu2008DoubleSieve.sieveCount N 1 N
          ((N : ℝ)^Wu2008DoubleSieve.truncatedSixthLowerAlpha) : ℝ) := by
  have hδ : 0 < Wu08TerminalAlignment.firstMain-firstLower+ε := by
    linarith only [firstLower_lt_actual,hε]
  obtain ⟨T,hT,h⟩ := Wu08TerminalAlignment.first_actual_count hδ
  refine ⟨T,hT,?_⟩
  intro N hN hEven
  have heq : Wu08TerminalAlignment.firstMain-
      (Wu08TerminalAlignment.firstMain-firstLower+ε) = firstLower-ε := by ring
  simpa only [heq] using h N hN hEven

/-- Honest remaining sufficient obligation, not a proof of publication payment. -/
theorem publication_of_new_mass
    (h : (14900897:ℝ)/8000000-log (1127/200) ≤ cLowerMass (1327/200)+E (1327/200)) :
    FirstPublicationAudit.publicationTarget ≤ Wu08TerminalAlignment.firstMain := by
  have hnew : FirstPublicationAudit.publicationTarget ≤ firstLower := by
    unfold firstLower FirstPublicationAudit.publicationTarget
    linarith only [h]
  exact hnew.trans firstLower_lt_actual.le

end FirstIntegralRecovery
