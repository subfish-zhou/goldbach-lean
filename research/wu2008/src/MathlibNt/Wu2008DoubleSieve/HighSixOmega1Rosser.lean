import MathlibNt.Wu2008DoubleSieve.HighSixEndpoint

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def singleMain (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, (logarithmicIntegral N / (Nat.totient p : ℝ)) *
    ordinaryRosserMainSum true N p (wuVariableRosserLevel N δ p) (z N δ p)

noncomputable def singleRemainder (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, ordinaryRosserRemainder true N p (wuVariableRosserLevel N δ p) (z N δ p)

/-- The moving single-prime level needs no squared-prefix condition on p. -/
theorem single_level_geometry {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    1 < wuVariableRosserLevel N δ p ∧ z N δ p ≤ (wuVariableRosserLevel N δ p : ℝ) := by
  have hr := ratio_bounds hN hδ hδhi hp
  have hz : z N δ p ≤ R N δ p := by
    calc
      _ ≤ (R N δ p)^(1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hr.1.le (by norm_num [S])
      _ = _ := rpow_one _
  have hf : R N δ p < (wuVariableRosserLevel N δ p : ℝ) := by
    unfold R wuVariableRosserLevel
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ)^(1/2-δ)/(p : ℝ))
  refine ⟨?_, hz.trans hf.le⟩
  exact_mod_cast hr.1.trans hf

/-- The literal code Omega1 has the factor two, including its signed remainder. -/
theorem omega1_finite_upper {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    O1 N δ ≤ 2*singleMain N δ + 2*singleRemainder N δ := by
  unfold O1 wuOmega1 singleMain singleRemainder
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  have hg := single_level_geometry hN hδ hδhi hp
  have hf := ordinaryRosser_upper_finite (N := N) (d := p) hg.1 hg.2
  change (sourceSieveCount N p (p*N) (z N δ p) : ℝ) ≤ _ at hf
  change 2*(sourceSieveCount N p (p*N) (z N δ p) : ℝ) ≤ _
  linarith

/-- One global single-prime BV budget retains all label-dependent cutoffs. -/
theorem single_remainder_small {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |singleRemainder N δ| ≤ ε*truncatedSixthMassScale N := by
  obtain ⟨C, hC, T, hBV⟩ := SingleUpperCounts.global_signed_bv
    (show 0 < left by norm_num [left]) hδ (show (0 : ℝ) < 3 by norm_num)
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C/(ε*wuSingularSeries 1))))
  refine ⟨max 4 (max T M), le_max_left _ _, ?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_left T M).trans ((le_max_right _ _).trans hN)
  have hNM : M ≤ N := (le_max_right T M).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hseries : wuSingularSeries 1 ≤ wuSingularSeries N :=
    wuSingularSeries_le_of_dvd (by norm_num) (by omega) (one_dvd N)
  have hbudget : C/log (N : ℝ) ≤ ε*wuSingularSeries N := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp (hM N hNM)
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hseries hε.le) hlog.le
    nlinarith
  have hb := hBV N hNT (P N)
    (fun p hp => ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
      (mem_primeWindow.mp hp).2.2.1⟩)
    true (wuVariableRosserLevel N δ) (z N δ)
    (fun p _ => (wuVariableRosserLevel_eq_combined N p δ).le)
  change |singleRemainder N δ| ≤ C*N/log (N : ℝ)^(3 : ℝ) at hb
  have hb' : |singleRemainder N δ| ≤ C*N/log (N : ℝ)^(3 : ℕ) := by
    convert hb using 1
    norm_num
  calc
    _ ≤ C*N/log (N : ℝ)^(3 : ℕ) := hb'
    _ = (C/log (N : ℝ))*((N : ℝ)/log (N : ℝ)^(2 : ℕ)) := by ring
    _ ≤ (ε*wuSingularSeries N)*((N : ℝ)/log (N : ℝ)^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold truncatedSixthMassScale; ring

/-- Actual Omega1 with its full finite Rosser main and internally paid BV. -/
theorem omega1_rosser_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      O1 N δ ≤ 2*singleMain N δ + ε*truncatedSixthMassScale N := by
  obtain ⟨T,hT4,hT⟩ := single_remainder_small hδ (half_pos hε)
  refine ⟨T,hT4,?_⟩
  intro N hN
  have hf := omega1_finite_upper (by omega : 2 ≤ N) hδ hδhi
  have hr := (le_abs_self (singleRemainder N δ)).trans (hT N hN)
  linarith

end Wu2008DoubleSieve.HighSix
