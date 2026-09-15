import MathlibNt.Wu2008DoubleSieve.HighSixBV
import MathlibNt.Wu2008DoubleSieve.PhiLower

namespace Wu2008DoubleSieve.HighSix
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def pairLevel (N : ℕ) (δ : ℝ) (p q : ℕ) : ℝ :=
  (N : ℝ)^(1/2-δ)/(p*q : ℕ)
noncomputable def argument (N : ℕ) (δ : ℝ) (p q : ℕ) : ℝ :=
  log (pairLevel N δ p q) / log (z N δ p)

/-- The full moving interval lies in the genuine classical logarithmic branch. -/
theorem argument_bounds {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) :
    0 < pairLevel N δ p q ∧ 2 ≤ argument N δ p q ∧ argument N δ p q ≤ 4 := by
  have hg := cutoff_geometry hN hδ hδhi hp
  have hr := ratio_bounds hN hδ hδhi hp
  have hR0 : 0 < R N δ p := zero_lt_one.trans hr.1
  have hlR : 0 < log (R N δ p) := log_pos hr.1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  have hlevel : pairLevel N δ p q = R N δ p / (q : ℝ) := by
    unfold pairLevel R
    rw [Nat.cast_mul, div_div]
  have hlz : log (z N δ p) = (1/S)*log (R N δ p) := log_rpow hR0 _
  have hlw : log (w N δ p) = (1/s)*log (R N δ p) := log_rpow hR0 _
  have hlogqlo := log_le_log (zero_lt_one.trans hg.1) (mem_primeWindow.mp hq).2.2.1
  have hlogqhi := log_le_log hq0 (mem_primeWindow.mp hq).2.2.2.le
  rw [hlz] at hlogqlo
  rw [hlw] at hlogqhi
  have hlz0 : 0 < log (z N δ p) := log_pos hg.1
  refine ⟨hlevel ▸ div_pos hR0 hq0, ?_, ?_⟩
  · apply (le_div_iff₀ hlz0).mpr
    rw [hlz, hlevel, log_div hR0.ne' hq0.ne']
    norm_num [S, s] at *
    linarith
  · apply (div_le_iff₀ hlz0).mpr
    rw [hlz, hlevel, log_div hR0.ne' hq0.ne']
    norm_num [S, s] at *
    linarith

/-- A common polynomial envelope controls the selected full modulus. -/
theorem modulus_envelope {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) :
    ((p*q)*N : ℕ) ≤ N^3 ∧ (((p*q)*N : ℕ) : ℝ) ≤ (z N δ p)^(75 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpN : p ≤ N := by
    have h := (mem_primeWindow.mp hp).2.2.2.le.trans
      (rpow_le_rpow_of_exponent_le hN1 (show right ≤ 1 by norm_num [right]))
    rw [rpow_one] at h
    exact_mod_cast h
  have hqN : q ≤ N := (inner_lt_outer hN hδ hδhi hp hq).le.trans hpN
  have hnat : (p*q)*N ≤ N^3 := by nlinarith [Nat.mul_le_mul hpN hqN]
  refine ⟨hnat, ?_⟩
  calc
    _ ≤ (N : ℝ)^(3 : ℝ) := by norm_cast
    _ = ((N : ℝ)^(1/25 : ℝ))^(75 : ℝ) := by
      rw [← rpow_mul (Nat.cast_nonneg N)]; norm_num
    _ ≤ _ := rpow_le_rpow (by positivity) (inner_lower_cutoff hN hδ hδhi hp) (by norm_num)

/-- Both the density threshold and local-product threshold are chosen before
N,p,q. The selected modulus is pqN, with no source-box restriction. -/
theorem normalized_point_lower {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ p : ℕ, p ∈ P N →
      ∀ q : ℕ, q ∈ primeWindow N (z N δ p) (w N δ p) →
      (log (argument N δ p q - 1)-4*η) *
        (4*wuSingularSeries ((p*q)*N)/log (pairLevel N δ p q)) ≤
      ordinaryRosserMainSum false N (p*q) (wuVariableRosserLevel N δ (p*q)) (z N δ p) := by
  have hρ : 0 < exp eulerMascheroniConstant*η/2 := by positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_lower_density_canonical_local hρ
  obtain ⟨Z1, hZ1⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative 75 η (by norm_num) hη)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^(1/25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/25)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop (max 2 (max Z Z1))))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he p hp q hq
  have hN2 : 2 ≤ N := by omega
  have hz := (hT N (by omega)).trans (inner_lower_cutoff hN2 hδ hδhi hp)
  have hz2 : 2 ≤ z N δ p := (le_max_left _ _).trans hz
  have hzZ : Z ≤ z N δ p := (le_max_left Z Z1).trans ((le_max_right _ _).trans hz)
  have hzZ1 : Z1 ≤ z N δ p := (le_max_right Z Z1).trans ((le_max_right _ _).trans hz)
  have ha := argument_bounds hN2 hδ hδhi hp hq
  have hM0 : 0 < (p*q)*N := Nat.mul_pos
    (Nat.mul_pos (mem_primeWindow.mp hp).1.pos (mem_primeWindow.mp hq).1.pos) (by omega)
  have hEven : Even ((p*q)*N) := he.mul_left _
  have hlocal := hZ1 (z N δ p) hzZ1 ((p*q)*N) hM0 hEven
    (modulus_envelope hN2 hδ hδhi hp hq).2
  have hlz : 0 < log (z N δ p) := log_pos (by linarith)
  have hll : 0 < log (pairLevel N δ p q) := by
    have h := (le_div_iff₀ hlz).mp ha.2.1
    linarith
  have hnormal : 2*argument N δ p q*wuSingularSeries ((p*q)*N)/
      (exp eulerMascheroniConstant*log (pairLevel N δ p q)) =
      2*exp (-eulerMascheroniConstant)*wuSingularSeries ((p*q)*N)/log (z N δ p) := by
    unfold argument
    rw [exp_neg]
    field_simp
  rw [← hnormal] at hlocal
  have hn := canonical_lower_normalization_budget ha.2.1 ha.2.2
    (wuSingularSeries_pos _ hM0) hll hη.le hη1 hlocal
  exact hn.trans (hdensity N (p*q) he (z N δ p) (pairLevel N δ p q)
    (argument N δ p q) hzZ hz2 ha.1 rfl ha.2.1 ha.2.2)

noncomputable def normalizedMain (N : ℕ) (δ η : ℝ) : ℝ :=
  ∑ p ∈ P N, ∑ q ∈ primeWindow N (z N δ p) (w N δ p),
    (logarithmicIntegral N / (Nat.totient (p*q) : ℝ)) *
      ((log (argument N δ p q-1)-4*η) *
        (4*wuSingularSeries ((p*q)*N)/log (pairLevel N δ p q)))

/-- True two-prime normalization, with its explicit density error still visible. -/
theorem normalized_main_lower {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      normalizedMain N δ η ≤ pairMain N δ := by
  obtain ⟨T, hT4, hT⟩ := normalized_point_lower hδ hδhi hη hη1
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  apply sum_le_sum
  intro p hp
  apply sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left (hT N hN he p hp q hq)
  exact div_nonneg (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
    (by norm_num) (by exact_mod_cast (show 2 ≤ N by omega))) (Nat.cast_nonneg _)

/-- Actual lower estimate after both the full two-prime normalization and
signed BV payment; eta remains explicit until the prime quadrature is paid. -/
theorem omega2_normalized_paid {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      normalizedMain N δ η - ε*truncatedSixthMassScale N ≤ O2 N δ := by
  obtain ⟨T1, hT14, hT1⟩ := normalized_main_lower hδ hδhi hη hη1
  obtain ⟨T2, _, hT2⟩ := omega2_lower_paid hδ hδhi hε
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN he
  exact (sub_le_sub_right (hT1 N ((le_max_left _ _).trans hN) he) _).trans
    (hT2 N ((le_max_right _ _).trans hN))

/-- Immediate literal mother consumption. This is not a claim that the
remaining normalized moving prime sum has already been replaced by J. -/
theorem count_normalized_paid {δ η ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hη1 : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*C6 N ≤ O1 N δ - normalizedMain N δ η + O3 N δ + ε*truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := omega2_normalized_paid hδ hδhi hη hη1 hε
  refine ⟨T, hT4, ?_⟩
  intro N hN he
  have hf := count_finite (show 2 ≤ N by omega) hδ hδhi
  have hb := hT N hN he
  linarith

end Wu2008DoubleSieve.HighSix
