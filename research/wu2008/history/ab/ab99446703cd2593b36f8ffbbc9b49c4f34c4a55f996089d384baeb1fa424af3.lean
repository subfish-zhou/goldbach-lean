import SrcSingleAnalyticPhi

noncomputable section
namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve Real Finset Filter
open scoped Classical Topology BigOperators
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

def innerPrimes (j : Fin 7) (N : ℕ) (δ a : ℝ) (p : ℕ) : Finset ℕ :=
  primeWindow N (wuLocalCutoff N δ p (psiTop j)) (wuLocalCutoff N δ p a)
def pairLevel (N : ℕ) (δ : ℝ) (p q : ℕ) : ℝ :=
  (N : ℝ) ^ levelExponent δ / (p * q : ℕ)
def argument (j : Fin 7) (N : ℕ) (δ : ℝ) (p q : ℕ) : ℝ :=
  log (pairLevel N δ p q) / log (wuLocalCutoff N δ p (psiTop j))
def pairMain (j : Fin 7) (N : ℕ) (δ a : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes j N, ∑ q ∈ innerPrimes j N δ a p,
    logarithmicIntegral N / (Nat.totient (p * q) : ℝ) *
      ordinaryRosserMainSum false N (p * q) (wuVariableRosserLevel N δ (p * q))
        (wuLocalCutoff N δ p (psiTop j))
def pairRemainder (j : Fin 7) (N : ℕ) (δ a : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes j N, ∑ q ∈ innerPrimes j N δ a p,
    ordinaryRosserRemainder false N (p * q) (wuVariableRosserLevel N δ (p * q))
      (wuLocalCutoff N δ p (psiTop j))
def normalizedPair (j : Fin 7) (N : ℕ) (δ a η : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes j N, ∑ q ∈ innerPrimes j N δ a p,
    logarithmicIntegral N / (Nat.totient (p * q) : ℝ) *
      ((log (argument j N δ p q - 1) - 4 * η) *
        (4 * wuSingularSeries ((p * q) * N) / log (pairLevel N δ p q)))

theorem parameter_lower {j : Fin 7} {a : ℝ} (ha : psiNode j ≤ a) :
    0 < a ∧ 2 / psiTop j + 1 / a ≤ 1 ∧ 2 ≤ psiTop j - psiTop j / a := by
  have hg := seven_parameter_geometry j
  have hs : 0 < psiNode j := by linarith [hg.1]
  have hi := one_div_le_one_div_of_le hs ha
  have hmul := mul_le_mul_of_nonneg_left hi (show 0 ≤ psiTop j by linarith [hg.2.2.1])
  rw [mul_one_div, mul_one_div] at hmul
  exact ⟨hs.trans_le ha, by linarith [hg.2.2.2.2.2.1],
    by linarith [hg.2.2.2.2.2.2.1]⟩

theorem inner_lt_outer {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hq : q ∈ innerPrimes j N δ a p) : q < p := by
  exact_mod_cast (mem_primeWindow.mp hq).2.2.2.trans_le
    ((cutoff_range hN hd hh hp ha hb).2.1.trans
      (seven_cutoff_geometry j hN hd hh hp).2.2.2.le)

theorem pair_level_eq (N p q : ℕ) (δ : ℝ) :
    pairLevel N δ p q = psiRatio N δ p / q := by
  unfold pairLevel psiRatio
  rw [Nat.cast_mul, div_div]

theorem pair_level_geometry {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a)
    (hq : q ∈ innerPrimes j N δ a p) :
    (wuLocalCutoff N δ p (psiTop j)) ^ 2 ≤ pairLevel N δ p q ∧
      wuLocalCutoff N δ p (psiTop j) ≤ (wuVariableRosserLevel N δ (p * q) : ℝ) := by
  have hr := (seven_ratio_geometry j hN hd hh hp).1
  have hR0 := zero_lt_one.trans hr
  have hz := (seven_cutoff_geometry j hN hd hh hp).1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  have hzq : (wuLocalCutoff N δ p (psiTop j)) ^ 2 * (q : ℝ) ≤ psiRatio N δ p := by
    calc
      _ ≤ (wuLocalCutoff N δ p (psiTop j)) ^ 2 * wuLocalCutoff N δ p a :=
        mul_le_mul_of_nonneg_left (mem_primeWindow.mp hq).2.2.2.le (sq_nonneg _)
      _ = (psiRatio N δ p) ^ (2 / psiTop j + 1 / a) := by
        change ((psiRatio N δ p) ^ (1 / psiTop j)) ^ 2 * (psiRatio N δ p) ^ (1 / a) = _
        rw [pow_two, ← rpow_add hR0, ← rpow_add hR0]
        congr 1; ring
      _ ≤ (psiRatio N δ p) ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hr.le (parameter_lower ha).2.1
      _ = _ := rpow_one _
  have hzz : (wuLocalCutoff N δ p (psiTop j)) ^ 2 ≤ pairLevel N δ p q := by
    rw [pair_level_eq]
    exact (le_div_iff₀ hq0).mpr hzq
  have hfloor : pairLevel N δ p q < (wuVariableRosserLevel N δ (p * q) : ℝ) := by
    unfold pairLevel wuVariableRosserLevel levelExponent
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 2 - δ) / (p * q : ℕ))
  exact ⟨hzz, (show wuLocalCutoff N δ p (psiTop j) ≤
    (wuLocalCutoff N δ p (psiTop j)) ^ 2 by nlinarith).trans (hzz.trans hfloor.le)⟩

theorem argument_bounds {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a)
    (hq : q ∈ innerPrimes j N δ a p) :
    0 < pairLevel N δ p q ∧ 2 ≤ argument j N δ p q ∧ argument j N δ p q ≤ 4 := by
  have hg := seven_parameter_geometry j
  have hr := (seven_ratio_geometry j hN hd hh hp).1
  have hR0 := zero_lt_one.trans hr
  have hlR := log_pos hr
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  have hlz : log (wuLocalCutoff N δ p (psiTop j)) = (1 / psiTop j) * log (psiRatio N δ p) :=
    log_rpow hR0 _
  have hlw : log (wuLocalCutoff N δ p a) = (1 / a) * log (psiRatio N δ p) :=
    log_rpow hR0 _
  have hz := (seven_cutoff_geometry j hN hd hh hp).1
  have hlogqlo := log_le_log (zero_lt_one.trans hz) (mem_primeWindow.mp hq).2.2.1
  have hlogqhi := log_le_log hq0 (mem_primeWindow.mp hq).2.2.2.le
  rw [hlz] at hlogqlo
  rw [hlw] at hlogqhi
  have hlz0 := log_pos hz
  have hSpos : 0 < psiTop j := by linarith [hg.2.2.1]
  have hSinv : (1 / 5 : ℝ) ≤ 1 / psiTop j :=
    one_div_le_one_div_of_le hSpos hg.2.2.2.1
  have hmul := mul_le_mul_of_nonneg_right (parameter_lower ha).2.1 hlR.le
  have hmulS := mul_le_mul_of_nonneg_right hSinv hlR.le
  refine ⟨by rw [pair_level_eq]; positivity, ?_, ?_⟩
  · apply (le_div_iff₀ hlz0).mpr
    rw [hlz, pair_level_eq, log_div hR0.ne' hq0.ne']
    nlinarith only [hmul, hlogqhi]
  · apply (div_le_iff₀ hlz0).mpr
    rw [hlz, pair_level_eq, log_div hR0.ne' hq0.ne']
    nlinarith only [hmulS, hlogqlo]

theorem pair_modulus_envelope {j : Fin 7} {N p q : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes j N) (ha : psiNode j ≤ a) (hb : a ≤ psiTop j)
    (hq : q ∈ innerPrimes j N δ a p) :
    (((p * q) * N : ℕ) : ℝ) ≤ (wuLocalCutoff N δ p (psiTop j)) ^ (120 : ℝ) := by
  have hpN := outer_le_N hN hp
  have hqN := (inner_lt_outer hN hd hh hp ha hb hq).le.trans hpN
  calc
    _ ≤ (N : ℝ) ^ (3 : ℝ) := by
      norm_cast
      nlinarith [Nat.mul_le_mul hpN hqN, Nat.mul_le_mul_right N (Nat.mul_le_mul hpN hqN)]
    _ = ((N : ℝ) ^ (1 / 40 : ℝ)) ^ (120 : ℝ) := by
      rw [← rpow_mul (Nat.cast_nonneg N)]; norm_num
    _ ≤ _ := rpow_le_rpow (by positivity)
      (cutoff_range hN hd hh hp (seven_parameter_geometry j).2.2.2.2.1 le_rfl).1 (by norm_num)

theorem omega2_single (j : Fin 7) (N : ℕ) (δ a : ℝ) :
    wuOmega2Sum N δ a (psiTop j) (fun _ : Fin 1 => psiPrimes j N) =
      ∑ p ∈ psiPrimes j N, wuOmega2 N p δ a (psiTop j) := by
  unfold wuOmega2Sum boxConvolutionSupport
  exact SingleUpperCounts.single_weighted_sum _ _

theorem omega2_finite_lower {j : Fin 7} {N : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (ha : psiNode j ≤ a) :
    pairMain j N δ a + pairRemainder j N δ a ≤
      wuOmega2Sum N δ a (psiTop j) (fun _ : Fin 1 => psiPrimes j N) := by
  rw [omega2_single]
  unfold pairMain pairRemainder wuOmega2
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  rw [HighSix.source_pair_count (N := N) (p := p) (v := wuLocalCutoff N δ p (psiTop j))
    (mem_primeWindow.mp hq).1 (mem_primeWindow.mp hq).2.2.1]
  exact ordinaryRosser_lower_finite (pair_level_geometry hN hd hh hp ha hq).2

theorem pair_remainder_paid {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (j : Fin 7) (a : ℝ),
      psiNode j ≤ a → a ≤ psiTop j →
      |pairRemainder j N δ a| ≤ ε * truncatedSixthMassScale N := by
  obtain ⟨C, _, T, hBV⟩ := HighSix.double_masked_bv
    (show (0 : ℝ) < 1 / 40 by norm_num) hd (show (0 : ℝ) < 3 by norm_num)
  obtain ⟨M, hM4, hM⟩ := logarithmic_error_payment (C := C) heps
  refine ⟨max M T, hM4.trans (le_max_left _ _), fun N hN j a ha hb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let V := primeWindow N ((N : ℝ) ^ (1 / 40 : ℝ)) ((N : ℝ) ^ truncatedSixthLowerAlpha)
  have hU : ∀ p ∈ psiPrimes j N, p.Prime ∧ p.Coprime N ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ p := by
    intro p hp
    exact ⟨(mem_primeWindow.mp hp).1, (mem_primeWindow.mp hp).2.1,
      (rpow_le_rpow_of_exponent_le hNr
        ((by norm_num : (1 / 40 : ℝ) ≤ 1 / 4).trans
          (seven_parameter_geometry j).2.2.2.2.2.2.2.1.le)).trans (mem_primeWindow.mp hp).2.2.1⟩
  have hV : ∀ q ∈ V, q.Prime ∧ q.Coprime N ∧ (N : ℝ) ^ (1 / 40 : ℝ) ≤ q := by
    intro q hq
    exact ⟨(mem_primeWindow.mp hq).1, (mem_primeWindow.mp hq).2.1, (mem_primeWindow.mp hq).2.2.1⟩
  have hsub : ∀ p ∈ psiPrimes j N, innerPrimes j N δ a p ⊆ V := by
    intro p hp q hq
    exact mem_primeWindow.mpr ⟨(mem_primeWindow.mp hq).1, (mem_primeWindow.mp hq).2.1,
      (cutoff_range hN2 hd hh hp (seven_parameter_geometry j).2.2.2.2.1 le_rfl).1.trans
        (mem_primeWindow.mp hq).2.2.1,
      (mem_primeWindow.mp hq).2.2.2.trans_le (cutoff_range hN2 hd hh hp ha hb).2.1⟩
  exact (hBV N (by omega) (psiPrimes j N) V hU hV (innerPrimes j N δ a) hsub false
    (fun p q => wuVariableRosserLevel N δ (p * q)) (fun p _ => wuLocalCutoff N δ p (psiTop j))
    (fun p _ q _ => (wuVariableRosserLevel_eq_combined N (p * q) δ).le)).trans (hM N (by omega))

theorem normalized_point_lower {δ η : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heta : 0 < η) (heta1 : η ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (j : Fin 7) (a : ℝ), psiNode j ≤ a → a ≤ psiTop j →
      ∀ p ∈ psiPrimes j N, ∀ q ∈ innerPrimes j N δ a p,
      (log (argument j N δ p q - 1) - 4 * η) *
        (4 * wuSingularSeries ((p * q) * N) / log (pairLevel N δ p q)) ≤
      ordinaryRosserMainSum false N (p * q) (wuVariableRosserLevel N δ (p * q))
        (wuLocalCutoff N δ p (psiTop j)) := by
  have hrho : 0 < exp eulerMascheroniConstant * η / 2 := by positivity
  obtain ⟨Z, hdensity⟩ := ordinaryRosser_lower_density_canonical_local hrho
  obtain ⟨Z1, hZ1⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative 120 η (by norm_num) heta)
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_ge_atTop (max 2 (max Z Z1))))
  refine ⟨max 4 T, le_max_left _ _, fun N hN he j a ha hb p hp q hq => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hz := (hT N (by omega)).trans
    (cutoff_range hN2 hd hh hp (seven_parameter_geometry j).2.2.2.2.1 le_rfl).1
  have hz2 := (le_max_left _ _).trans hz
  have hzZ := (le_max_left Z Z1).trans ((le_max_right _ _).trans hz)
  have hzZ1 := (le_max_right Z Z1).trans ((le_max_right _ _).trans hz)
  have harg := argument_bounds hN2 hd hh hp ha hq
  have hM0 : 0 < (p * q) * N :=
    Nat.mul_pos (Nat.mul_pos (mem_primeWindow.mp hp).1.pos (mem_primeWindow.mp hq).1.pos) (by omega)
  have hlocal := hZ1 (wuLocalCutoff N δ p (psiTop j)) hzZ1 ((p * q) * N) hM0 (he.mul_left _)
    (pair_modulus_envelope hN2 hd hh hp ha hb hq)
  have hlz : 0 < log (wuLocalCutoff N δ p (psiTop j)) := log_pos (by linarith)
  have hll : 0 < log (pairLevel N δ p q) := by
    have h := (le_div_iff₀ hlz).mp harg.2.1
    linarith
  have hnormal : 2 * argument j N δ p q * wuSingularSeries ((p * q) * N) /
      (exp eulerMascheroniConstant * log (pairLevel N δ p q)) =
      2 * exp (-eulerMascheroniConstant) * wuSingularSeries ((p * q) * N) /
        log (wuLocalCutoff N δ p (psiTop j)) := by
    unfold argument
    rw [exp_neg]; field_simp
  rw [← hnormal] at hlocal
  exact (canonical_lower_normalization_budget harg.2.1 harg.2.2
    (wuSingularSeries_pos _ hM0) hll heta.le heta1 hlocal).trans
    (hdensity N (p * q) he (wuLocalCutoff N δ p (psiTop j)) (pairLevel N δ p q)
      (argument j N δ p q) hzZ hz2 harg.1 rfl harg.2.1 harg.2.2)

theorem omega2_normalized_paid {δ η ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heta : 0 < η) (heta1 : η ≤ 1) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (j : Fin 7) (a : ℝ), psiNode j ≤ a → a ≤ psiTop j →
      normalizedPair j N δ a η - ε * truncatedSixthMassScale N ≤
        wuOmega2Sum N δ a (psiTop j) (fun _ : Fin 1 => psiPrimes j N) := by
  obtain ⟨T1, hT14, hT1⟩ := normalized_point_lower hd hh heta heta1
  obtain ⟨T2, _, hT2⟩ := pair_remainder_paid hd hh heps
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), fun N hN he j a ha hb => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hmain : normalizedPair j N δ a η ≤ pairMain j N δ a := by
    apply sum_le_sum
    intro p hp
    apply sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_left (hT1 N (by omega) he j a ha hb p hp q hq)
      (div_nonneg (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
        (by norm_num) (by exact_mod_cast hN2)) (Nat.cast_nonneg _))
  have hfinite := omega2_finite_lower hN2 hd hh ha
  have hrem := (abs_le.mp (hT2 N (by omega) j a ha hb)).1
  linarith only [hmain, hfinite, hrem]

#check @omega2_normalized_paid
#print axioms omega2_normalized_paid
end WuSource.SrcSingle.Analytic
