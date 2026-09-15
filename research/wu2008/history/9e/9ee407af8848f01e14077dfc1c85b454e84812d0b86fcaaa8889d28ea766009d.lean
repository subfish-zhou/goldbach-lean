import R2OmegaHighCarrier

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real Filter Set LiLiuPrereqBuchstab
open scoped Classical Topology Interval BigOperators

def outerIntegral (j : Fin 4) (δ : ℝ) : ℝ :=
  ∫ t in psiLeft (index j)..psiRight (index j), 1 / (t * (1 / 2 - δ - t))
def closedPrimes (j : Fin 4) (N : ℕ) : Finset ℕ :=
  primesIcc ((N : ℝ) ^ psiLeft (index j)) ((N : ℝ) ^ psiRight (index j))
def reciprocalMain (j : Fin 4) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes (index j) N, HighSix.primeWeight δ (log p / log N) / (p : ℝ)
def subTwoMain (j : Fin 4) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes (index j) N, HighSix.primeWeight δ (log p / log N) / ((p : ℝ) - 2)

theorem outer_closed {N p : ℕ} {j : Fin 4} (hp : p ∈ psiPrimes (index j) N) :
    p ∈ closedPrimes j N := by
  have hm := mem_primeWindow.mp hp
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr ⟨hm.1, hm.2.2.1, hm.2.2.2.le⟩

theorem closed_coordinate {N p : ℕ} {j : Fin 4} (hN : 2 ≤ N)
    (hp : p ∈ closedPrimes j N) :
    log (p : ℝ) / log N ∈ Set.Icc (psiLeft (index j)) (psiRight (index j)) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc (rpow_nonneg hn0.le (psiRight (index j)))).mp hp
  constructor
  · apply (le_div_iff₀ hl).mpr
    rw [← log_rpow hn0]
    exact log_le_log (by positivity) hlo
  · apply (div_le_iff₀ hl).mpr
    rw [← log_rpow hn0]
    exact log_le_log (by exact_mod_cast hpp.pos) hhi

theorem prime_weight_bounds {δ t : ℝ} (j : Fin 4) (hh : δ ≤ 1 / 100)
    (ht : t ∈ Set.Icc (psiLeft (index j)) (psiRight (index j))) :
    0 ≤ HighSix.primeWeight δ t ∧ HighSix.primeWeight δ t ≤ 10 := by
  have hright := (geometry j).2.2.2.2.2.2.2.2.1
  have hgap : (1 / 10 : ℝ) ≤ 1 / 2 - δ - t := by linarith [ht.2]
  unfold HighSix.primeWeight
  exact ⟨by positivity, (div_le_iff₀ (by linarith)).mpr (by linarith)⟩

theorem prime_weight_eq_single {δ t : ℝ} (j : Fin 4)
    (hd : 0 ≤ δ) (hh : δ ≤ 1 / 100)
    (ht : t ∈ Set.Icc (psiLeft (index j)) (psiRight (index j))) :
    SingleUpperQuadrature.weight δ t = HighSix.primeWeight δ t := by
  have hg := geometry j
  have hs := SingleUpperQuadrature.argument_mem hd hh
    (show t ∈ Set.Icc (1 / 15 : ℝ) (1 / 3) from
      ⟨hg.2.2.2.2.2.2.1.trans ht.1, ht.2.trans hg.2.2.2.2.2.2.2.2.1⟩)
  have harg : ((1 / 2 - δ) - t) / truncatedSixthLowerAlpha ≤ 3 := by
    apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    have hleft := ht.1
    unfold psiLeft at hleft
    have ha : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
    nlinarith [hg.2.1]
  have hA : wuUpperCoefficient (((1 / 2 - δ) - t) / truncatedSixthLowerAlpha) = 1 := by
    unfold wuUpperCoefficient
    rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three harg]
    field_simp [(show ((1 / 2 - δ) - t) / truncatedSixthLowerAlpha ≠ 0 by linarith [hs.1]),
      (exp_pos eulerMascheroniConstant).ne']
  simp only [SingleUpperQuadrature.weight, HighSix.primeWeight, hA]

theorem closed_prime_integral {δ ε : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4,
      |(∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p / log N) / (p : ℝ)) -
        outerIntegral j δ| ≤ ε := by
  obtain ⟨T, hT4, hT⟩ := SingleUpperQuadrature.weighted_prime_quadrature heps
  refine ⟨T, hT4, ?_⟩
  intro N hN j
  have hg := geometry j
  have h := hT N hN δ _ _ hd hh hg.2.2.2.2.2.2.1
    hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1
  have hi : (∫ t in psiLeft (index j)..psiRight (index j),
      SingleUpperQuadrature.weight δ t / t) = outerIntegral j δ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hg.2.2.2.2.2.2.2.1] at ht
    rw [prime_weight_eq_single j hd hh ht]
    simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [hi] at h
  have hsum : (∑ p ∈ closedPrimes j N, SingleUpperQuadrature.weight δ (log p / log N) / (p : ℝ)) =
      ∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p / log N) / (p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [prime_weight_eq_single j hd hh (closed_coordinate (by omega) hp)]
  exact (hsum ▸ h).le

theorem missing_card {N : ℕ} (j : Fin 4) (hN : 2 ≤ N) :
    ((closedPrimes j N \ psiPrimes (index j) N).card : ℝ) ≤ 16 := by
  let E := (closedPrimes j N).filter (fun p : ℕ => (p : ℝ) = (N : ℝ) ^ psiRight (index j))
  have he : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact_mod_cast (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  have hs : closedPrimes j N \ psiPrimes (index j) N ⊆
      largePrimeDivisors N ((N : ℝ) ^ (1 / 15 : ℝ)) ∪ E := by
    intro p hp
    obtain ⟨hc, hn⟩ := mem_sdiff.mp hp
    obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc
      (rpow_nonneg (Nat.cast_nonneg N) (psiRight (index j)))).mp hc
    by_cases hd : p ∣ N
    · apply mem_union_left
      exact mem_largePrimeDivisors.mpr ⟨hpp, hd, by omega,
        (rpow_le_rpow_of_exponent_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (geometry j).2.2.2.2.2.2.1).trans hlo⟩
    · apply Finset.mem_union_right
      apply mem_filter.mpr
      refine ⟨hc, le_antisymm hhi ?_⟩
      by_contra hh
      exact hn (mem_primeWindow.mpr
        ⟨hpp, hpp.coprime_iff_not_dvd.mpr hd, hlo, lt_of_not_ge hh⟩)
  have hc := (Finset.card_le_card hs).trans (card_union_le _ _)
  have hcR : ((closedPrimes j N \ psiPrimes (index j) N).card : ℝ) ≤
      (largePrimeDivisors N ((N : ℝ) ^ (1 / 15 : ℝ))).card + 1 := by
    exact_mod_cast (by omega :
      (closedPrimes j N \ psiPrimes (index j) N).card ≤
        (largePrimeDivisors N ((N : ℝ) ^ (1 / 15 : ℝ))).card + 1)
  have hd := largePrimeDivisors_card_le_inv (κ := (1 / 15 : ℝ)) (by omega)
    (show 0 < N by omega) le_rfl (by norm_num)
  norm_num at hd
  linarith

theorem reciprocal_mask_error {N : ℕ} {δ : ℝ} (j : Fin 4)
    (hN : 2 ≤ N) (hh : δ ≤ 1 / 100) :
    |(∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p / log N) / (p : ℝ)) -
      reciprocalMain j N δ| ≤ 160 / (N : ℝ) ^ (1 / 15 : ℝ) := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : 0 < (N : ℝ) ^ (1 / 15 : ℝ) := rpow_pos_of_pos hn0 _
  have hsub : psiPrimes (index j) N ⊆ closedPrimes j N := fun _ hp => outer_closed hp
  rw [reciprocalMain, ← sum_sdiff hsub, add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ closedPrimes j N \ psiPrimes (index j) N,
        |HighSix.primeWeight δ (log p / log N) / (p : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ closedPrimes j N \ psiPrimes (index j) N,
        10 / (N : ℝ) ^ (1 / 15 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hc := (mem_sdiff.mp hp).1
      have hpm := (mem_primesIcc (rpow_nonneg hn0.le (psiRight (index j)))).mp hc
      have hpr : (0 : ℝ) < p := by exact_mod_cast hpm.1.pos
      have hw := prime_weight_bounds j hh (closed_coordinate hN hc)
      have hlo := (rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (geometry j).2.2.2.2.2.2.1).trans hpm.2.1
      rw [abs_div, abs_of_nonneg hw.1, abs_of_pos hpr]
      exact (div_le_div_of_nonneg_right hw.2 hpr.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hp0 hlo)
    _ = ((closedPrimes j N \ psiPrimes (index j) N).card : ℝ) *
        (10 / (N : ℝ) ^ (1 / 15 : ℝ)) := by simp
    _ ≤ 16 * (10 / (N : ℝ) ^ (1 / 15 : ℝ)) :=
      mul_le_mul_of_nonneg_right (missing_card j hN) (by positivity)
    _ = _ := by ring

theorem reciprocal_integral {δ ε : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4,
      |reciprocalMain j N δ - outerIntegral j δ| ≤ ε := by
  obtain ⟨T0, hT04, hq⟩ := closed_prime_integral hd hh (half_pos heps)
  obtain ⟨T1, hg⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 15 by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (160 / (ε / 2))))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j
  have hN2 : 2 ≤ N := by omega
  have hb : 160 / (N : ℝ) ^ (1 / 15 : ℝ) ≤ ε / 2 := by
    apply (div_le_iff₀ (rpow_pos_of_pos
      (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega)) _)).mpr
    have h := (div_le_iff₀ (half_pos heps)).mp (hg N (by omega))
    linarith
  have hm := (reciprocal_mask_error j hN2 hh).trans hb
  rw [abs_sub_comm] at hm
  exact (abs_sub_le _ _ _).trans ((add_le_add hm (hq N (by omega) j)).trans (by linarith))

theorem subTwo_integral {δ ε : ℝ} (hd : 0 ≤ δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 4,
      |subTwoMain j N δ - outerIntegral j δ| ≤ ε := by
  let τ := ε / 100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨T0, hT04, hd'⟩ := SingleUpperPrimePayment.denominator_payment hτ
  obtain ⟨T1, _, hm⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  obtain ⟨T2, _, hq⟩ := reciprocal_integral hd hh (half_pos heps)
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN j
  have hN2 : 2 ≤ N := by omega
  have hg := geometry j
  have hden (p : ℕ) (hp : p ∈ psiPrimes (index j) N) :=
    hd' N (by omega) p (mem_primeWindow.mp hp).1
      ((rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
        hg.2.2.2.2.2.2.1).trans (mem_primeWindow.mp hp).2.2.1)
  have hmass : (∑ p ∈ psiPrimes (index j) N, 1 / (p : ℝ)) ≤ 5 :=
    (sum_le_sum_of_subset_of_nonneg (fun _ hp => outer_closed hp) (by intros; positivity)).trans
      (hm N (by omega) _ _ hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1)
  have herr : |subTwoMain j N δ - reciprocalMain j N δ| ≤ ε / 2 := by
    rw [subTwoMain, reciprocalMain, ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ psiPrimes (index j) N,
          |HighSix.primeWeight δ (log p / log N) / ((p : ℝ) - 2) -
            HighSix.primeWeight δ (log p / log N) / (p : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ psiPrimes (index j) N, 10 * τ * (1 / (p : ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden p hp).1
        have hw := prime_weight_bounds j hh (closed_coordinate hN2 (outer_closed hp))
        have hd0 : 0 ≤ 1 / ((p : ℝ) - 2) - 1 / (p : ℝ) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) (by linarith))
        have hd1 : 1 / ((p : ℝ) - 2) - 1 / (p : ℝ) ≤ τ * (1 / (p : ℝ)) := by
          have h := (hden p hp).2.1
          ring_nf at h ⊢
          linarith
        rw [show HighSix.primeWeight δ (log p / log N) / ((p : ℝ) - 2) -
          HighSix.primeWeight δ (log p / log N) / (p : ℝ) =
          HighSix.primeWeight δ (log p / log N) * (1 / ((p : ℝ) - 2) - 1 / (p : ℝ)) by ring,
          abs_of_nonneg (mul_nonneg hw.1 hd0)]
        exact (mul_le_mul hw.2 hd1 hd0 (by norm_num)).trans_eq (by ring)
      _ = (10 * τ) * ∑ p ∈ psiPrimes (index j) N, 1 / (p : ℝ) := (mul_sum ..).symm
      _ ≤ (10 * τ) * 5 := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = ε / 2 := by dsimp [τ]; ring
  exact (abs_sub_le _ _ _).trans ((add_le_add herr (hq N (by omega) j)).trans (by linarith))

#check @WuPaper.R2OmegaHigh.outerIntegral
#check @WuPaper.R2OmegaHigh.closedPrimes
#check @WuPaper.R2OmegaHigh.reciprocalMain
#check @WuPaper.R2OmegaHigh.subTwoMain
#check @WuPaper.R2OmegaHigh.outer_closed
#check @WuPaper.R2OmegaHigh.closed_coordinate
#check @WuPaper.R2OmegaHigh.prime_weight_bounds
#check @WuPaper.R2OmegaHigh.prime_weight_eq_single
#check @WuPaper.R2OmegaHigh.closed_prime_integral
#check @WuPaper.R2OmegaHigh.missing_card
#check @WuPaper.R2OmegaHigh.reciprocal_mask_error
#check @WuPaper.R2OmegaHigh.reciprocal_integral
#check @WuPaper.R2OmegaHigh.subTwo_integral
#print axioms WuPaper.R2OmegaHigh.outerIntegral
#print axioms WuPaper.R2OmegaHigh.closedPrimes
#print axioms WuPaper.R2OmegaHigh.reciprocalMain
#print axioms WuPaper.R2OmegaHigh.subTwoMain
#print axioms WuPaper.R2OmegaHigh.outer_closed
#print axioms WuPaper.R2OmegaHigh.closed_coordinate
#print axioms WuPaper.R2OmegaHigh.prime_weight_bounds
#print axioms WuPaper.R2OmegaHigh.prime_weight_eq_single
#print axioms WuPaper.R2OmegaHigh.closed_prime_integral
#print axioms WuPaper.R2OmegaHigh.missing_card
#print axioms WuPaper.R2OmegaHigh.reciprocal_mask_error
#print axioms WuPaper.R2OmegaHigh.reciprocal_integral
#print axioms WuPaper.R2OmegaHigh.subTwo_integral
end WuPaper.R2OmegaHigh
