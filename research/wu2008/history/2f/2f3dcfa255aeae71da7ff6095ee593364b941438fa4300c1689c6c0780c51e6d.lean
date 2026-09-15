import R2GammaHighLower
import MathlibNt.Wu2008DoubleSieve.HighSixThetaIntegral

noncomputable section
namespace WuPaper.R2GammaHigh
open Wu2008DoubleSieve WuSource.SrcSingle Real Finset Filter Set LiLiuPrereqBuchstab
open scoped Classical Topology Interval

def primeIntegral (j : Fin 3) (δ : ℝ) : ℝ :=
  ∫ t in (psiLeft (j.castAdd 4))..(psiRight (j.castAdd 4)), 1/(t*((1/2-δ)-t))

def closedPrimes (j : Fin 3) (N : ℕ) : Finset ℕ :=
  primesIcc ((N : ℝ)^psiLeft (j.castAdd 4)) ((N : ℝ)^psiRight (j.castAdd 4))

def reciprocalMain (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes (j.castAdd 4) N, HighSix.primeWeight δ (log p/log N)/(p : ℝ)

def subTwoMain (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ psiPrimes (j.castAdd 4) N, HighSix.primeWeight δ (log p/log N)/((p : ℝ)-2)

theorem interval_geometry (j : Fin 3) :
    (1/4 : ℝ) < psiLeft (j.castAdd 4) ∧
      psiLeft (j.castAdd 4) < psiRight (j.castAdd 4) ∧
      psiRight (j.castAdd 4) ≤ 1/3 ∧
      (1/2-psiLeft (j.castAdd 4))/truncatedSixthLowerAlpha ≤ 3 := by
  fin_cases j <;> norm_num [psiLeft, psiRight, psiNode, sourceNode, truncatedSixthLowerAlpha]

theorem prime_weight_eq_single {δ t : ℝ} (j : Fin 3)
    (hd : 0 ≤ δ) (hh : δ ≤ 1/100)
    (ht : t ∈ Icc (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4))) :
    SingleUpperQuadrature.weight δ t = HighSix.primeWeight δ t := by
  have hg := interval_geometry j
  have ht' : t ∈ Icc (1/15 : ℝ) (1/3) := ⟨by linarith [ht.1], ht.2.trans hg.2.2.1⟩
  have ha := SingleUpperQuadrature.argument_mem hd hh ht'
  have h3 : ((1/2-δ)-t)/truncatedSixthLowerAlpha ≤ 3 := by
    apply le_trans _ hg.2.2.2
    exact div_le_div_of_nonneg_right (by linarith [ht.1])
      (by norm_num [truncatedSixthLowerAlpha])
  have hA : wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) = 1 := by
    generalize hu : ((1/2-δ)-t)/truncatedSixthLowerAlpha = u at *
    unfold wuUpperCoefficient
    rw [MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_eq_of_le_three h3]
    field_simp [(show u ≠ 0 by linarith [ha.1]), (exp_pos eulerMascheroniConstant).ne']
  simp only [SingleUpperQuadrature.weight, HighSix.primeWeight, hA]

theorem outer_closed {N p : ℕ} (j : Fin 3)
    (hp : p ∈ psiPrimes (j.castAdd 4) N) : p ∈ closedPrimes j N := by
  obtain ⟨hpp, _, hlo, hhi⟩ := mem_primeWindow.mp hp
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr ⟨hpp, hlo, hhi.le⟩

theorem closed_coordinate {N p : ℕ} (j : Fin 3) (hN : 2 ≤ N)
    (hp : p ∈ closedPrimes j N) :
    log (p : ℝ)/log N ∈ Icc (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4)) :=
  SingleUpperHighQuadrature.closed_coordinate hN hp

theorem prime_weight_bounds {δ t : ℝ} (j : Fin 3) (hh : δ ≤ 1/100)
    (ht : t ∈ Icc (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4))) :
    0 ≤ HighSix.primeWeight δ t ∧ HighSix.primeWeight δ t ≤ 10 := by
  have hg := interval_geometry j
  have hd : (1/10 : ℝ) ≤ (1/2-δ)-t := by linarith [ht.2, hg.2.2.1]
  have hp : 0 < (1/2-δ)-t := by linarith
  exact ⟨by unfold HighSix.primeWeight; positivity,
    (div_le_iff₀ hp).mpr (by linarith)⟩

theorem closed_prime_integral {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/100 →
      |(∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p/log N)/(p : ℝ)) -
        primeIntegral j δ| ≤ ε := by
  obtain ⟨T, hT4, hquad⟩ := SingleUpperQuadrature.weighted_prime_quadrature heps
  refine ⟨T, hT4, ?_⟩
  intro N hN j δ hd hh
  have hg := interval_geometry j
  have h := hquad N hN δ (psiLeft (j.castAdd 4)) (psiRight (j.castAdd 4))
    hd hh (by linarith [hg.1]) hg.2.1.le hg.2.2.1
  have hi : (∫ t in (psiLeft (j.castAdd 4))..(psiRight (j.castAdd 4)),
      SingleUpperQuadrature.weight δ t/t) = primeIntegral j δ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hg.2.1.le] at ht
    rw [prime_weight_eq_single j hd hh ht]
    simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
  have hs : (∑ p ∈ closedPrimes j N, SingleUpperQuadrature.weight δ (log p/log N)/(p : ℝ)) =
      ∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p/log N)/(p : ℝ) := by
    apply sum_congr rfl
    intro p hp
    rw [prime_weight_eq_single j hd hh (closed_coordinate j (by omega) hp)]
  rw [hi] at h
  exact (hs ▸ h).le

theorem missing_card {N : ℕ} (j : Fin 3) (hN : 2 ≤ N) :
    ((closedPrimes j N \ psiPrimes (j.castAdd 4) N).card : ℝ) ≤ 5 := by
  have hN0 : 0 < N := by omega
  have hg := interval_geometry j
  let E := (closedPrimes j N).filter
    (fun p : ℕ => (p : ℝ) = (N : ℝ)^psiRight (j.castAdd 4))
  have he : E.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    exact_mod_cast (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
  have hs : closedPrimes j N \ psiPrimes (j.castAdd 4) N ⊆
      largePrimeDivisors N ((N : ℝ)^(1/4 : ℝ)) ∪ E := by
    intro p hp
    obtain ⟨hc, hn⟩ := mem_sdiff.mp hp
    obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mp hc
    by_cases hpN : p ∣ N
    · apply mem_union_left
      exact mem_largePrimeDivisors.mpr ⟨hpp, hpN, hN0.ne',
        (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hg.1.le).trans hlo⟩
    · apply Finset.mem_union_right
      apply mem_filter.mpr
      refine ⟨hc, le_antisymm hhi ?_⟩
      by_contra h
      exact hn (mem_primeWindow.mpr
        ⟨hpp, hpp.coprime_iff_not_dvd.mpr hpN, hlo, lt_of_not_ge h⟩)
  have hc := (Finset.card_le_card hs).trans (card_union_le _ _)
  have hcR : ((closedPrimes j N \ psiPrimes (j.castAdd 4) N).card : ℝ) ≤
      (largePrimeDivisors N ((N : ℝ)^(1/4 : ℝ))).card + 1 := by
    exact_mod_cast (by omega :
      (closedPrimes j N \ psiPrimes (j.castAdd 4) N).card ≤
        (largePrimeDivisors N ((N : ℝ)^(1/4 : ℝ))).card + 1)
  have hdiv := largePrimeDivisors_card_le_inv (κ := (1/4 : ℝ))
    (by omega) hN0 le_rfl (by norm_num)
  norm_num at hdiv
  linarith

theorem reciprocal_mask_error {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hh : δ ≤ 1/100) :
    |(∑ p ∈ closedPrimes j N, HighSix.primeWeight δ (log p/log N)/(p : ℝ)) -
      reciprocalMain j N δ| ≤ 50/(N : ℝ)^(1/4 : ℝ) := by
  have hpow : 0 < (N : ℝ)^(1/4 : ℝ) :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hsub : psiPrimes (j.castAdd 4) N ⊆ closedPrimes j N := fun _ hp => outer_closed j hp
  rw [reciprocalMain, ← sum_sdiff hsub, add_sub_cancel_right]
  calc
    _ ≤ ∑ p ∈ closedPrimes j N \ psiPrimes (j.castAdd 4) N,
        |HighSix.primeWeight δ (log p/log N)/(p : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ closedPrimes j N \ psiPrimes (j.castAdd 4) N, 10/(N : ℝ)^(1/4 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hc := (mem_sdiff.mp hp).1
      have hp' := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mp hc
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
      have hw := prime_weight_bounds j hh (closed_coordinate j hN hc)
      have hlo := (rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (interval_geometry j).1.le).trans hp'.2.1
      rw [abs_div, abs_of_nonneg hw.1, abs_of_pos hp0]
      exact (div_le_div_of_nonneg_right hw.2 hp0.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hpow hlo)
    _ = ((closedPrimes j N \ psiPrimes (j.castAdd 4) N).card : ℝ)*
        (10/(N : ℝ)^(1/4 : ℝ)) := by simp
    _ ≤ 5*(10/(N : ℝ)^(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (missing_card j hN) (by positivity)
    _ = _ := by ring

theorem reciprocal_integral {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/100 →
      |reciprocalMain j N δ - primeIntegral j δ| ≤ ε := by
  obtain ⟨T1, hT14, hquad⟩ := closed_prime_integral (half_pos heps)
  obtain ⟨T2, hlarge⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (50/(ε/2))))
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN j δ hd hh
  have hN2 : 2 ≤ N := by omega
  have hpow : 0 < (N : ℝ)^(1/4 : ℝ) :=
    rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hb : 50/(N : ℝ)^(1/4 : ℝ) ≤ ε/2 := by
    apply (div_le_iff₀ hpow).mpr
    have h := (div_le_iff₀ (half_pos heps)).mp (hlarge N (by omega))
    linarith
  have hm := (reciprocal_mask_error j hN2 hh).trans hb
  rw [abs_sub_comm] at hm
  exact (abs_sub_le _ _ _).trans
    ((add_le_add hm (hquad N (by omega) j δ hd hh)).trans (by linarith))

theorem subTwo_reciprocal {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ δ : ℝ, δ ≤ 1/100 → |subTwoMain j N δ - reciprocalMain j N δ| ≤ ε := by
  let τ := ε/50
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨T1, hT14, hden⟩ := SingleUpperPrimePayment.denominator_payment hτ
  obtain ⟨T2, _, hmass⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN j δ hh
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hg := interval_geometry j
  have hden' (p : ℕ) (hp : p ∈ psiPrimes (j.castAdd 4) N) :=
    hden N (by omega) p (mem_primeWindow.mp hp).1
      ((rpow_le_rpow_of_exponent_le hN1 (by linarith [hg.1] : (1/15 : ℝ) ≤
        psiLeft (j.castAdd 4))).trans (mem_primeWindow.mp hp).2.2.1)
  have hb : (∑ p ∈ psiPrimes (j.castAdd 4) N, 1/(p : ℝ)) ≤ 5 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (fun _ hp => outer_closed j hp)
      (by intros; positivity))
    exact hmass N (by omega) _ _ (by linarith [hg.1]) hg.2.1.le hg.2.2.1
  rw [subTwoMain, reciprocalMain, ← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ psiPrimes (j.castAdd 4) N,
        |HighSix.primeWeight δ (log p/log N)/((p : ℝ)-2)-
          HighSix.primeWeight δ (log p/log N)/(p : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ psiPrimes (j.castAdd 4) N, 10*τ*(1/(p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden' p hp).1
      have hw := prime_weight_bounds j hh (closed_coordinate j hN2 (outer_closed j hp))
      have h0 : 0 ≤ 1/((p : ℝ)-2)-1/(p : ℝ) := sub_nonneg.mpr
        (one_div_le_one_div_of_le (by linarith) (by linarith))
      have h1 : 1/((p : ℝ)-2)-1/(p : ℝ) ≤ τ*(1/(p : ℝ)) := by
        have h := (hden' p hp).2.1
        ring_nf at h ⊢
        linarith
      rw [show HighSix.primeWeight δ (log p/log N)/((p : ℝ)-2)-
          HighSix.primeWeight δ (log p/log N)/(p : ℝ) =
          HighSix.primeWeight δ (log p/log N)*(1/((p : ℝ)-2)-1/(p : ℝ)) by ring,
        abs_of_nonneg (mul_nonneg hw.1 h0)]
      calc
        _ ≤ 10*(τ*(1/(p : ℝ))) := mul_le_mul hw.2 h1 h0 (by norm_num)
        _ = _ := by ring
    _ = (10*τ)*∑ p ∈ psiPrimes (j.castAdd 4) N, 1/(p : ℝ) := (mul_sum ..).symm
    _ ≤ (10*τ)*5 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ε := by dsimp [τ]; ring

theorem subTwo_integral {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1/100 → |subTwoMain j N δ - primeIntegral j δ| ≤ ε := by
  obtain ⟨T1, hT14, hsub⟩ := subTwo_reciprocal (half_pos heps)
  obtain ⟨T2, _, hrec⟩ := reciprocal_integral (half_pos heps)
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN j δ hd hh
  exact (abs_sub_le _ _ _).trans ((add_le_add (hsub N (by omega) j δ hh)
    (hrec N (by omega) j δ hd hh)).trans (by linarith))

#check @primeIntegral
#check @closedPrimes
#check @reciprocalMain
#check @subTwoMain
#check @interval_geometry
#check @prime_weight_eq_single
#check @outer_closed
#check @closed_coordinate
#check @prime_weight_bounds
#check @closed_prime_integral
#check @missing_card
#check @reciprocal_mask_error
#check @reciprocal_integral
#check @subTwo_reciprocal
#check @subTwo_integral
#print axioms primeIntegral
#print axioms closedPrimes
#print axioms reciprocalMain
#print axioms subTwoMain
#print axioms interval_geometry
#print axioms prime_weight_eq_single
#print axioms outer_closed
#print axioms closed_coordinate
#print axioms prime_weight_bounds
#print axioms closed_prime_integral
#print axioms missing_card
#print axioms reciprocal_mask_error
#print axioms reciprocal_integral
#print axioms subTwo_reciprocal
#print axioms subTwo_integral
end WuPaper.R2GammaHigh
