import MathlibNt.Wu2008DoubleSieve.HighSixPrimeIntegral

namespace Wu2008DoubleSieve.HighSix
open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def subTwoMain (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ P N, primeWeight δ (log p/log N)/((p : ℝ)-2)
noncomputable def liRatio (N : ℕ) : ℝ := logarithmicIntegral N*log N/(N : ℝ)

/-- The p-2 correction is paid in both directions on the original carrier. -/
theorem subTwo_reciprocal {δ ε : ℝ} (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |subTwoMain N δ-reciprocalMain N δ| ≤ ε := by
  let τ := ε/50
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨T1,hT14,hT1⟩ := SingleUpperPrimePayment.denominator_payment hτ
  obtain ⟨T2,_,hT2⟩ := SingleUpperPrimePayment.reciprocal_mass_bound
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hden (p : ℕ) (hp : p ∈ P N) := hT1 N (by omega) p (mem_primeWindow.mp hp).1
    ((rpow_le_rpow_of_exponent_le hNr (show (1/15 : ℝ) ≤ left by norm_num [left])).trans
      (mem_primeWindow.mp hp).2.2.1)
  have hb : (∑ p ∈ P N, 1/(p : ℝ)) ≤ 5 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (fun _ hp => outer_closed hp)
      (by intros; positivity))
    exact hT2 N (by omega) left right (by norm_num [left])
      (by norm_num [left,right]) (by norm_num [right])
  rw [subTwoMain,reciprocalMain,← sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ P N, |primeWeight δ (log p/log N)/((p : ℝ)-2)-
        primeWeight δ (log p/log N)/(p : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P N, 10*τ*(1/(p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (hden p hp).1
      have hw := primeWeight_bounds hδhi (closed_coordinate hN2 (outer_closed hp))
      have hd0 : 0 ≤ 1/((p : ℝ)-2)-1/(p : ℝ) := sub_nonneg.mpr
        (one_div_le_one_div_of_le (by linarith) (by linarith))
      have hd1 : 1/((p : ℝ)-2)-1/(p : ℝ) ≤ τ*(1/(p : ℝ)) := by
        have hh := (hden p hp).2.1
        ring_nf at hh ⊢
        linarith
      rw [show primeWeight δ (log p/log N)/((p : ℝ)-2)-primeWeight δ (log p/log N)/(p : ℝ) =
        primeWeight δ (log p/log N)*(1/((p : ℝ)-2)-1/(p : ℝ)) by ring,
        abs_of_nonneg (mul_nonneg hw.1 hd0)]
      calc
        _ ≤ 10*(τ*(1/(p : ℝ))) := mul_le_mul hw.2 hd1 hd0 (by norm_num)
        _ = _ := by ring
    _ = (10*τ)*∑ p ∈ P N, 1/(p : ℝ) := (mul_sum ..).symm
    _ ≤ (10*τ)*5 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ε := by dsimp [τ]; ring

/-- Exact p-2 quadrature; its threshold precedes N. -/
theorem subTwo_integral {δ ε : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      |subTwoMain N δ-primeIntegral δ| ≤ ε := by
  obtain ⟨T1,hT14,hT1⟩ := subTwo_reciprocal hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := reciprocal_integral hδ hδhi (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  exact (abs_sub_le _ _ _).trans
    ((add_le_add (hT1 N (by omega)) (hT2 N (by omega))).trans (by linarith))

/-- A two-sided relative estimate is obtained from the actual li remainder. -/
theorem trueLi_relative {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → |liRatio N-1| ≤ ε := by
  obtain ⟨C,_hC,hrem⟩ := MathlibNt.SieveTheory.LiuWeight.eventually_abs_liuLogarithmicIntegralRemainder_le 0
  obtain ⟨T,hT⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hrem)
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨S,hS⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (C/ε)))
  refine ⟨max 4 (max T S),le_max_left _ _,?_⟩
  intro N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh : |logarithmicIntegral N-(N : ℝ)/log N| ≤ C*N/log (N : ℝ)^2 :=
    hT N (by omega) (by exact_mod_cast (show 2 ≤ N by omega))
  have hc : C/log (N : ℝ) ≤ ε := by
    apply (div_le_iff₀ hl).mpr
    have hb := (div_le_iff₀ hε).mp (hS N (by omega))
    linarith
  have he : liRatio N-1 = (logarithmicIntegral N-(N : ℝ)/log N)*(log N/(N : ℝ)) := by
    unfold liRatio
    field_simp
  rw [he,abs_mul,abs_of_pos (div_pos hl hNr)]
  calc
    _ ≤ (C*N/log (N : ℝ)^2)*(log N/(N : ℝ)) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = C/log (N : ℝ) := by field_simp
    _ ≤ ε := hc

/-- Exact normalization of the original B6, keeping the true li factor and
Euler p-2 denominators. No positivity of the gain coefficient is used. -/
theorem B6_exact {N : ℕ} {δ : ℝ} (hN : 2 ≤ N) (he : Even N) :
    B6 N δ = 4*liRatio N*subTwoMain N δ*truncatedSixthMassScale N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [B6,SingleUpperNormalization.theta_single_exact hN (P N) (by
    intro p hp
    have hpp := (mem_primeWindow.mp hp).1
    have hcop := (mem_primeWindow.mp hp).2.1
    have hp2 : 2 < p := by
      have hd : 2 ∣ N := even_iff_two_dvd.mp he
      have hpne : p ≠ 2 := by intro h; subst p; exact hpp.coprime_iff_not_dvd.mp hcop hd
      have := hpp.two_le
      omega
    exact ⟨hpp,hp2,hcop⟩)]
  have hs : (∑ p ∈ P N, 1/(((p : ℝ)-2)*((1/2-δ)-log p/log N))) = subTwoMain N δ := by
    apply sum_congr rfl
    intro p _hp
    simp only [primeWeight,div_eq_mul_inv,mul_inv_rev,one_mul]
  rw [hs]
  unfold liRatio truncatedSixthMassScale
  field_simp

/-- The actual B6 has a two-sided normalized integral error. All analytic
payments and the internal absolute-integral budget precede N. -/
theorem B6_integral_error {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      |B6 N δ-4*primeIntegral δ*truncatedSixthMassScale N| ≤ ε*truncatedSixthMassScale N := by
  let η := ε/(16*(|primeIntegral δ|+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T1,hT14,hT1⟩ := subTwo_integral hδ.le hδhi hη
  obtain ⟨T2,_,hT2⟩ := trueLi_relative hη
  obtain ⟨T3,_,hT3⟩ := trueLi_relative (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hN2 : 2 ≤ N := by omega
  have hscale : 0 ≤ truncatedSixthMassScale N := by
    unfold truncatedSixthMassScale
    have := (wuSingularSeries_pos N (show 0 < N by omega)).le
    positivity
  have hq := hT1 N (by omega)
  have hr := hT2 N (by omega)
  have hr1 := hT3 N (by omega)
  have hr2 : |liRatio N| ≤ 2 := by
    exact (abs_le.mpr ⟨by linarith [(abs_le.mp hr1).1],by linarith [(abs_le.mp hr1).2]⟩)
  have hb : |4*liRatio N*subTwoMain N δ-4*primeIntegral δ| ≤ ε := by
    rw [show 4*liRatio N*subTwoMain N δ-4*primeIntegral δ =
      4*liRatio N*(subTwoMain N δ-primeIntegral δ)+4*primeIntegral δ*(liRatio N-1) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have ha := mul_le_mul (mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ 4)) hq
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4*2)
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*|primeIntegral δ| by positivity)
    have hηeq : 16*(|primeIntegral δ|+1)*η = ε := by dsimp [η]; field_simp
    have hn := mul_nonneg (abs_nonneg (primeIntegral δ)) hη.le
    nlinarith only [ha,hh,hηeq,hn,hη.le]
  rw [B6_exact hN2 he,← sub_mul,abs_mul,abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_right hb hscale
end Wu2008DoubleSieve.HighSix
