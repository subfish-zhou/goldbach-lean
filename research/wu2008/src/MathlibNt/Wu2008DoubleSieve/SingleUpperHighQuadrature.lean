import MathlibNt.Wu2008DoubleSieve.SingleUpperPrimePayment

namespace Wu2008DoubleSieve.SingleUpperHighQuadrature
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperNormalization
open SingleUpperQuadrature SingleUpperPrimePayment
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The literal high count retains the equality atom at the splitting point. -/
noncomputable def highCount (N : ℕ) (δ r : ℝ) : ℝ :=
  ∑ p ∈ highPrimes N δ r,
    (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)

/-- Cancel the identical low count; no estimate on a signed subset is used. -/
theorem actual_high_density {δ ρ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, r ≤ 1/3 → highCount N δ r ≤
        highDensityMass N δ ρ r + ε * truncatedSixthMassScale N := by
  obtain ⟨T,hT4,hT⟩ := actual_low_high_upper hδ hδhi hρ hε
  refine ⟨T,hT4, ?_⟩
  intro N hN he r hr
  have h := hT N hN he r hr
  rw [count_split] at h
  change lowCount N δ r + highCount N δ r ≤ _ at h
  linarith

/-- Enlargement is only an inclusion, not removal of coprimality by equality. -/
theorem high_subset_closed {N : ℕ} {δ r : ℝ} :
    highPrimes N δ r ⊆ primesIcc ((N : ℝ)^((1/2-δ)/2)) ((N : ℝ)^r) := by
  intro p hp
  obtain ⟨hpw,hlo⟩ := mem_filter.mp hp
  have hw := mem_primeWindow.mp hpw
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr
    ⟨hw.1,hlo,hw.2.2.2.le⟩

theorem closed_coordinate {N p : ℕ} {a b : ℝ} (hN : 2 ≤ N)
    (hp : p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b)) :
    log (p : ℝ)/log N ∈ Icc a b := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hpp,hlo,hhi⟩ := (mem_primesIcc (rpow_nonneg hN0.le _)).mp hp
  have hl := log_le_log (rpow_pos_of_pos hN0 _) hlo
  have hu := log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p) hhi
  rw [log_rpow hN0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hN1)).mpr hl,
    (div_le_iff₀ (log_pos hN1)).mpr hu⟩

/-- The original high integral is nonnegative, including zero length. -/
theorem high_integral_nonneg {δ r : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (hrlo : (1/2-δ)/2 ≤ r) (hrhi : r ≤ 1/3) :
    0 ≤ ∫ t in ((1/2-δ)/2)..r, weight δ t/t := by
  apply intervalIntegral.integral_nonneg hrlo
  intro t ht
  have ht' : t ∈ Icc (1/15 : ℝ) (1/3) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact div_nonneg (weight_nonneg hδ hδhi ht') (by linarith [ht'.1])

/-- A coarse uniform bound is obtained from genuine compact regularity. -/
theorem high_integral_uniform_bound : ∃ B : ℝ, 0 < B ∧
    ∀ δ r : ℝ, 0 ≤ δ → δ ≤ 1/100 → (1/2-δ)/2 ≤ r → r ≤ 1/3 →
      (∫ t in ((1/2-δ)/2)..r, weight δ t/t) ≤ B := by
  obtain ⟨M,K,hM,_hK,hreg⟩ := weight_regular
  refine ⟨15*M, by positivity, ?_⟩
  intro δ r hδ hδhi hrlo hrhi
  have hb : ∀ t ∈ uIoc ((1/2-δ)/2) r, ‖weight δ t/t‖ ≤ 15*M := by
    intro t ht
    rw [uIoc_of_le hrlo] at ht
    have ht' : t ∈ Icc (1/15 : ℝ) (1/3) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have ht0 : 0 < t := by linarith [ht'.1]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
    apply (div_le_iff₀ ht0).mpr
    have h := (hreg δ hδ hδhi).2.1 t ht'
    have hm := mul_le_mul_of_nonneg_left ht'.1 (show 0 ≤ 15*M by positivity)
    nlinarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hrlo)] at h
  have hw : r-(1/2-δ)/2 ≤ 1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 15*M by positivity)
  exact (le_abs_self _).trans (h.trans (by nlinarith))

/-- Pointwise phi correction and the 6*tau loss are paid before enlargement.
The closed reciprocal mass bounds the whole loss, not individual atoms. -/
theorem high_weight_sum_upper {δ τ : ℝ} (hδ : 0 ≤ δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ r : ℝ, (1/2-δ)/2 ≤ r → r ≤ 1/3 →
      (∑ p ∈ highPrimes N δ r,
        (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
          ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N))) ≤
        (1+τ)*((∑ p ∈ primesIcc ((N : ℝ)^((1/2-δ)/2)) ((N : ℝ)^r),
          weight δ (log p/log N)/(p : ℝ)) + 300*τ) := by
  obtain ⟨TD,hTD4,hD⟩ := denominator_payment hτ
  obtain ⟨TM,_hTM4,hM⟩ := reciprocal_mass_bound
  refine ⟨max TD TM, hTD4.trans (le_max_left _ _), ?_⟩
  intro N hN r hrlo hrhi
  have hND : TD ≤ N := (le_max_left _ _).trans hN
  have hNM : TM ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTD4.trans hND
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hb : (1/15 : ℝ) ≤ (1/2-δ)/2 := by linarith
  let P := primesIcc ((N : ℝ)^((1/2-δ)/2)) ((N : ℝ)^r)
  have hcoord (p : ℕ) (hp : p ∈ P) : log (p : ℝ)/log N ∈ Icc (1/15 : ℝ) (1/3) := by
    have h := closed_coordinate (by omega : 2 ≤ N) hp
    exact ⟨hb.trans h.1,h.2.trans hrhi⟩
  have hterm (p : ℕ) (hp : p ∈ highPrimes N δ r) :
      (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
        ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) ≤
      (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := by
    have hpP := high_subset_closed hp
    have hpp := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mp hpP
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.1.pos
    have ht := hcoord p hpP
    have hc : (1/10 : ℝ) ≤ (1/2-δ)-log (p : ℝ)/log N := by linarith [ht.2]
    have hc0 : 0 < (1/2-δ)-log (p : ℝ)/log N := by linarith
    have hw := weight_nonneg hδ hδhi ht
    have hden := (hD N hND p hpp.1
      ((rpow_le_rpow_of_exponent_le hN1.le hb).trans hpp.2.1)).2.2
    have herr : 6*τ/((1/2-δ)-log (p : ℝ)/log N) ≤ 60*τ := by
      apply (div_le_iff₀ hc0).mpr
      have h := mul_le_mul_of_nonneg_left hc (show 0 ≤ 60*τ by positivity)
      nlinarith
    have heq :
        (wuUpperCoefficient (((1/2-δ)-log (p : ℝ)/log N)/truncatedSixthLowerAlpha)+6*τ) /
          ((Nat.totient p : ℝ)*((1/2-δ)-log (p : ℝ)/log N)) =
        (weight δ (log p/log N)+6*τ/((1/2-δ)-log (p : ℝ)/log N)) *
          (1/(Nat.totient p : ℝ)) := by
      unfold weight
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq]
    calc
      _ ≤ (weight δ (log p/log N)+6*τ/((1/2-δ)-log (p : ℝ)/log N))*((1+τ)/p) :=
        mul_le_mul_of_nonneg_left hden (add_nonneg hw (by positivity))
      _ ≤ (weight δ (log p/log N)+60*τ)*((1+τ)/p) :=
        mul_le_mul_of_nonneg_right (add_le_add le_rfl herr) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ highPrimes N δ r,
        (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := sum_le_sum hterm
    _ ≤ ∑ p ∈ P, (1+τ)*(weight δ (log p/log N)/(p : ℝ)+60*τ/(p : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg high_subset_closed
      intro p hp _
      have hw := weight_nonneg hδ hδhi (hcoord p hp)
      positivity
    _ = (1+τ)*((∑ p ∈ P, weight δ (log p/log N)/(p : ℝ)) +
        60*τ*(∑ p ∈ P, 1/(p : ℝ))) := by
      rw [← mul_sum, sum_add_distrib, mul_sum]
      congr 2
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      have hh := hM N hNM ((1/2-δ)/2) r hb hrlo hrhi
      have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 60*τ by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1+τ)
      dsimp [P] at *
      linarith

/-- Every analytic producer is consumed at a common threshold. The original
closed quadrature absorbs the extra upper atom, even for a zero-length interval. -/
theorem actual_high_with_tau {δ τ : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, (1/2-δ)/2 ≤ r → r ≤ 1/3 → highCount N δ r ≤
        (4*(1+τ)^2*((∫ t in ((1/2-δ)/2)..r, weight δ t/t)+301*τ)+τ) *
          truncatedSixthMassScale N := by
  obtain ⟨TA,hTA4,hA⟩ := actual_high_density hδ hδhi
    (show 0 < exp eulerMascheroniConstant*τ/2 by positivity) hτ
  obtain ⟨TD,_hTD4,hD⟩ := high_density_normalized hδ.le hδhi hτ hτ1
  obtain ⟨TS,_hTS4,hS⟩ := high_weight_sum_upper hδ.le hδhi hτ
  obtain ⟨TQ,_hTQ4,hQ⟩ := weighted_prime_quadrature hτ
  obtain ⟨TL,_hTL4,hL⟩ := trueLi_upper hτ
  refine ⟨max TA (max TD (max TS (max TQ TL))),
    hTA4.trans (le_max_left _ _), ?_⟩
  intro N hN he r hrlo hrhi
  have hNA : TA ≤ N := (le_max_left _ _).trans hN
  have hND : TD ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNS : TS ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNQ : TQ ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hNL : TL ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)))
  have hN4 := hTA4.trans hNA
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast (show 2 ≤ N by omega))
  have hcoef : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N := by positivity
  let I := ∫ t in ((1/2-δ)/2)..r, weight δ t/t
  have hI : 0 ≤ I := high_integral_nonneg hδ.le hδhi hrlo hrhi
  have hquad := (abs_lt.mp (hQ N hNQ δ ((1/2-δ)/2) r hδ.le hδhi
    (by linarith) hrlo hrhi)).2
  have hsum := (hS N hNS r hrlo hrhi).trans
    (mul_le_mul_of_nonneg_left
      (show (∑ p ∈ primesIcc ((N : ℝ)^((1/2-δ)/2)) ((N : ℝ)^r),
        weight δ (log p/log N)/(p : ℝ)) + 300*τ ≤ I+301*τ by dsimp [I]; linarith)
      (show 0 ≤ 1+τ by positivity))
  have hcoeff : 4*logarithmicIntegral N*wuSingularSeries N/log N ≤
      4*(1+τ)*truncatedSixthMassScale N := by
    calc
      _ ≤ 4*((1+τ)*(N : ℝ)/log N)*wuSingularSeries N/log N := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hL N hNL) (by norm_num)) hC)
          hlog.le
      _ = _ := by unfold truncatedSixthMassScale; ring
  have hdensity := (hD N hND he r hrhi).trans (mul_le_mul_of_nonneg_left hsum hcoef)
  have hpaid := hdensity.trans (mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (1+τ)*(I+301*τ) by positivity))
  have hactual := (hA N hNA he r hrhi).trans (add_le_add hpaid le_rfl)
  convert hactual using 1 <;> first | rfl | ring

/-- A continuous polynomial pays all multiplicative errors at once, before N.
No numerical parameter search or moving mesh is used. -/
theorem polynomial_budget {B ε : ℝ} (_hB : 0 < B) (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∀ I : ℝ, I ≤ B →
      4*(1+τ)^2*(I+301*τ)+τ ≤ 4*I+ε := by
  let f : ℝ → ℝ := fun t => 4*((1+t)^2-1)*B+1204*(1+t)^2*t+t
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨η,hη,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let τ := min (η/2) 1
  have hτ : 0 < τ := lt_min (half_pos hη) (by norm_num)
  have hτη : τ < η := (min_le_left _ _).trans_lt (by linarith)
  have hf : f τ < ε := by
    have hh := hclose (show dist τ 0 < η by simpa only [Real.dist_eq, sub_zero, abs_of_pos hτ] using hτη)
    have hf0 : f 0 = 0 := by dsimp [f]; ring
    rw [Real.dist_eq, hf0, sub_zero] at hh
    exact (le_abs_self _).trans_lt hh
  refine ⟨τ,hτ,min_le_right _ _, ?_⟩
  intro I hI
  have hn : 0 ≤ 4*((1+τ)^2-1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hI hn
  dsimp [f] at hf
  nlinarith

/-- Actual high count to the original classical integral, with threshold uniform
in the upper endpoint. Equality at the splitting point is never discarded. -/
theorem actual_high_classical_upper {δ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ r : ℝ, (1/2-δ)/2 ≤ r → r ≤ 1/3 → highCount N δ r ≤
        (4*(∫ t in ((1/2-δ)/2)..r, weight δ t/t)+ε)*truncatedSixthMassScale N := by
  obtain ⟨B,hB,hbound⟩ := high_integral_uniform_bound
  obtain ⟨τ,hτ,hτ1,hbudget⟩ := polynomial_budget hB hε
  obtain ⟨T,hT4,hT⟩ := actual_high_with_tau hδ hδhi hτ hτ1
  refine ⟨T,hT4, ?_⟩
  intro N hN he r hrlo hrhi
  have hN4 := hT4.trans hN
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hscale : 0 ≤ truncatedSixthMassScale N := by unfold truncatedSixthMassScale; positivity
  exact (hT N hN he r hrlo hrhi).trans (mul_le_mul_of_nonneg_right
    (hbudget _ (hbound δ r hδ.le hδhi hrlo hrhi)) hscale)

end Wu2008DoubleSieve.SingleUpperHighQuadrature
