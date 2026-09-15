import MathlibNt.Wu2008DoubleSieve.SingleUpperPrimePayment

namespace Wu2008DoubleSieve.SingleUpperLowQuadrature
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open SingleUpperNormalization SingleUpperQuadrature SingleUpperPrimePayment
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Closed coordinates retain both finite endpoint atoms. -/
theorem closed_coordinate {N p : ℕ} {a b : ℝ} (hN : 2 ≤ N)
    (hp : p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b)) :
    log p / log N ∈ Icc a b := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h := (mem_primesIcc (rpow_nonneg hN0.le _)).mp hp
  have hl := log_le_log (rpow_pos_of_pos hN0 _) h.2.1
  have hu := log_le_log (by exact_mod_cast h.1.pos : (0 : ℝ) < p) h.2.2
  rw [log_rpow hN0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hNr)).2 hl, (div_le_iff₀ (log_pos hNr)).2 hu⟩

/-- Removing coprimality is inclusion, not an equality of prime masks. -/
theorem window_subset_closed {N : ℕ} {a b : ℝ} :
    primeWindow N ((N : ℝ)^a) ((N : ℝ)^b) ⊆
      primesIcc ((N : ℝ)^a) ((N : ℝ)^b) := by
  intro p hp
  have h := mem_primeWindow.mp hp
  exact (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) _)).mpr
    ⟨h.1,h.2.2.1,h.2.2.2.le⟩

/-- Positivity of the coefficient follows from the genuine sieve function. -/
theorem coefficient_nonneg {δ t : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1/100)
    (ht : t ∈ Icc (1/15 : ℝ) (1/3)) :
    0 ≤ wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) := by
  have hs := argument_mem hδ hδhi ht
  have hs0 : 0 < ((1/2-δ)-t)/truncatedSixthLowerAlpha := by linarith [hs.1]
  unfold wuUpperCoefficient
  have := MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne.jr1965F_pos hs0
  positivity

/-- A sample displacement is paid once against reciprocal prime mass. -/
theorem sample_bound : ∃ L : ℝ, 0 < L ∧
    ∀ δ a t h η : ℝ, 0 ≤ δ → δ ≤ 1/100 →
      a ∈ Icc (1/15 : ℝ) (1/3) → t ∈ Icc (1/15 : ℝ) (1/3) →
      a ≤ t → t-a ≤ h → 0 ≤ η →
    0 ≤ (wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha)+η) /
      ((1/2-δ)-t) ∧
    (wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha)+η) /
      ((1/2-δ)-t) ≤ weight δ t + 10*(L*h/truncatedSixthLowerAlpha+η) := by
  obtain ⟨M,L,_hM,hL,_hMb,hLb⟩ := coefficient_regular
  refine ⟨L,hL,?_⟩
  intro δ a t h η hδ hδhi ha ht hat hth hη
  have hα : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hd : (1/10 : ℝ) ≤ (1/2-δ)-t := by linarith [ht.2]
  have hd0 : 0 < (1/2-δ)-t := by linarith
  have hh : 0 ≤ h := (sub_nonneg.mpr hat).trans hth
  have hb := hLb _ (argument_mem hδ hδhi ha) _ (argument_mem hδ hδhi ht)
  have he : ((1/2-δ)-a)/truncatedSixthLowerAlpha -
      ((1/2-δ)-t)/truncatedSixthLowerAlpha = (t-a)/truncatedSixthLowerAlpha := by ring
  rw [he, abs_div, abs_of_pos hα, abs_of_nonneg (sub_nonneg.mpr hat)] at hb
  have hm := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hth hα.le) hL.le
  have hdiff : wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha) -
      wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha) ≤
      L*h/truncatedSixthLowerAlpha := by
    calc
      _ ≤ |wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha) -
          wuUpperCoefficient (((1/2-δ)-t)/truncatedSixthLowerAlpha)| := le_abs_self _
      _ ≤ L*((t-a)/truncatedSixthLowerAlpha) := hb
      _ ≤ _ := by simpa only [mul_div_assoc] using hm
  refine ⟨div_nonneg (add_nonneg (coefficient_nonneg hδ hδhi ha) hη) hd0.le, ?_⟩
  unfold weight
  apply (div_le_iff₀ hd0).mpr
  rw [add_mul, div_mul_cancel₀ _ hd0.ne']
  have hpay := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 10*(L*h/truncatedSixthLowerAlpha+η) by positivity)
  nlinarith

/-- Exact arithmetic normalization before any estimate or prime-mask enlargement. -/
theorem packing_exact {N : ℕ} {δ η Δ a : ℝ} {n : ℕ}
    (hN : 2 ≤ N) (hΔ : 1 < Δ)
    (hp : ∀ j ∈ range n, ∀ p ∈ primeWindow N
      ((N : ℝ)^gamma5GainPoint N Δ a j)
      ((N : ℝ)^gamma5GainPoint N Δ a (j+1)), 2 < p) :
    packingMass N δ η Δ a n =
      (4*logarithmicIntegral N*wuSingularSeries N/log N) *
      ∑ j ∈ range n, ∑ p ∈ primeWindow N
        ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1)),
        (wuUpperCoefficient (((1/2-δ)-gamma5GainPoint N Δ a j)/truncatedSixthLowerAlpha)+η) /
          (((p : ℝ)-2)*((1/2-δ)-log p/log N)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  unfold packingMass
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hw : convolutionWuWindows N Δ (fun _ : Fin 1 => gamma5GainEnd N Δ a j) =
      (fun _ : Fin 1 => primeWindow N ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) := by
    funext k
    change primeWindow N (gamma5GainEnd N Δ a j / Δ) (gamma5GainEnd N Δ a j) = _
    rw [gamma5Gain_end_lower hNr hΔ]
    rfl
  rw [hw, theta_single_exact hN _ (fun p h =>
    ⟨(mem_primeWindow.mp h).1,hp j hj p h,(mem_primeWindow.mp h).2.1⟩)]
  rw [mul_left_comm, mul_sum]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

/-- Geometry is uniform in the number of microcells. -/
theorem grid_geometry {N p n j : ℕ} {Δ a : ℝ} (hN : 2 ≤ N) (hΔ : 1 < Δ)
    (ha : 1/15 ≤ a) (hn : gamma5GainPoint N Δ a n ≤ 1/3) (hj : j ∈ range n)
    (hp : p ∈ primeWindow N ((N : ℝ)^gamma5GainPoint N Δ a j)
      ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) :
    gamma5GainPoint N Δ a j ∈ Icc (1/15 : ℝ) (1/3) ∧
    log p/log N ∈ Icc (1/15 : ℝ) (1/3) ∧
    gamma5GainPoint N Δ a j ≤ log p/log N ∧
    log p/log N - gamma5GainPoint N Δ a j ≤ gamma5GainStep N Δ ∧
    (N : ℝ)^(1/15 : ℝ) ≤ p := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hm := (gamma5Gain_point_strictMono hNr hΔ a).monotone
  have hjn : j+1 ≤ n := by have := mem_range.mp hj; omega
  have hja : a ≤ gamma5GainPoint N Δ a j := by
    simpa only [gamma5GainPoint, Nat.cast_zero, zero_mul, add_zero] using hm (Nat.zero_le j)
  have hjb : gamma5GainPoint N Δ a (j+1) ≤ 1/3 := (hm hjn).trans hn
  have ht := closed_coordinate hN (window_subset_closed hp)
  have hstep : gamma5GainPoint N Δ a (j+1) =
      gamma5GainPoint N Δ a j + gamma5GainStep N Δ := by
    unfold gamma5GainPoint
    push_cast
    ring
  refine ⟨⟨ha.trans hja,(hm (by omega)).trans hjb⟩,
    ⟨(ha.trans hja).trans ht.1,ht.2.trans hjb⟩,ht.1,?_,?_⟩
  · rw [hstep] at ht
    linarith [ht.2]
  · exact (rpow_le_rpow_of_exponent_le hNr.le (ha.trans hja)).trans
      (mem_primeWindow.mp hp).2.2.1

/-- The complete grid error is paid against one mass bounded by five.
No Mertens or quadrature error is multiplied by the microcell count. -/
theorem packing_prime_upper : ∃ L : ℝ, 0 < L ∧
    ∀ τ : ℝ, 0 < τ → ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∀ δ η Δ a : ℝ, ∀ n : ℕ, 0 ≤ δ → δ ≤ 1/100 → 0 ≤ η → 1 < Δ →
      1/15 ≤ a → gamma5GainPoint N Δ a n ≤ 1/3 →
    packingMass N δ η Δ a n ≤
      (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+τ) *
      ((∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        weight δ (log p/log N)/(p : ℝ)) +
        50*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+η)) := by
  obtain ⟨L,hL,hSample⟩ := sample_bound
  refine ⟨L,hL,?_⟩
  intro τ hτ
  obtain ⟨TD,hTD4,hD⟩ := denominator_payment hτ
  obtain ⟨TR,_hTR4,hR⟩ := reciprocal_mass_bound
  refine ⟨max TD TR,hTD4.trans (le_max_left _ _),?_⟩
  intro N hN δ η Δ a n hδ hδhi hη hΔ ha hn
  have hND : TD ≤ N := (le_max_left _ _).trans hN
  have hNR : TR ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTD4.trans hND
  have hN2 : 2 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hstep := gamma5Gain_step_pos hNr hΔ
  have hα : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  let E := 10*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+η)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast hN2)
  have hnorm : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N :=
    div_nonneg (by positivity) (log_pos hNr).le
  have hgeom (j : ℕ) (hj : j ∈ range n) (p : ℕ)
      (hp : p ∈ primeWindow N ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) := grid_geometry hN2 hΔ ha hn hj hp
  have hden (j : ℕ) (hj : j ∈ range n) (p : ℕ)
      (hp : p ∈ primeWindow N ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) :=
    hD N hND p (mem_primeWindow.mp hp).1 (hgeom j hj p hp).2.2.2.2
  rw [packing_exact hN2 hΔ (fun j hj p hp => (hden j hj p hp).1)]
  have hsum : (∑ j ∈ range n, ∑ p ∈ primeWindow N
      ((N : ℝ)^gamma5GainPoint N Δ a j)
      ((N : ℝ)^gamma5GainPoint N Δ a (j+1)),
      (wuUpperCoefficient (((1/2-δ)-gamma5GainPoint N Δ a j)/truncatedSixthLowerAlpha)+η) /
        (((p : ℝ)-2)*((1/2-δ)-log p/log N))) ≤
      (1+τ)*(∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        (weight δ (log p/log N)+E)/(p : ℝ)) := by
    rw [grid_sum hN2 hΔ, mul_sum]
    apply sum_le_sum
    intro j hj
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨haj,ht,hat,hth,_hpmin⟩ := hgeom j hj p hp
    have hs := hSample δ _ _ _ η hδ hδhi haj ht hat hth hη
    have hd := (hden j hj p hp).2.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
    calc
      _ = ((wuUpperCoefficient (((1/2-δ)-gamma5GainPoint N Δ a j)/truncatedSixthLowerAlpha)+η) /
          ((1/2-δ)-log p/log N)) * (1/((p : ℝ)-2)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ ((wuUpperCoefficient (((1/2-δ)-gamma5GainPoint N Δ a j)/truncatedSixthLowerAlpha)+η) /
          ((1/2-δ)-log p/log N)) * ((1+τ)/(p : ℝ)) := mul_le_mul_of_nonneg_left hd hs.1
      _ ≤ (weight δ (log p/log N)+E)*((1+τ)/(p : ℝ)) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      _ = _ := by ring
  have hab : a ≤ gamma5GainPoint N Δ a n := by
    unfold gamma5GainPoint
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hstep.le)
  have hclosed : (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
      (weight δ (log p/log N)+E)/(p : ℝ)) ≤
      ∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        (weight δ (log p/log N)+E)/(p : ℝ) := by
    apply sum_le_sum_of_subset_of_nonneg window_subset_closed
    intro p hp _
    have ht := closed_coordinate hN2 hp
    exact div_nonneg (add_nonneg (weight_nonneg hδ hδhi
      ⟨ha.trans ht.1,ht.2.trans hn⟩) hE) (Nat.cast_nonneg p)
  have hmass := hR N hNR a _ ha hab hn
  have hpay : (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
      (weight δ (log p/log N)+E)/(p : ℝ)) ≤
      (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        weight δ (log p/log N)/(p : ℝ)) +
        50*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+η) := by
    simp_rw [add_div]
    rw [sum_add_distrib]
    have heq : (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n), E/(p : ℝ)) =
        E*(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n), 1/(p : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hmass hE
    dsimp [E] at hh
    linarith
  calc
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*
        ((1+τ)*(∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
          (weight δ (log p/log N)+E)/(p : ℝ))) := mul_le_mul_of_nonneg_left hsum hnorm
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*
        ((1+τ)*((∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
          weight δ (log p/log N)/(p : ℝ)) +
          50*(L*gamma5GainStep N Δ/truncatedSixthLowerAlpha+η))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hclosed.trans hpay) (by positivity)) hnorm
    _ = _ := by ring

end Wu2008DoubleSieve.SingleUpperLowQuadrature
