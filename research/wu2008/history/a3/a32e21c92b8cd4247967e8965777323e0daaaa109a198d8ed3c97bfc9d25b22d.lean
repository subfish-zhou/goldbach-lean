import MathlibNt.Wu2008DoubleSieve.Gamma5MassPrimeFinite

/-!
# Uniform actual prime quadrature on every source rectangle

Both rectangle endpoints and the moving scale follow the common threshold.
Closed auxiliary sections are compared bilaterally with the original strict
ordered prime masks. All coprimality deletions and endpoint atoms are paid.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

theorem gamma5Mass_prime_lower {N : ℕ} {R A B α : ℝ}
    (hR : 1 < R) (hA : gamma5MassA ≤ A) (hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA) :
    ∀ p ∈ gamma5MassPrimes R A B, p.Prime ∧ (N : ℝ) ^ α ≤ (p : ℝ) := by
  intro p hp
  obtain ⟨hpp, hlo, _⟩ := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) B)).mp hp
  exact ⟨hpp, hZ.trans ((rpow_le_rpow_of_exponent_le hR.le hA).trans hlo)⟩

theorem gamma5Mass_row_discrepancy {N p : ℕ} {R C D α e : ℝ}
    (hN : 1 < N) (hα : 0 < α) (hR : 1 < R) (hp : p.Prime)
    (hC : gamma5MassA ≤ C) (hCD : C ≤ D) (hD : D ≤ gamma5ClassicalB)
    (hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA)
    (hquad : ∀ (f : ℝ → ℝ) (A B : ℝ),
      ContinuousOn f (Icc (1 / 10 : ℝ) (1 / 2)) →
      (∀ t ∈ Icc (1 / 10 : ℝ) (1 / 2), |f t| ≤ 4) →
      (∀ x ∈ Icc (1 / 10 : ℝ) (1 / 2), ∀ y ∈ Icc (1 / 10 : ℝ) (1 / 2),
        |f x - f y| ≤ 16 * |x - y|) →
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| < e) :
    |(∑ q ∈ gamma5MassRowPrimes N R C D p,
        gamma5MassH (gamma5MassCoordinate R p) (gamma5MassCoordinate R q) / q) -
      gamma5MassSection C D (gamma5MassCoordinate R p)| ≤
        e + 12 / (N : ℝ) ^ α + 4 / (α * (N : ℝ) ^ α) := by
  let t := gamma5MassCoordinate R p
  let P := gamma5MassPrimes R (gamma5MassSectionStart C D t) D
  let P' := P.filter (fun q => p < q ∧ (q : ℝ) < R ^ gamma5ClassicalB)
  let g := fun q : ℕ => gamma5MassH t (gamma5MassCoordinate R q) / q
  have hpow : 0 < (N : ℝ) ^ α := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hg (q : ℕ) : |g q| ≤ 4 / q := by
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
      abs_of_pos (gamma5Mass_H_bounds _ _).1]
    exact div_le_div_of_nonneg_right (gamma5Mass_H_bounds _ _).2 (Nat.cast_nonneg _)
  have hCpow := hZ.trans (rpow_le_rpow_of_exponent_le hR.le hC)
  have hb := gamma5Mass_row_boundary hR hp hCD hD hpow hCpow
    (by norm_num : (0 : ℝ) ≤ 4) g (fun q _ => hg q)
  have hdel := gamma5Mass_divisor_deletion hN hα (by norm_num : (0 : ℝ) ≤ 4)
    P' (fun q hq => gamma5Mass_prime_lower hR
      (hC.trans (gamma5Mass_start_bounds hCD t).1) hZ q (mem_filter.mp hq).1)
    g (fun q _ => hg q)
  have he : P'.filter (fun q => q.Coprime N) = gamma5MassRowPrimes N R C D p := by
    ext q
    simp only [P', P, gamma5MassRowPrimes, mem_filter, t, and_assoc]
  rw [he] at hdel
  have hs := gamma5Mass_start_bounds hCD t
  have hq := hquad (gamma5MassH t) (gamma5MassSectionStart C D t) D
    (gamma5Mass_H_continuous t)
    (fun u _ => by rw [abs_of_pos (gamma5Mass_H_bounds t u).1]; exact (gamma5Mass_H_bounds t u).2)
    (fun u _ v _ => gamma5Mass_H_second_lipschitz t u v)
    ((gamma5Mass_constants.1.trans hC).trans hs.1) hs.2
    (hD.trans gamma5Mass_constants.2.2.1)
  change |(∑ q ∈ P, g q) - gamma5MassSection C D t| < e at hq
  change |(∑ q ∈ P, g q) - ∑ q ∈ P', g q| ≤ 3 * 4 / (N : ℝ) ^ α at hb
  have h1 := abs_sub_le (∑ q ∈ gamma5MassRowPrimes N R C D p, g q)
    (∑ q ∈ P', g q) (gamma5MassSection C D t)
  have h2 := abs_sub_le (∑ q ∈ P', g q) (∑ q ∈ P, g q) (gamma5MassSection C D t)
  rw [abs_sub_comm] at hb hdel
  change |(∑ q ∈ gamma5MassRowPrimes N R C D p, g q) - gamma5MassSection C D t| ≤ _
  linarith

theorem gamma5Mass_pair_quadrature_finite {e : ℝ} (he : 0 < e) :
    ∀ᶠ R : ℝ in atTop, ∀ N : ℕ, 1 < N → ∀ α : ℝ, 0 < α →
      (N : ℝ) ^ α ≤ R ^ gamma5MassA →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → C ≤ D → D ≤ gamma5ClassicalB →
      |gamma5MassReciprocalPairs N R A B C D - gamma5MassRectangleIntegral A B C D| ≤
        6 * e + (60 + 36 / α) / (N : ℝ) ^ α := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    primeOrdered_weighted_uniform 4 16 e (by norm_num) (by norm_num) he,
    primeOrdered_weighted_uniform 16 104 e (by norm_num) (by norm_num) he,
    primeOrdered_reciprocal_uniform 1 (by norm_num)] with R hR hinner houter hmass
  intro N hN α hα hZ A B C D hA hAB hB hC hCD hD
  have hAa := gamma5Mass_constants.1.trans hA
  have hBb := hB.trans gamma5Mass_constants.2.2.1
  have hCc := gamma5Mass_constants.1.trans hC
  have hDd := hD.trans gamma5Mass_constants.2.2.1
  have hr := gamma5Mass_section_regular hCc hCD hDd
  let P := gamma5MassPrimes R A B
  let P' := P.filter (fun p => p.Coprime N)
  let I := ∫ t in A..B, gamma5MassSection C D t / t
  let E := e + 12 / (N : ℝ) ^ α + 4 / (α * (N : ℝ) ^ α)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmassP : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 := by
    have h := (le_abs_self _).trans (hmass A B hAa hAB hBb).le
    have hi := (primeOrdered_exponent_density_bounds hAa hAB hBb).2
    dsimp [P, gamma5MassPrimes]
    linarith
  have hmassP' : (∑ p ∈ P', 1 / (p : ℝ)) ≤ 5 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)).trans hmassP
  have hrow :
      |gamma5MassReciprocalPairs N R A B C D -
        ∑ p ∈ P', gamma5MassSection C D (gamma5MassCoordinate R p) / p| ≤ 5 * E := by
    rw [gamma5Mass_pairs_eq_rows hR hCD]
    change |(∑ p ∈ P', _) - ∑ p ∈ P', _| ≤ _
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ P', E / p := by
        apply sum_le_sum
        intro p hp
        rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact gamma5Mass_row_discrepancy hN hα hR
          ((gamma5Mass_coordinate_mem_iff hR p).mp (mem_filter.mp hp).1).1
          hC hCD hD hZ hinner
      _ = E * ∑ p ∈ P', 1 / (p : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ 5 * E := by nlinarith [mul_le_mul_of_nonneg_left hmassP' hE]
  have hdel := gamma5Mass_divisor_deletion hN hα (by norm_num : (0 : ℝ) ≤ 16)
    P (gamma5Mass_prime_lower hR hA hZ)
    (fun p => gamma5MassSection C D (gamma5MassCoordinate R p) / p)
    (fun p _ => by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
      exact div_le_div_of_nonneg_right (hr.1 _) (Nat.cast_nonneg _))
  have hquad := houter (gamma5MassSection C D) A B
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => hr.2 x y))
    (fun t _ => hr.1 t) (fun x _ y _ => hr.2 x y) hAa hAB hBb
  change |(∑ p ∈ P, gamma5MassSection C D (gamma5MassCoordinate R p) / p) - I| < e at hquad
  have h1 := abs_sub_le (gamma5MassReciprocalPairs N R A B C D)
    (∑ p ∈ P', gamma5MassSection C D (gamma5MassCoordinate R p) / p) I
  have h2 := abs_sub_le (∑ p ∈ P', gamma5MassSection C D (gamma5MassCoordinate R p) / p)
    (∑ p ∈ P, gamma5MassSection C D (gamma5MassCoordinate R p) / p) I
  rw [abs_sub_comm] at hdel
  rw [gamma5Mass_rectangle_eq hA hAB hB hC hCD hD]
  change |gamma5MassReciprocalPairs N R A B C D - I| ≤ _
  have heq : 5 * E + 16 / (α * (N : ℝ) ^ α) + e =
      6 * e + (60 + 36 / α) / (N : ℝ) ^ α := by dsimp [E]; ring
  linarith

/-- One threshold precedes the moving scale and all four rectangle endpoints. -/
theorem gamma5Mass_pair_quadrature_uniform {α β ε : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β * gamma5MassA) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, (N : ℝ) ^ β ≤ R →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma5ClassicalB →
      gamma5MassA ≤ C → C ≤ D → D ≤ gamma5ClassicalB →
      |gamma5MassReciprocalPairs N R A B C D - gamma5MassRectangleIntegral A B C D| < ε := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (gamma5Mass_pair_quadrature_finite (show 0 < ε / 12 by positivity))
  have hlarge := ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop R0)
  have hdecay : Tendsto (fun N : ℕ => (60 + 36 / α) / (N : ℝ) ^ α) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlarge, hdecay.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity)),
    eventually_ge_atTop (2 : ℕ)] with N hlargeN herr hN
  intro R hR A B C D hA hAB hB hC hCD hD
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA := by
    calc
      _ ≤ (N : ℝ) ^ (β * gamma5MassA) := rpow_le_rpow_of_exponent_le hN1 hαβ
      _ = ((N : ℝ) ^ β) ^ gamma5MassA := rpow_mul (Nat.cast_nonneg _) _ _
      _ ≤ _ := rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hR
        (by norm_num [gamma5MassA, gamma5ClassicalS])
  have h := hR0 R (hlargeN.trans hR) N (by omega) α hα hZ A B C D hA hAB hB hC hCD hD
  linarith

end Wu2008DoubleSieve
