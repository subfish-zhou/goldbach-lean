import MathlibNt.Wu2008DoubleSieve.Gamma6BaseKernel

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def gamma6BasePrimes (N : ℕ) (R A B cap : ℝ) : Finset ℕ :=
  ((gamma5MassPrimes R A B).filter (fun p : ℕ => (p : ℝ) < R ^ cap)).filter
    (fun p => p.Coprime N)

noncomputable def gamma6BasePairs (N : ℕ) (R A B C D : ℝ) : Finset (ℕ × ℕ) :=
  gamma6BasePrimes N R A B gamma6BaseB ×ˢ gamma6BasePrimes N R C D gamma6BaseF

noncomputable def gamma6BaseReciprocalPairs (N : ℕ) (R A B C D : ℝ) : ℝ :=
  ∑ x ∈ gamma6BasePairs N R A B C D,
    gamma6BaseH (gamma5MassCoordinate R x.1) (gamma5MassCoordinate R x.2) /
      ((x.1 : ℝ) * x.2)

theorem gamma6Base_pairs_eq_rows (N : ℕ) (R A B C D : ℝ) :
    gamma6BaseReciprocalPairs N R A B C D =
      ∑ p ∈ gamma6BasePrimes N R A B gamma6BaseB,
        (∑ q ∈ gamma6BasePrimes N R C D gamma6BaseF,
          gamma6BaseH (gamma5MassCoordinate R p) (gamma5MassCoordinate R q) / q) / p := by
  unfold gamma6BaseReciprocalPairs gamma6BasePairs
  rw [sum_product]
  apply sum_congr rfl
  intro p _
  rw [sum_div]
  apply sum_congr rfl
  intro q _
  ring

theorem gamma6Base_upper_atom {R A B cap Z M : ℝ}
    (hR : 1 < R) (hB : B ≤ cap) (hZ : 0 < Z) (hZA : Z ≤ R ^ A) (hM : 0 ≤ M)
    (g : ℕ → ℝ) (hg : ∀ p ∈ gamma5MassPrimes R A B, |g p| ≤ M / p) :
    |(∑ p ∈ gamma5MassPrimes R A B, g p) -
      ∑ p ∈ (gamma5MassPrimes R A B).filter (fun p : ℕ => (p : ℝ) < R ^ cap), g p| ≤ M / Z := by
  let P := gamma5MassPrimes R A B
  let E := P.filter (fun p : ℕ => ¬(p : ℝ) < R ^ cap)
  have hsub : E ⊆ {⌊R ^ cap⌋₊} := by
    intro p hp
    obtain ⟨hp, hn⟩ := mem_filter.mp hp
    have hu := ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) B)).mp hp).2.2
    have he : (p : ℝ) = R ^ cap :=
      le_antisymm (hu.trans (rpow_le_rpow_of_exponent_le hR.le hB)) (le_of_not_gt hn)
    have hf : p = ⌊R ^ cap⌋₊ := by rw [← he, Nat.floor_natCast]
    exact mem_singleton.mpr hf
  have hcard : E.card ≤ 1 := (Finset.card_le_card hsub).trans (by simp)
  have he : (∑ p ∈ P, g p) - ∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < R ^ cap), g p =
      ∑ p ∈ E, g p := by
    have h := sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < R ^ cap) g
    dsimp [E]
    linarith
  change |(∑ p ∈ P, g p) - _| ≤ _
  rw [he]
  calc
    _ ≤ ∑ p ∈ E, |g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ E, M / Z := by
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).1
      have hl := ((mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) B)).mp hp').2.1
      exact (hg p hp').trans (div_le_div_of_nonneg_left hM hZ (hZA.trans hl))
    _ = (E.card : ℝ) * (M / Z) := by simp
    _ ≤ 1 * (M / Z) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := one_mul _

theorem gamma6Base_window_discrepancy {N : ℕ} {R A B cap α M e : ℝ}
    (hN : 1 < N) (hα : 0 < α) (hR : 1 < R)
    (hA : gamma5MassA ≤ A) (hB : B ≤ cap)
    (hZ : (N : ℝ) ^ α ≤ R ^ gamma5MassA) (hM : 0 ≤ M)
    (f : ℝ → ℝ)
    (hf : ∀ p ∈ gamma5MassPrimes R A B, |f (gamma5MassCoordinate R p)| ≤ M)
    (hquad : |primeOrderedClosedSum R A B f - ∫ t in A..B, f t / t| < e) :
    |(∑ p ∈ gamma6BasePrimes N R A B cap, f (gamma5MassCoordinate R p) / p) -
      ∫ t in A..B, f t / t| ≤ e + M / (N : ℝ) ^ α + M / (α * (N : ℝ) ^ α) := by
  let P := gamma5MassPrimes R A B
  let P' := P.filter (fun p : ℕ => (p : ℝ) < R ^ cap)
  let g := fun p : ℕ => f (gamma5MassCoordinate R p) / p
  let I := ∫ t in A..B, f t / t
  have hpow : 0 < (N : ℝ) ^ α := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hg : ∀ p ∈ P, |g p| ≤ M / p := by
    intro p hp
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    exact div_le_div_of_nonneg_right (hf p hp) (Nat.cast_nonneg _)
  have hb := gamma6Base_upper_atom hR hB hpow
    (hZ.trans (rpow_le_rpow_of_exponent_le hR.le hA)) hM g hg
  have hd := gamma5Mass_divisor_deletion hN hα hM P'
    (fun p hp => gamma5Mass_prime_lower hR hA hZ p (mem_filter.mp hp).1)
    g (fun p hp => hg p (mem_filter.mp hp).1)
  change |(∑ p ∈ P, g p) - I| < e at hquad
  change |(∑ p ∈ P, g p) - ∑ p ∈ P', g p| ≤ _ at hb
  change |(∑ p ∈ P', g p) - ∑ p ∈ gamma6BasePrimes N R A B cap, g p| ≤ _ at hd
  have h1 := abs_sub_le (∑ p ∈ gamma6BasePrimes N R A B cap, g p) (∑ p ∈ P', g p) I
  have h2 := abs_sub_le (∑ p ∈ P', g p) (∑ p ∈ P, g p) I
  rw [abs_sub_comm] at hb hd
  change |(∑ p ∈ gamma6BasePrimes N R A B cap, g p) - I| ≤ _
  linarith

theorem gamma6Base_pair_quadrature_finite {e : ℝ} (he : 0 < e) :
    ∀ᶠ R : ℝ in atTop, ∀ N : ℕ, 1 < N → ∀ α : ℝ, 0 < α →
      (N : ℝ) ^ α ≤ R ^ gamma5MassA →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma6BaseB →
      gamma6BaseC ≤ C → C ≤ D → D ≤ gamma6BaseF →
      |gamma6BaseReciprocalPairs N R A B C D - gamma6BaseIntegral A B C D| ≤
        6 * e + (36 + 36 / α) / (N : ℝ) ^ α := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    primeOrdered_weighted_uniform 4 16 e (by norm_num) (by norm_num) he,
    primeOrdered_weighted_uniform 16 64 e (by norm_num) (by norm_num) he,
    primeOrdered_reciprocal_uniform 1 (by norm_num)] with R hR hinner houter hmass
  intro N hN α hα hZ A B C D hA hAB hB hC hCD hD
  have hCa : gamma5MassA ≤ C :=
    (by norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseC] : gamma5MassA ≤ gamma6BaseC).trans hC
  have hAa := gamma6Base_constants.1.trans hA
  have hBb : B ≤ 1 / 2 := hB.trans (by norm_num [gamma6BaseB])
  have hCc := gamma6Base_constants.1.trans hCa
  have hDd := hD.trans gamma6Base_constants.2.2.2.2.1
  have hr := gamma6Base_section_regular hCc hCD hDd
  let P := gamma5MassPrimes R A B
  let P' := gamma6BasePrimes N R A B gamma6BaseB
  let I := ∫ t in A..B, gamma6BaseSection C D t / t
  let E := e + 4 / (N : ℝ) ^ α + 4 / (α * (N : ℝ) ^ α)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmassP : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 := by
    have h := (le_abs_self _).trans (hmass A B hAa hAB hBb).le
    have hi := (primeOrdered_exponent_density_bounds hAa hAB hBb).2
    dsimp [P, gamma5MassPrimes]
    linarith
  have hsub : P' ⊆ P := (filter_subset _ _).trans (filter_subset _ _)
  have hmassP' : (∑ p ∈ P', 1 / (p : ℝ)) ≤ 5 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans hmassP
  have hrow :
      |gamma6BaseReciprocalPairs N R A B C D -
        ∑ p ∈ P', gamma6BaseSection C D (gamma5MassCoordinate R p) / p| ≤ 5 * E := by
    rw [gamma6Base_pairs_eq_rows]
    change |(∑ p ∈ P', _) - ∑ p ∈ P', _| ≤ _
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ p ∈ P', E / p := by
        apply sum_le_sum
        intro p _
        rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply gamma6Base_window_discrepancy hN hα hR hCa hD hZ (by norm_num)
        · intro q _
          rw [abs_of_pos (gamma6Base_H_bounds _ _).1]
          exact (gamma6Base_H_bounds _ _).2
        · apply hinner _ C D (gamma6Base_H_continuous _)
          · intro u _
            rw [abs_of_pos (gamma6Base_H_bounds _ _).1]
            exact (gamma6Base_H_bounds _ _).2
          · exact fun u _ v _ => gamma6Base_H_second _ u v
          · exact hCc
          · exact hCD
          · exact hDd
      _ = E * ∑ p ∈ P', 1 / (p : ℝ) := by rw [mul_sum]; simp only [mul_one_div]
      _ ≤ 5 * E := by nlinarith [mul_le_mul_of_nonneg_left hmassP' hE]
  have hquad := houter (gamma6BaseSection C D) A B
    (primeOrdered_continuous_of_lipschitz (fun x _ y _ => hr.2 x y))
    (fun t _ => hr.1 t) (fun x _ y _ => hr.2 x y) hAa hAB hBb
  have hout := gamma6Base_window_discrepancy hN hα hR hA hB hZ
    (by norm_num : (0 : ℝ) ≤ 16) (gamma6BaseSection C D) (fun p _ => hr.1 _) hquad
  have htri := abs_sub_le (gamma6BaseReciprocalPairs N R A B C D)
    (∑ p ∈ P', gamma6BaseSection C D (gamma5MassCoordinate R p) / p) I
  rw [gamma6Base_integral_eq hAB hB hCD hD]
  change |gamma6BaseReciprocalPairs N R A B C D - I| ≤ _
  change |(∑ p ∈ P', gamma6BaseSection C D (gamma5MassCoordinate R p) / p) - I| ≤ _ at hout
  have heq : 5 * E + (e + 16 / (N : ℝ) ^ α + 16 / (α * (N : ℝ) ^ α)) =
      6 * e + (36 + 36 / α) / (N : ℝ) ^ α := by dsimp [E]; ring
  linarith

theorem gamma6Base_pair_quadrature_uniform {α β ε : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β * gamma5MassA) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ R : ℝ, (N : ℝ) ^ β ≤ R →
      ∀ A B C D : ℝ,
      gamma5MassA ≤ A → A ≤ B → B ≤ gamma6BaseB →
      gamma6BaseC ≤ C → C ≤ D → D ≤ gamma6BaseF →
      |gamma6BaseReciprocalPairs N R A B C D - gamma6BaseIntegral A B C D| < ε := by
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp
    (gamma6Base_pair_quadrature_finite (show 0 < ε / 12 by positivity))
  have hlarge := ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop R0)
  have hdecay : Tendsto (fun N : ℕ => (36 + 36 / α) / (N : ℝ) ^ α) atTop (𝓝 0) :=
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
