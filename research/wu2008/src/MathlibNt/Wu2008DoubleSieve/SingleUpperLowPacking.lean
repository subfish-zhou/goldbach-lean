import MathlibNt.Wu2008DoubleSieve.SingleUpperSplice
import MathlibNt.Wu2008DoubleSieve.Gamma5GainGrid

namespace Wu2008DoubleSieve.SingleUpperLowPacking
open Finset Real Filter SingleUpperCounts SingleUpperSplice
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- Even if p is below the cutoff, removing it only enlarges the source count. -/
theorem count_le_source (N p : ℕ) (z : ℝ) :
    (sieveCount N p N z : ℝ) ≤ (sourceSieveCount N p (p*N) z : ℝ) := by
  unfold sieveCount sourceSieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (dvd_mul_right p N)]
  apply Int.cast_le.mpr
  apply Int.ofNat_le.mpr
  apply card_le_card
  intro n hn
  obtain ⟨hnc, hs⟩ := mem_filter.mp hn
  apply mem_filter.mpr
  refine ⟨hnc, hs.1, hs.2.1, ?_⟩
  intro q hq hc hqz
  exact hs.2.2 q hq (Nat.coprime_mul_iff_right.mp hc).2 hqz

/-- A one-prime source Phi is the actual sum, with its varying cutoff. -/
theorem phi_single (N : ℕ) (δ s : ℝ) (P : Finset ℕ) :
    wuBoxPhi N δ (fun _ : Fin 1 => P) s =
      ∑ p ∈ P, (sourceSieveCount N p (p*N) (wuLocalCutoff N δ p s) : ℝ) := by
  unfold wuBoxPhi convolutionSieveCount
  exact single_weighted_sum P _

/-- The sample uses the lower exponent, so the source cutoff is no larger
than the target cutoff. The direction is essential for an upper bound. -/
theorem cell_cutoff_le {N p : ℕ} {δ a : ℝ}
    (hN : 2 ≤ N) (hp : 0 < p) (ha : a < 1/2-δ)
    (hpa : (N : ℝ)^a ≤ (p : ℝ)) :
    wuLocalCutoff N δ p (((1/2-δ)-a)/truncatedSixthLowerAlpha) ≤
      (N : ℝ)^truncatedSixthLowerAlpha := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have ha0 : 0 < truncatedSixthLowerAlpha := by norm_num [truncatedSixthLowerAlpha]
  have hs : 0 < ((1/2-δ)-a)/truncatedSixthLowerAlpha := div_pos (sub_pos.mpr ha) ha0
  have hquot : (N : ℝ)^(1/2-δ)/(p : ℝ) ≤ (N : ℝ)^((1/2-δ)-a) := by
    calc
      _ ≤ (N : ℝ)^(1/2-δ)/(N : ℝ)^a :=
        div_le_div_of_nonneg_left (rpow_nonneg hN0.le _) (rpow_pos_of_pos hN0 _) hpa
      _ = _ := (rpow_sub hN0 _ _).symm
  unfold wuLocalCutoff
  calc
    _ ≤ ((N : ℝ)^((1/2-δ)-a))^(1/(((1/2-δ)-a)/truncatedSixthLowerAlpha)) :=
      rpow_le_rpow (by positivity) hquot (by positivity)
    _ = _ := by
      rw [← rpow_mul hN0.le]
      congr 1
      rw [one_div_div, mul_div_cancel₀ _ (sub_pos.mpr ha).ne']

/-- Uniform actual upper for each legal microcell. This consumes the accepted
all-s Phi upper, not any asserted extension of the Rosser main density. -/
theorem cell_upper {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1 + 2*log (N : ℝ)^(-4 : ℝ) →
      ∀ a b : ℝ, truncatedSixthLowerAlpha/2 ≤ a → a ≤ b → b ≤ (1/2-δ)/2 →
        (N : ℝ)^b / Δ = (N : ℝ)^a →
      (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^b),
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
      (wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha)+η) *
        boxTheta N ((N : ℝ)^(1/2-δ))
          (convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ)^b)) := by
  obtain ⟨T, hT⟩ := wu_boxPhi_upper_source_bounded 1 le_rfl hδ (by linarith) hη
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he Δ hΔlo hΔhi a b ha hab hb hcell
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have has : a < 1/2-δ := by linarith
  have hs : 1 ≤ ((1/2-δ)-a)/truncatedSixthLowerAlpha := by
    apply (le_div_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hs10 : ((1/2-δ)-a)/truncatedSixthLowerAlpha ≤ 10 := by
    apply (div_le_iff₀ (by norm_num [truncatedSixthLowerAlpha])).mpr
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hv : ∀ _j : Fin 1, (N : ℝ)^(δ^(1+1)) ≤ (N : ℝ)^b := by
    intro _j
    apply rpow_le_rpow_of_exponent_le hN1
    have hd : δ^2 ≤ (1/100 : ℝ)^2 := pow_le_pow_left₀ hδ.le hδhi 2
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hpref : boxSquaredPrefixes ((N : ℝ)^(1/2-δ)) (fun _ : Fin 1 => (N : ℝ)^b) := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
    rw [pow_two, ← rpow_add hN0]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hbox := (hT N hNT he 1 le_rfl Δ hΔlo hΔhi
    (fun _ => (N : ℝ)^b) (fun _ _ _ => le_rfl) hv hpref
    (((1/2-δ)-a)/truncatedSixthLowerAlpha) hs hs10).1
  have hw : convolutionWuWindows N Δ (fun _ : Fin 1 => (N : ℝ)^b) =
      (fun _ : Fin 1 => primeWindow N ((N : ℝ)^a) ((N : ℝ)^b)) := by
    funext j
    simp only [convolutionWuWindows, hcell]
  change _ ≤ (wuUpperCoefficient (((1/2-δ)-a)/truncatedSixthLowerAlpha)+η)*_ at hbox
  apply le_trans _ hbox
  rw [hw, phi_single]
  apply sum_le_sum
  intro p hp
  exact (count_le_source N p _).trans (by
    exact_mod_cast sourceSieveCount_antitone N p (p*N)
      (cell_cutoff_le (by omega) (mem_primeWindow.mp hp).1.pos has (mem_primeWindow.mp hp).2.2.1))

noncomputable def packingMass (N : ℕ) (δ η Δ a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n,
    (wuUpperCoefficient (((1/2-δ)-gamma5GainPoint N Δ a j)/truncatedSixthLowerAlpha)+η) *
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ (fun _ : Fin 1 => gamma5GainEnd N Δ a j))

/-- An exact microgrid of arbitrary finite length. The original half-open
convention retains every prime on a mesh boundary exactly once. -/
theorem grid_sum {N : ℕ} {Δ : ℝ} (hN : 2 ≤ N) (hΔ : 1 < Δ)
    (a : ℝ) (n : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n), f p) =
      ∑ j ∈ range n, ∑ p ∈ primeWindow N
        ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1)), f p := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  simp_rw [gamma5Gain_point_power hNr hΔ]
  have h := reboxingAlpha_sum_partition (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) a)
    hΔ N n f (t := 1)
  simpa only [reboxingAlpha_zero, div_one, rpow_one, Nat.cast_add, Nat.cast_one] using h

/-- The same cutoff chosen before all cells pays every actual source Phi.
No assumption is made on the number of cells, which may grow with N. -/
theorem grid_upper {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1 + 2*log (N : ℝ)^(-4 : ℝ) →
      ∀ a : ℝ, ∀ n : ℕ, truncatedSixthLowerAlpha/2 ≤ a →
        gamma5GainPoint N Δ a n ≤ (1/2-δ)/2 →
      (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
        packingMass N δ η Δ a n := by
  obtain ⟨T, hT4, hT⟩ := cell_upper hδ hδhi hη
  refine ⟨T, hT4, ?_⟩
  intro N hN he Δ hΔlo hΔhi a n ha hn
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hΔ : 1 < Δ := by
    have hp : 0 < log (N : ℝ)^(-4 : ℝ) := rpow_pos_of_pos (log_pos hNr) _
    linarith
  have hm := (gamma5Gain_point_strictMono hNr hΔ a).monotone
  rw [grid_sum (by omega) hΔ]
  apply sum_le_sum
  intro j hj
  have hjn : j+1 ≤ n := by have := mem_range.mp hj; omega
  have haj : a ≤ gamma5GainPoint N Δ a j := by
    simpa only [gamma5GainPoint, Nat.cast_zero, zero_mul, add_zero] using hm (Nat.zero_le j)
  exact hT N hN he Δ hΔlo hΔhi _ _ (ha.trans haj) (hm (by omega))
    ((hm hjn).trans hn) (gamma5Gain_end_lower hNr hΔ a j)

/-- End-anchored packing: the last endpoint is exactly c/2, not a shortened
power window. The first cell may slightly extend below alpha. -/
noncomputable def packingSize (N : ℕ) (δ Δ : ℝ) : ℕ :=
  ⌊(((1/2-δ)/2-truncatedSixthLowerAlpha)/gamma5GainStep N Δ)⌋₊ + 1

noncomputable def packingStart (N : ℕ) (δ Δ : ℝ) : ℝ :=
  (1/2-δ)/2 - (packingSize N δ Δ : ℝ)*gamma5GainStep N Δ

 theorem packing_endpoint (N : ℕ) (δ Δ : ℝ) :
    gamma5GainPoint N Δ (packingStart N δ Δ) (packingSize N δ Δ) = (1/2-δ)/2 := by
  unfold gamma5GainPoint packingStart
  ring

/-- Symbolic floor bounds, with no numerical computation or prime enumeration. -/
theorem packing_start_bounds {N : ℕ} {δ Δ : ℝ}
    (hN : 2 ≤ N) (hδ : δ ≤ 1/100) (hΔ : 1 < Δ) :
    truncatedSixthLowerAlpha-gamma5GainStep N Δ ≤ packingStart N δ Δ ∧
      packingStart N δ Δ < truncatedSixthLowerAlpha := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hs := gamma5Gain_step_pos hNr hΔ
  have hl : 0 ≤ (1/2-δ)/2-truncatedSixthLowerAlpha := by
    norm_num [truncatedSixthLowerAlpha] at *
    linarith
  have hf := (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hl hs.le))
  have hc := (div_lt_iff₀ hs).mp
    (Nat.lt_floor_add_one (((1/2-δ)/2-truncatedSixthLowerAlpha)/gamma5GainStep N Δ))
  unfold packingStart packingSize
  push_cast
  constructor <;> linarith

/-- A genuine legal Delta family has vanishing exponent mesh. -/
theorem mesh_small {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ Δ : ℝ, 1 + log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1 + 2*log (N : ℝ)^(-4 : ℝ) →
        gamma5GainStep N Δ ≤ ε := by
  have ht : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (max 1 (3/ε))))
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN Δ hΔlo hΔhi
  have hl := hM N ((le_max_right _ _).trans hN)
  have hl1 : 1 ≤ log (N : ℝ) := (le_max_left _ _).trans hl
  have hsmall := rpow_le_one_of_one_le_of_nonpos hl1 (by norm_num : (-4 : ℝ) ≤ 0)
  have hΔ0 : 0 < Δ := by
    have hp := rpow_nonneg (le_trans (by norm_num) hl1) (-4 : ℝ)
    linarith
  have hlogΔ : log Δ ≤ 3 := (log_le_sub_one_of_pos hΔ0).trans (by linarith)
  unfold gamma5GainStep
  apply (div_le_iff₀ (by linarith : 0 < log (N : ℝ))).mpr
  have hb := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hl)
  nlinarith

/-- The complete low segment of every original window is actually covered.
The source grid ends exactly at the low/high split; the high equality atom
is not inserted here. Only the harmless lower outer cell is enlarged. -/
theorem low_packing_upper {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1 + 2*log (N : ℝ)^(-4 : ℝ) → ∀ r : ℝ,
      lowCount N δ r ≤
        packingMass N δ η Δ (packingStart N δ Δ) (packingSize N δ Δ) := by
  obtain ⟨TG, hTG4, hG⟩ := grid_upper hδ hδhi hη
  obtain ⟨TM, _, hM⟩ := mesh_small (show 0 < truncatedSixthLowerAlpha/2 by
    norm_num [truncatedSixthLowerAlpha])
  refine ⟨max TG TM, hTG4.trans (le_max_left _ _), ?_⟩
  intro N hN he Δ hΔlo hΔhi r
  have hNG : TG ≤ N := (le_max_left _ _).trans hN
  have hNM : TM ≤ N := (le_max_right _ _).trans hN
  have hN4 := hTG4.trans hNG
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hΔ : 1 < Δ := by
    have hp : 0 < log (N : ℝ)^(-4 : ℝ) := rpow_pos_of_pos (log_pos hNr) _
    linarith
  have hb := packing_start_bounds (by omega : 2 ≤ N) hδhi hΔ
  have hm := hM N hNM Δ hΔlo hΔhi
  have hg := hG N hNG he Δ hΔlo hΔhi (packingStart N δ Δ) (packingSize N δ Δ)
    (by linarith) ((packing_endpoint N δ Δ).le)
  rw [packing_endpoint] at hg
  apply le_trans _ hg
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hw := mem_primeWindow.mp (mem_filter.mp hp).1
    exact mem_primeWindow.mpr ⟨hw.1, hw.2.1,
      (rpow_le_rpow_of_exponent_le hNr.le hb.2.le).trans hw.2.2.1,
      (mem_filter.mp hp).2⟩
  · intro p _ _
    unfold sieveCount
    positivity

/-- Actual low packing plus the masked high density, on the full window.
This is still a finite weighted expression, not a Glin endpoint. -/
theorem packed_actual_upper {δ η ρ ε : ℝ} (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) (hη : 0 < η) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1 + log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1 + 2*log (N : ℝ)^(-4 : ℝ) →
      ∀ r : ℝ, r ≤ 1/3 →
      (U N r : ℝ) ≤
        packingMass N δ η Δ (packingStart N δ Δ) (packingSize N δ Δ) +
        highDensityMass N δ ρ r + ε*truncatedSixthMassScale N := by
  obtain ⟨TL, hTL4, hL⟩ := low_packing_upper hδ hδhi hη
  obtain ⟨TH, _, hH⟩ := actual_low_high_upper hδ hδhi hρ hε
  refine ⟨max TL TH, hTL4.trans (le_max_left _ _), ?_⟩
  intro N hN he Δ hΔlo hΔhi r hr
  have hl := hL N ((le_max_left _ _).trans hN) he Δ hΔlo hΔhi r
  have hh := hH N ((le_max_right _ _).trans hN) he r hr
  linarith

end Wu2008DoubleSieve.SingleUpperLowPacking
