import MathlibNt.Wu2008DoubleSieve.SingleUpperHSource
import MathlibNt.Wu2008DoubleSieve.SingleUpperNormalization

namespace Wu2008DoubleSieve.SingleUpperHPacking
open Finset Set Real Filter SingleUpperCounts SingleUpperSplice SingleUpperLowPacking
open SingleUpperHSource SingleUpperNormalization
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- A canonical coarse predecessor, retaining the labels of every fine cell. -/
noncomputable def sample (Q : Finset ℝ) (a : ℝ) : ℝ :=
  if h : (Q.filter (fun q => q ≤ a)).Nonempty then
    (Q.filter (fun q => q ≤ a)).max' h
  else truncatedSixthLowerAlpha/2

theorem sample_mem_le {Q : Finset ℝ} {a : ℝ}
    (hQ : truncatedSixthLowerAlpha/2 ∈ Q) (ha : truncatedSixthLowerAlpha/2 ≤ a) :
    sample Q a ∈ Q ∧ sample Q a ≤ a := by
  have h : (Q.filter (fun q => q ≤ a)).Nonempty :=
    ⟨truncatedSixthLowerAlpha/2,mem_filter.mpr ⟨hQ,ha⟩⟩
  unfold sample
  rw [dif_pos h]
  exact mem_filter.mp (max'_mem _ h)

noncomputable def packingMass (Q : Finset ℝ) (N : ℕ) (δ η Δ a : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n,
    (effective δ (argument δ (sample Q (gamma5GainPoint N Δ a j)))+η) *
      boxTheta N ((N : ℝ)^(1/2-δ))
        (convolutionWuWindows N Δ (fun _ : Fin 1 => gamma5GainEnd N Δ a j))

/-- No threshold depends on N, the fine-cell count, or the fine-cell labels. -/
theorem grid_upper {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η)
    (Q : Finset ℝ) (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ a : ℝ, ∀ n : ℕ, truncatedSixthLowerAlpha/2 ≤ a →
        gamma5GainPoint N Δ a n ≤ (1/2-δ)/2 →
      (∑ p ∈ primeWindow N ((N : ℝ)^a) ((N : ℝ)^gamma5GainPoint N Δ a n),
        (sieveCount N p N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ)) ≤
        packingMass Q N δ η Δ a n := by
  obtain ⟨T,hT4,hT⟩ := finite_samples hδ hδhi hη Q hQ
  refine ⟨T,hT4,?_⟩
  intro N hN he Δ hΔlo hΔhi a n ha hn
  have hN4 := hT4.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 2 ≤ N by omega)
  have hΔ : 1 < Δ := by
    have hp : 0 < log (N : ℝ)^(-4 : ℝ) := rpow_pos_of_pos (log_pos hNr) _
    linarith
  have hm := (gamma5Gain_point_strictMono hNr hΔ a).monotone
  rw [SingleUpperLowPacking.grid_sum (by omega) hΔ]
  apply sum_le_sum
  intro j hj
  have hjn : j+1 ≤ n := by have := mem_range.mp hj; omega
  have haj : a ≤ gamma5GainPoint N Δ a j := by
    simpa only [gamma5GainPoint,Nat.cast_zero,zero_mul,add_zero] using hm (Nat.zero_le j)
  have hs := sample_mem_le hanchor (ha.trans haj)
  exact hT N hN he _ hs.1 Δ hΔlo hΔhi _ _ hs.2 (hm (by omega))
    ((hm hjn).trans hn) (gamma5Gain_end_lower hNr hΔ a j)

/-- End-anchored packing covers the complete original low segment, including
its lower overhang, without dropping a prime on a source boundary. -/
theorem low_packing_upper {δ η : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 < η)
    (Q : Finset ℝ) (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) → ∀ r : ℝ,
      lowCount N δ r ≤ packingMass Q N δ η Δ
        (packingStart N δ Δ) (packingSize N δ Δ) := by
  obtain ⟨TG,hTG4,hG⟩ := grid_upper hδ hδhi hη Q hanchor hQ
  obtain ⟨TM,_,hM⟩ := mesh_small (show 0 < truncatedSixthLowerAlpha/2 by
    norm_num [truncatedSixthLowerAlpha])
  refine ⟨max TG TM,hTG4.trans (le_max_left _ _),?_⟩
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
    exact mem_primeWindow.mpr ⟨hw.1,hw.2.1,
      (rpow_le_rpow_of_exponent_le hNr.le hb.2.le).trans hw.2.2.1,
      (mem_filter.mp hp).2⟩
  · intro p _ _
    unfold sieveCount
    positivity

/-- The actual Theta supplies 4, true li, and p-2 before any asymptotic
payment. The prime mask, multiplicities, and full source are unchanged. -/
theorem packing_exact {Q : Finset ℝ} {N : ℕ} {δ η Δ a : ℝ} {n : ℕ}
    (hN : 2 ≤ N) (hΔ : 1 < Δ)
    (hp : ∀ j ∈ range n, ∀ p ∈ primeWindow N
      ((N : ℝ)^gamma5GainPoint N Δ a j)
      ((N : ℝ)^gamma5GainPoint N Δ a (j+1)), 2 < p) :
    packingMass Q N δ η Δ a n =
      (4*logarithmicIntegral N*wuSingularSeries N/log N) *
      ∑ j ∈ range n, ∑ p ∈ primeWindow N
        ((N : ℝ)^gamma5GainPoint N Δ a j)
        ((N : ℝ)^gamma5GainPoint N Δ a (j+1)),
        (effective δ (argument δ (sample Q (gamma5GainPoint N Δ a j)))+η) /
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
  rw [hw,theta_single_exact hN _ (fun p h =>
    ⟨(mem_primeWindow.mp h).1,hp j hj p h,(mem_primeWindow.mp h).2.1⟩)]
  rw [mul_left_comm,mul_sum]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

/-- Direct full U bound, not the difference of two unrelated upper bounds. -/
theorem packed_actual_upper {δ η ρ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hη : 0 < η) (hρ : 0 < ρ) (hε : 0 < ε)
    (Q : Finset ℝ) (hanchor : truncatedSixthLowerAlpha/2 ∈ Q)
    (hQ : ∀ q ∈ Q, truncatedSixthLowerAlpha/2 ≤ q ∧ q ≤ (1/2-δ)/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      ∀ r : ℝ, r ≤ 1/3 →
      (U N r : ℝ) ≤ packingMass Q N δ η Δ
        (packingStart N δ Δ) (packingSize N δ Δ) +
        highDensityMass N δ ρ r + ε*truncatedSixthMassScale N := by
  obtain ⟨TL,hTL4,hL⟩ := low_packing_upper hδ hδhi hη Q hanchor hQ
  obtain ⟨TH,_,hH⟩ := actual_low_high_upper hδ hδhi hρ hε
  refine ⟨max TL TH,hTL4.trans (le_max_left _ _),?_⟩
  intro N hN he Δ hΔlo hΔhi r hr
  have hl := hL N ((le_max_left _ _).trans hN) he Δ hΔlo hΔhi r
  have hh := hH N ((le_max_right _ _).trans hN) he r hr
  linarith

end Wu2008DoubleSieve.SingleUpperHPacking
