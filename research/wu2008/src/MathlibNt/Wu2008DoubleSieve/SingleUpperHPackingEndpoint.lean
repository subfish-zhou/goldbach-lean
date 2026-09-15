import MathlibNt.Wu2008DoubleSieve.SingleUpperHFineCoarse

namespace Wu2008DoubleSieve.SingleUpperHPackingEndpoint
open Finset Set Real MeasureTheory
open SingleUpperHSource SingleUpperHIntegral SingleUpperHPacking SingleUpperHFineCoarse
open SingleUpperHCoarseLimit SingleUpperHCoarseChoice SingleUpperLowQuadrature
open SingleUpperPrimePayment SingleUpperLowPacking
open scoped Classical
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem effective_integral_nonneg {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    0 ≤ ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t := by
  have hab : truncatedSixthLowerAlpha ≤ (1/2-δ)/2 := by
    norm_num [truncatedSixthLowerAlpha] at *; linarith
  apply intervalIntegral.integral_nonneg hab
  intro t ht
  have ht' : t ∈ Icc (truncatedSixthLowerAlpha/2) ((1/2-δ)/2) :=
    ⟨(by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha/2 ≤ truncatedSixthLowerAlpha).trans ht.1,ht.2⟩
  exact div_nonneg (effective_slab_nonneg hδ hδhi ht')
    (mul_nonneg (by norm_num [truncatedSixthLowerAlpha] at *; linarith [ht.1]) (by linarith [ht.2]))

/-- Original p-2 normalization, uniformly before all fine cells. -/
theorem packing_prime_upper {δ η ρ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hη : 0 ≤ η) (hρ : 0 < ρ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Δ a : ℝ, ∀ m : ℕ,
      1 < Δ → truncatedSixthLowerAlpha/2 ≤ a → 1/15 ≤ a →
      truncatedSixthLowerAlpha-coarseMesh δ n ≤ a →
      gamma5GainPoint N Δ a m ≤ (1/2-δ)/2 →
      gamma5GainStep N Δ ≤ coarseMesh δ n →
      SingleUpperHPacking.packingMass (fullGrid δ n) N δ η Δ a m ≤
        (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+ρ)*coarsePrimeMass δ η n N := by
  obtain ⟨T,hT,hpay⟩ := denominator_payment hρ
  refine ⟨T,hT,?_⟩
  intro N hN Δ a m hΔ ha ha15 had hend hstep
  have hN2 : 2 ≤ N := by have := hT.trans hN; omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hm := (gamma5Gain_point_strictMono hNr hΔ a).monotone
  have haj (j : ℕ) : a ≤ gamma5GainPoint N Δ a j := by
    simpa only [gamma5GainPoint,Nat.cast_zero,zero_mul,add_zero] using hm (Nat.zero_le j)
  have hpay' (j : ℕ) (p : ℕ) (hp : p ∈ primeWindow N
      ((N : ℝ)^gamma5GainPoint N Δ a j) ((N : ℝ)^gamma5GainPoint N Δ a (j+1))) :=
    hpay N hN p (mem_primeWindow.mp hp).1
      ((rpow_le_rpow_of_exponent_le hNr.le (ha15.trans (haj j))).trans (mem_primeWindow.mp hp).2.2.1)
  rw [SingleUpperHPacking.packing_exact hN2 hΔ (fun j _ p hp => (hpay' j p hp).1)]
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN2)
  have hnorm : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N := by positivity
  rw [mul_assoc (4*logarithmicIntegral N*wuSingularSeries N/log N) (1+ρ)]
  apply mul_le_mul_of_nonneg_left _ hnorm
  calc
    _ ≤ (1+ρ)*(∑ j ∈ range m, ∑ p ∈ primeWindow N
        ((N : ℝ)^gamma5GainPoint N Δ a j) ((N : ℝ)^gamma5GainPoint N Δ a (j+1)),
        (effective δ (argument δ (sample (fullGrid δ n) (gamma5GainPoint N Δ a j)))+η)*
          (1/((p : ℝ)*((1/2-δ)-log p/log N)))) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have ht := closed_coordinate hN2 (window_subset_closed hp)
      have hjm : j+1 ≤ m := by have := mem_range.mp hj; omega
      have htend := ht.2.trans ((hm hjm).trans hend)
      have hs := sample_mem_le (fullGrid_anchor δ n) (ha.trans (haj j))
      have hcoef := add_nonneg (effective_slab_nonneg hδ hδhi
        (fullGrid_legal hδhi n _ hs.1)) hη
      have hd : 0 ≤ (1/2-δ)-log (p : ℝ)/log N := by linarith
      have h := mul_le_mul_of_nonneg_right (hpay' j p hp).2.1 (div_nonneg hcoef hd)
      convert h using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fine_sum_le hδ hδhi hη hN2 hΔ ha had hend hstep) (by positivity)

/-- Internally selected full coarse family and source slack; the actual packing
has the integral coefficient, not an assumed endpoint upper bound. -/
theorem packing_integral_upper {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∀ Δ : ℝ, 1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
        Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
      SingleUpperHPacking.packingMass (fullGrid δ n) N δ η Δ
        (packingStart N δ Δ) (packingSize N δ Δ) ≤
      (4*(∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t)+ε)*
        truncatedSixthMassScale N := by
  let I := ∫ t in truncatedSixthLowerAlpha..((1/2-δ)/2), effectiveKernel δ t
  have hI : 0 ≤ I := effective_integral_nonneg hδ hδhi
  obtain ⟨ρ,hρ,hbudget⟩ := SingleUpperLowEndpoint.scalar_budget I 1 ε hε
  obtain ⟨n,η,hη,hma,hmb,TC,hTC,hCoarse⟩ := coarse_prime_upper hδ hδhi hρ
  obtain ⟨TP,_,hPrime⟩ := packing_prime_upper (n := n) hδ hδhi hη.le hρ
  obtain ⟨TM,_,hMesh⟩ := mesh_small (mesh_pos hδhi n)
  obtain ⟨TI,_,hLi⟩ := trueLi_upper hρ
  refine ⟨n,η,hη,max TC (max TP (max TM TI)),hTC.trans (le_max_left _ _),?_⟩
  intro N hN Δ hΔlo hΔhi
  have hNC : TC ≤ N := (le_max_left _ _).trans hN
  have htail := (le_max_right TC (max TP (max TM TI))).trans hN
  have hNP : TP ≤ N := (le_max_left _ _).trans htail
  have htail' := (le_max_right TP (max TM TI)).trans htail
  have hNM : TM ≤ N := (le_max_left _ _).trans htail'
  have hNI : TI ≤ N := (le_max_right _ _).trans htail'
  have hN2 : 2 ≤ N := by have := hTC.trans hNC; omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN2
  have hlog := log_pos hNr
  have hΔ : 1 < Δ := by have := rpow_pos_of_pos hlog (-4 : ℝ); linarith
  have hmesh := hMesh N hNM Δ hΔlo hΔhi
  have hstart := packing_start_bounds hN2 hδhi hΔ
  have had : truncatedSixthLowerAlpha-coarseMesh δ n ≤ packingStart N δ Δ := by linarith [hstart.1]
  have ha : truncatedSixthLowerAlpha/2 ≤ packingStart N δ Δ := by linarith
  have ha15 : 1/15 ≤ packingStart N δ Δ := by linarith
  have hp := hPrime N hNP Δ (packingStart N δ Δ) (packingSize N δ Δ)
    hΔ ha ha15 had (by rw [packing_endpoint]) hmesh
  have hC : 0 ≤ wuSingularSeries N := (wuSingularSeries_pos N (by omega)).le
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by exact_mod_cast hN2)
  have hnorm0 : 0 ≤ 4*logarithmicIntegral N*wuSingularSeries N/log N := by positivity
  have hscale : 0 ≤ truncatedSixthMassScale N := by unfold truncatedSixthMassScale; positivity
  have hnorm : 4*logarithmicIntegral N*wuSingularSeries N/log N ≤
      4*(1+ρ)*truncatedSixthMassScale N := by
    calc
      _ = logarithmicIntegral N*(4*wuSingularSeries N/log N) := by ring
      _ ≤ ((1+ρ)*(N : ℝ)/log N)*(4*wuSingularSeries N/log N) :=
        mul_le_mul_of_nonneg_right (hLi N hNI) (by positivity)
      _ = _ := by unfold truncatedSixthMassScale; ring
  calc
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+ρ)*coarsePrimeMass δ η n N := hp
    _ ≤ (4*logarithmicIntegral N*wuSingularSeries N/log N)*(1+ρ)*(I+ρ) :=
      mul_le_mul_of_nonneg_left (hCoarse N hNC) (by positivity)
    _ ≤ (4*(1+ρ)*truncatedSixthMassScale N)*(1+ρ)*(I+ρ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm (by positivity)) (by positivity)
    _ = (4*(1+ρ)^2*(I+1*ρ))*truncatedSixthMassScale N := by ring
    _ ≤ (4*I+ε)*truncatedSixthMassScale N := mul_le_mul_of_nonneg_right hbudget hscale

end Wu2008DoubleSieve.SingleUpperHPackingEndpoint
