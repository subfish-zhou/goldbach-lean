import MathlibNt.Wu2008DoubleSieve.HighSixOmega3XGeometry

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

/-- The reciprocal-prime budget retains every ordered triple. -/
theorem X_scale_mass {N d : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hd : d ∈ P N)
    (hstart : primeErrorStart ≤ (N : ℝ)^(1/25 : ℝ)) :
    (∑ p ∈ omega3XPrimes N δ s S d,
      omega3XScale N d p.1 p.2.1 p.2.2/log p.2.1) ≤
        ((125 : ℝ)^3*25)*((N : ℝ)/d/log N) := by
  have hN0 : (0 : ℝ) < N := by positivity
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hsum := omega3X_prime_triple_reciprocal_le (η := 1/25) hN (by norm_num) hstart
    (omega3XPrimes N δ s S d) (fun p hp => X_prime_interval hN hδ hδhi hd hp)
  calc
    _ ≤ ∑ p ∈ omega3XPrimes N δ s S d,
        ((N : ℝ)/d/((1/25)*log N))*(1/((p.1 : ℝ)*p.2.1*p.2.2)) := by
      apply sum_le_sum
      intro p hp
      have hP := X_prime_interval hN hδ hδhi hd hp
      have hlow := ((mem_primesIcc hN0.le).mp hP.2.1).2.1
      have hlog := log_le_log (rpow_pos_of_pos hN0 _) hlow
      rw [log_rpow hN0] at hlog
      calc
        _ ≤ omega3XScale N d p.1 p.2.1 p.2.2/((1/25)*log N) :=
          div_le_div_of_nonneg_left (by unfold omega3XScale; positivity) (by positivity) hlog
        _ = _ := by unfold omega3XScale; ring
    _ = ((N : ℝ)/d/((1/25)*log N))*
        ∑ p ∈ omega3XPrimes N δ s S d, 1/((p.1 : ℝ)*p.2.1*p.2.2) := (mul_sum ..).symm
    _ ≤ ((N : ℝ)/d/((1/25)*log N))*(5/(1/25))^3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Uniform repeated-p1 payment does not discard that possible exception. -/
theorem X_repeated_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3XRepeatedMajorant N δ s S (W N) ≤
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (omega3_repeated_scalar_budget (show (0 : ℝ) < 1/25 by norm_num) hε)
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hsource : omega3XRepeatedMajorant N δ s S (W N) ≤
      (((N : ℝ)/(N : ℝ)^(1/25 : ℝ))*(1+log N)^3)*boxConvolutionReciprocalMass (W N) := by
    unfold omega3XRepeatedMajorant omega3XScale
    apply omega3_repeated_weighted_floor_le _ _ (rpow_pos_of_pos (by positivity) _)
    · intro d hd
      exact support_pos hd
    · intro d _ a ha
      exact omega3XPrimes_mem_Icc ha
    · intro d hd a ha
      have h1 := (mem_omega3XPrimes.mp ha).2.1
      exact (inner_lower_cutoff hN2 hδ hδhi ((support N) ▸ hd)).trans
        (mem_primeWindow.mp h1).2.2.1
  have hm : 0 ≤ boxConvolutionReciprocalMass (W N) :=
    sum_nonneg fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg d)
  exact hsource.trans (mul_le_mul_of_nonneg_right (hT N (by omega)) hm)

/-- Actual rough counts consume uniform Buchstab convergence with full mass. -/
theorem X_rough_buchstab_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3XRoughMajorant N δ s S (W N) ≤ omega3XBuchstabMain N δ s S (W N)+
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by
  let C : ℝ := 125^3*25
  have hC : 0 < C := by norm_num [C]
  obtain ⟨T1,hT14,hT1⟩ := X_buchstab_uniform hδ hδhi (div_pos hε hC)
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show (0 : ℝ) < 1/25 by norm_num)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop primeErrorStart))
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have herr : omega3XRoughMajorant N δ s S (W N) ≤ omega3XBuchstabMain N δ s S (W N)+
      (ε/C)*(∑ d ∈ boxConvolutionSupport (W N), (convolutionCoeff (W N) d : ℝ)*
        ∑ p ∈ omega3XPrimes N δ s S d, omega3XScale N d p.1 p.2.1 p.2.2/log p.2.1) := by
    unfold omega3XRoughMajorant omega3XBuchstabMain
    simp only [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro p hp
    have h := (hT1 N (by omega) d ((support N) ▸ hd) p hp).2.2
    have he := (le_abs_self ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ)-
      omega3XScale N d p.1 p.2.1 p.2.2*
        buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2)/log p.2.1)/log p.2.1)).trans h
    have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (convolutionCoeff (W N) d) : (0 : ℝ) ≤ _)
    nlinarith only [hm]
  have hmass : (∑ d ∈ boxConvolutionSupport (W N), (convolutionCoeff (W N) d : ℝ)*
      ∑ p ∈ omega3XPrimes N δ s S d, omega3XScale N d p.1 p.2.1 p.2.2/log p.2.1) ≤
      C*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    calc
      _ ≤ (convolutionCoeff (W N) d : ℝ)*(C*((N : ℝ)/d/log N)) :=
        mul_le_mul_of_nonneg_left
          (X_scale_mass hN2 hδ hδhi ((support N) ▸ hd) (hT2 N (by omega))) (Nat.cast_nonneg _)
      _ = _ := by ring
  have he := mul_le_mul_of_nonneg_left hmass (div_pos hε hC).le
  have hcancel : (ε/C)*(C*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N)) =
      ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by field_simp
  rw [hcancel] at he
  exact herr.trans (add_le_add le_rfl he)

/-- The actual X, not an integral proxy, now reaches the original Buchstab integral. -/
theorem actualX_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3SieveX N δ s S (W N) ≤ omega3XIntegralMain N δ s S (W N)+
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by
  obtain ⟨T1,hT14,hT1⟩ := X_repeated_paid hδ hδhi (show 0 < ε/3 by positivity)
  obtain ⟨T2,_,hT2⟩ := X_rough_buchstab_paid hδ hδhi (show 0 < ε/3 by positivity)
  obtain ⟨T3,_,hT3⟩ := buchstab_integral_paid hδ hδhi (show 0 < ε/3 by positivity)
  refine ⟨max T1 (max T2 T3),hT14.trans (le_max_left _ _),?_⟩
  intro N hN
  have hf := omega3SieveX_le_rough_add_repeated N δ s S (W N) (fun _ hd => support_pos hd)
  have h1 := hT1 N (by omega)
  have h2 := hT2 N (by omega)
  have h3 := hT3 N (by omega)
  linarith

end Wu2008DoubleSieve.HighSix.Omega3Upper
