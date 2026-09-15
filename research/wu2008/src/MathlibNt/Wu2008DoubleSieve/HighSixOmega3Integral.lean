import MathlibNt.Wu2008DoubleSieve.HighSixOmega3Payment

namespace Wu2008DoubleSieve.HighSix.Omega3Upper
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The fixed compact phi interval and a uniform growing R precede all labels. -/
theorem ordered_quadrature {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ p ∈ P N,
      |primeOrderedTripleSum (R N δ p) (1/S) (1/s)
        (primeOrderedBuchstabWeight (omega3XPhi N p δ)) -
        omega3XIntegral s S (omega3XPhi N p δ)| < ε := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp
    (primeOrdered_buchstab_uniform 6 ε (by norm_num) hε)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show (0 : ℝ) < 1/6 by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN p hp
  have hN2 : 2 ≤ N := by omega
  have hg := support_geometry hN2 hδ hδhi hp
  have hφ := phi_bounds hN2 hδ hδhi hp
  exact hR0 _ ((hT N (by omega)).trans hg.2.2.2.2.2) _ _ _ hφ.1.le hφ.2
    (by norm_num [S]) (by norm_num [s,S]) (by norm_num [s])

/-- Exact logarithmic rewriting followed by ordered, not product-image, enlargement. -/
theorem buchstab_le_ordered {N d : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hd : d ∈ P N) :
    (∑ p ∈ omega3XPrimes N δ s S d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      x*buchstab (log x/log p.2.1)/log p.2.1) ≤
        (N : ℝ)/((d : ℝ)*log (R N δ d))*
          primeOrderedTripleSum (R N δ d) (1/S) (1/s)
            (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
  have hR : 1 < R N δ d := (ratio_bounds hN hδ hδhi hd).1
  have hd0 : 0 < d := (mem_primeWindow.mp hd).1.pos
  have hφ : 2 ≤ omega3XPhi N d δ := (phi_bounds hN hδ hδhi hd).1.le
  have hA : 1/10 ≤ 1/S := by norm_num [S]
  have hB : 1/s ≤ 1/2 := by norm_num [s]
  let f := fun p1 p2 p3 : ℕ => (N : ℝ)/((d : ℝ)*log (R N δ d))*
    (primeOrderedBuchstabWeight (omega3XPhi N d δ)
      (log p1/log (R N δ d)) (log p2/log (R N δ d)) (log p3/log (R N δ d))/
      ((p1 : ℝ)*p2*p3))
  have hf : ∀ p1 ∈ primesIcc (wuLocalCutoff N δ d S) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
      ∀ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), 0 ≤ f p1 p2 p3 := by
    intro p1 hp1 p2 hp2 p3 hp3
    have hR0 : 0 ≤ R N δ d := by linarith
    have h1 := (mem_primesIcc (rpow_nonneg hR0 (1/s))).mp hp1
    have h2 := (mem_primesIoc (rpow_nonneg hR0 (1/s))).mp hp2
    have h3 := (mem_primesIoc (rpow_nonneg hR0 (1/s))).mp hp3
    have hm1 := omega3XPrime_coordinate_mem hR hp1
    have hm2 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1/s))).mpr ⟨h2.1,h1.2.1.trans h2.2.1.le,h2.2.2⟩)
    have hm3 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1/s))).mpr
      ⟨h3.1,(h1.2.1.trans h2.2.1.le).trans h3.2.1.le,h3.2.2⟩)
    have hw := buchstab_pos (omega3X_argument_bounds hφ
      ⟨hA.trans hm1.1,hm1.2.trans hB⟩ ⟨hA.trans hm2.1,hm2.2.trans hB⟩
      ⟨hA.trans hm3.1,hm3.2.trans hB⟩).2.2
    have hlR := log_pos hR
    have hl2 : 0 < log (p2 : ℝ) := log_pos (by exact_mod_cast h2.1.one_lt)
    dsimp [f,primeOrderedBuchstabWeight]
    positivity
  calc
    _ = ∑ p ∈ omega3XPrimes N δ s S d, f p.1 p.2.1 p.2.2 := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨h2,h1,_,h3,_,_⟩ := mem_omega3XPrimes.mp hp
      exact omega3XPrime_buchstab_term_eq (by omega) hd0
        (mem_primeWindow.mp h1).1 (mem_primeWindow.mp h2).1 h3 hR
    _ ≤ _ := (omega3XPrime_sum_le_nested f hf).trans_eq (by
      simp only [primeOrderedTripleSum,f,mul_sum,wuLocalCutoff,R])

/-- The actual finite Buchstab sum is consumed, not supplied as an upper hypothesis. -/
theorem buchstab_integral_paid {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3XBuchstabMain N δ s S (W N) ≤ omega3XIntegralMain N δ s S (W N) +
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass (W N) := by
  obtain ⟨T,hT4,hT⟩ := ordered_quadrature hδ hδhi (show 0 < ε/6 by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by positivity
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN2)
  unfold omega3XBuchstabMain omega3XIntegralMain boxConvolutionReciprocalMass
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hdP : d ∈ P N := (support N) ▸ hd
  rw [coeff hdP]
  simp only [Nat.cast_one,one_mul]
  have hg := support_geometry hN2 hδ hδhi hdP
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hg.1
  have hlR := log_pos hg.2.2.2.1
  have hlo := log_le_log (rpow_pos_of_pos hN0 _) hg.2.2.2.2.2
  rw [log_rpow hN0] at hlo
  have he := le_of_lt ((abs_lt.mp (hT N hN d hdP)).2)
  have hmul := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (N : ℝ)/((d : ℝ)*log (R N δ d)) by positivity)
  have hfee : (N : ℝ)/((d : ℝ)*log (R N δ d))*(ε/6) ≤
      ε*((N : ℝ)/log N)/d := by
    calc
      _ ≤ (N : ℝ)/((d : ℝ)*((1/6)*log N))*(ε/6) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
          (mul_le_mul_of_nonneg_left hlo hd0.le)
      _ = _ := by ring
  have hb := buchstab_le_ordered hN2 hδ hδhi hdP
  change _ ≤ (N : ℝ)*(1/((d : ℝ)*log (R N δ d))*
    omega3XIntegral s S (omega3XPhi N d δ)) + ε*((N : ℝ)/log N)*(1/d)
  ring_nf at hb hmul hfee ⊢
  linarith

/-- The genuine high-prime integral with its exact quotient logarithm. -/
theorem integral_main_envelope {N : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    omega3XIntegralMain N δ s S (W N) ≤ (N : ℝ)*omega3XIntegralEnvelope s S *
      ∑ d ∈ boxConvolutionSupport (W N),
        (convolutionCoeff (W N) d : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)) := by
  unfold omega3XIntegralMain
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hdP : d ∈ P N := (support N) ▸ hd
  have hl := log_pos (ratio_bounds hN hδ hδhi hdP).1
  have he := (integral_le_envelope hN hδ hδhi hdP).2
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left he
    (show 0 ≤ (convolutionCoeff (W N) d : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)) by
      change 0 ≤ (convolutionCoeff (W N) d : ℝ)/((d : ℝ)*log (R N δ d))
      positivity)

/-- Full singular series, totient and true-li normalization. No fixed-delta
factor is discarded and no maximizing phi is selected. -/
theorem integral_scaled {δ K τ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
    (hK : 0 ≤ K) (hτ : 0 < τ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      omega3XIntegralMain N δ s S (W N)*(K*wuSingularSeries N/log N) ≤
        ((1+τ)*K/4*omega3XIntegralEnvelope s S)*B6 N δ := by
  obtain ⟨T,hT4,hT⟩ := omega3X_trueLi_sharp_lower hτ
  refine ⟨T,hT4,?_⟩
  intro N hN
  let E := omega3XIntegralEnvelope s S
  let A := ∑ d ∈ boxConvolutionSupport (W N),
    (convolutionCoeff (W N) d : ℝ)/((d : ℝ)*log (R N δ d))
  let U := ∑ d ∈ boxConvolutionSupport (W N),
    (convolutionCoeff (W N) d : ℝ)*wuSingularSeries (d*N)/
      ((Nat.totient d : ℝ)*log (R N δ d))
  have hN4 : 4 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hC0 := wuSingularSeries_pos N hN0
  have hlog := log_pos (show (1 : ℝ) < N by exact_mod_cast hN2)
  have hE : 0 ≤ E := (omega3XIntegralEnvelope_bounds (by norm_num [s])
    (by norm_num [s,S]) (by norm_num [S])).1
  have hA : 0 ≤ A := sum_nonneg fun d hd => by
    have hl := log_pos (ratio_bounds hN2 hδ hδhi ((support N) ▸ hd)).1
    positivity
  have hS : wuSingularSeries N*A ≤ U := by
    dsimp [A,U]
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hd0 := support_pos hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have htpos : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd0
    have htot : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
    have hl := log_pos (ratio_bounds hN2 hδ hδhi ((support N) ▸ hd)).1
    have hC := wuSingularSeries_le_mul hN0 hd0
    have hCd := hC0.trans_le hC
    calc
      _ = (convolutionCoeff (W N) d : ℝ)*wuSingularSeries N/((d : ℝ)*log (R N δ d)) := by ring
      _ ≤ _ := by gcongr
  have hU : 0 ≤ U := (mul_nonneg hC0.le hA).trans hS
  have he := integral_main_envelope hN2 hδ hδhi
  change omega3XIntegralMain N δ s S (W N) ≤ (N : ℝ)*E*A at he
  calc
    _ ≤ ((N : ℝ)*E*A)*(K*wuSingularSeries N/log N) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (E*K)*((N : ℝ)/log N)*(wuSingularSeries N*A) := by ring
    _ ≤ (E*K)*((N : ℝ)/log N)*U := mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (E*K)*((1+τ)*logarithmicIntegral N)*U := by
      gcongr
      exact hT N hN
    _ = _ := by
      change (E*K)*((1+τ)*logarithmicIntegral N)*U =
        ((1+τ)*K/4*E)*(4*logarithmicIntegral N*U)
      ring

end Wu2008DoubleSieve.HighSix.Omega3Upper
