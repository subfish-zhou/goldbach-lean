import MathlibNt.Wu2008DoubleSieve.HighSixPsiIntegral
import MathlibNt.Wu2008DoubleSieve.SingleUpperHighQuadrature

namespace Wu2008DoubleSieve.HighSix
open Finset Real
open scoped Classical

/-- The untouched original upper tail. This is an actual finite count,
not an assumed analytic remainder estimate. -/
noncomputable def U3tailCount (N : ℕ) : ℝ :=
  ∑ p ∈ primeWindow N ((N : ℝ)^right) ((N : ℝ)^(1/3 : ℝ)),
    (sieveCount N p N ((N : ℝ)^alpha) : ℝ)

/-- Identification of the genuine high carrier, including its lower equality atom. -/
theorem highPrimes_window {N : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hδhi : δ ≤ 1/100) (r : ℝ) :
    SingleUpperSplice.highPrimes N δ r =
      primeWindow N ((N : ℝ)^((1/2-δ)/2)) ((N : ℝ)^r) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc : (N : ℝ)^truncatedSixthLowerAlpha ≤ (N : ℝ)^((1/2-δ)/2) :=
    rpow_le_rpow_of_exponent_le hNr (by norm_num [truncatedSixthLowerAlpha]; linarith)
  ext p
  simp only [SingleUpperSplice.highPrimes,mem_filter,mem_primeWindow]
  constructor
  · rintro ⟨⟨hpp,hcop,_ha,hr⟩,hl⟩
    exact ⟨hpp,hcop,hl,hr⟩
  · rintro ⟨hpp,hcop,hl,hr⟩
    exact ⟨⟨hpp,hcop,hc.trans hl,hr⟩,hl⟩

/-- Literal finite three-way reassembly. No upper bound is subtracted. -/
theorem U3_high_split_j6 {N : ℕ} {δ : ℝ} (hN : 2 ≤ N) (hδ : 0 < δ)
    (hδhi : δ ≤ 1/100) :
    SingleUpperHighQuadrature.highCount N δ (1/3) =
      SingleUpperHighQuadrature.highCount N δ left+C6 N+U3tailCount N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcl : (N : ℝ)^((1/2-δ)/2) ≤ (N : ℝ)^left :=
    rpow_le_rpow_of_exponent_le hNr (by norm_num [left]; linarith)
  have hlr : (N : ℝ)^left ≤ (N : ℝ)^right :=
    rpow_le_rpow_of_exponent_le hNr (by norm_num [left,right])
  have hr3 : (N : ℝ)^right ≤ (N : ℝ)^(1/3 : ℝ) :=
    rpow_le_rpow_of_exponent_le hNr (by norm_num [right])
  have h1 := sum_primeWindow_split N hcl (hlr.trans hr3)
    (fun p => sieveCount N p N ((N : ℝ)^alpha))
  have h2 := sum_primeWindow_split N hlr hr3
    (fun p => sieveCount N p N ((N : ℝ)^alpha))
  rw [h2] at h1
  have hR := congrArg (fun x : ℤ => (x : ℝ)) h1
  push_cast at hR
  unfold SingleUpperHighQuadrature.highCount C6 U3tailCount P
  rw [highPrimes_window hN hδhi,highPrimes_window hN hδhi]
  have ha : truncatedSixthLowerAlpha = alpha := by norm_num [truncatedSixthLowerAlpha,alpha]
  rw [ha]
  linarith only [hR]

/-- The new j6 estimate is inserted into the real high U3 count. The
remaining original tail count is explicit: its masked analytic producer
is not inferred by subtracting two existing prefix upper bounds. -/
theorem U3_high_j6_inserted {δ ε : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      SingleUpperHighQuadrature.highCount N δ (1/3) ≤
        (4*(∫ t in ((1/2-δ)/2)..left, SingleUpperQuadrature.weight δ t/t)+
          4*(1-firstFunctionalGainPsi δ s S)*primeIntegral δ+ε)*truncatedSixthMassScale N+
            U3tailCount N := by
  obtain ⟨T1,hT14,hT1⟩ := SingleUpperHighQuadrature.actual_high_classical_upper hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hT2⟩ := C6_psi_integral_upper hδ hδhi (half_pos hε)
  refine ⟨max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he
  have hlow := hT1 N (by omega) he left (by norm_num [left]; linarith) (by norm_num [left])
  have hj6 := hT2 N (by omega) he
  change C6 N ≤ (4*(1-firstFunctionalGainPsi δ s S)*primeIntegral δ)*truncatedSixthMassScale N+
    (ε/2)*truncatedSixthMassScale N at hj6
  rw [U3_high_split_j6 (by omega) hδ hδhi]
  nlinarith only [hlow,hj6]
end Wu2008DoubleSieve.HighSix
