import HighO3Geometry

namespace HighO3
open Finset Real Wu2008DoubleSieve HighBoxRecovery HighTheta Filter LiLiuPrereqBuchstab
open scoped Classical Topology
noncomputable section

/-- Literal strict nested prime carrier, including the closed p3 endpoint. -/
theorem finite_ordered {N d : ℕ} {δ η s t : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let R := (N : ℝ)^(1/2-δ)/d
    (∑ p ∈ omega3XPrimes N δ s t d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      x*buchstab (log x/log p.2.1)/log p.2.1) ≤
    (N : ℝ)/((d : ℝ)*log R)*primeOrderedTripleSum R (1/t) (1/s)
      (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
  let R := (N : ℝ)^(1/2-δ)/d
  have hg := phi_bounds hN hd hδ hδhi hη hsize
  have hR : 1 < R := hg.2.1
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have : 0 < 2*δ/(1/2-δ) := by positivity
    linarith [hg.2.2.1]
  have hA : 1/10 ≤ 1/t := one_div_le_one_div_of_le (by linarith) ht
  have hB : 1/s ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hs
  let f := fun p1 p2 p3 : ℕ =>
    (N : ℝ)/((d : ℝ)*log R)*
      (primeOrderedBuchstabWeight (omega3XPhi N d δ)
        (log p1/log R) (log p2/log R) (log p3/log R)/((p1 : ℝ)*p2*p3))
  have hf : ∀ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
      ∀ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), 0 ≤ f p1 p2 p3 := by
    intro p1 hp1 p2 hp2 p3 hp3
    have hR0 : 0 ≤ R := by linarith
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
      ⟨hA.trans hm1.1,hm1.2.trans hB⟩
      ⟨hA.trans hm2.1,hm2.2.trans hB⟩
      ⟨hA.trans hm3.1,hm3.2.trans hB⟩).2.2
    have hlR := log_pos hR
    have hl2 : 0 < log (p2 : ℝ) := log_pos (by exact_mod_cast h2.1.one_lt)
    dsimp [f,primeOrderedBuchstabWeight]
    positivity
  calc
    _ = ∑ p ∈ omega3XPrimes N δ s t d, f p.1 p.2.1 p.2.2 := by
      apply sum_congr rfl
      intro p hp
      have h := mem_omega3XPrimes.mp hp
      exact omega3XPrime_buchstab_term_eq (by omega) hd
        (mem_primeWindow.mp h.2.1).1 (mem_primeWindow.mp h.1).1 h.2.2.2.1 hR
    _ ≤ _ := (omega3XPrime_sum_le_nested f hf).trans_eq (by
      simp only [primeOrderedTripleSum,mul_sum,f,wuLocalCutoff,R])

/-- The compact quadrature threshold precedes every supported product. -/
theorem ordered_uniform {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ d : ℕ, 0 < d →
      (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      |primeOrderedTripleSum ((N : ℝ)^(1/2-δ)/d) (1/t) (1/s)
        (primeOrderedBuchstabWeight (omega3XPhi N d δ))-
        omega3XIntegral s t (omega3XPhi N d δ)| < ε := by
  let P := max 2 (1/(10*η))
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp
    (primeOrdered_buchstab_uniform P ε (le_max_left _ _) hε)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < 10*η by positivity)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN d hd hsize s t hs hst ht
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hg := phi_bounds (by omega) hd hδ hδhi hη hsize
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have : 0 < 2*δ/(1/2-δ) := by positivity
    linarith [hg.2.2.1]
  exact hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans hg.1) _ _ _ hφ
    (hg.2.2.2.trans (le_max_right _ _))
    (one_div_le_one_div_of_le (by linarith) ht)
    (one_div_le_one_div_of_le (by linarith) hst)
    (one_div_le_one_div_of_le (by norm_num) hs)

/-- Transport of the additive quadrature error uses the genuine quotient log. -/
theorem log_error {N d : ℕ} {δ η ε : ℝ} (hN : 2 ≤ N) (hd : 0 < d)
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η)
    (hsize : (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) (hε : 0 ≤ ε) :
    (N : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d))*(ε*(10*η)) ≤
      ε*((N : ℝ)/log N)/d := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN := log_pos (show (1 : ℝ) < N by exact_mod_cast (show 1 < N by omega))
  have hg := phi_bounds hN hd hδ hδhi hη hsize
  have hl := log_le_log (rpow_pos_of_pos hN0 _) hg.1
  rw [log_rpow hN0] at hl
  calc
    _ = (ε*(10*η)*((N : ℝ)/d))/log ((N : ℝ)^(1/2-δ)/d) := by ring
    _ ≤ (ε*(10*η)*((N : ℝ)/d))/((10*η)*log N) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hl
    _ = _ := by field_simp

/-- Actual finite Buchstab main sum to the original triple integral.
No target mass-to-integral inequality is assumed. -/
theorem buchstab_integral {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hη : 0 < η) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ (i : ℕ) (W : Fin i → Finset ℕ),
      (∀ d ∈ boxConvolutionSupport W, 0 < d ∧ (d : ℝ) ≤ (N : ℝ)^(1/2-δ-10*η)) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3XBuchstabMain N δ s t W ≤ omega3XIntegralMain N δ s t W+
        ε*((N : ℝ)/log N)*boxConvolutionReciprocalMass W := by
  obtain ⟨T,hT4,hT⟩ := ordered_uniform hδ hδhi hη (show 0 < ε*(10*η) by positivity)
  refine ⟨T,hT4,?_⟩
  intro N hN i W hw s t hs hst ht
  have hN2 : 2 ≤ N := by omega
  unfold omega3XBuchstabMain omega3XIntegralMain boxConvolutionReciprocalMass
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  have hg := phi_bounds hN2 (hw d hd).1 hδ hδhi hη (hw d hd).2
  have hlog := log_pos hg.2.1
  have hcoef : 0 ≤ (N : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d)) := by positivity
  have hdisc := le_of_lt ((le_abs_self _).trans_lt
    (hT N hN d (hw d hd).1 (hw d hd).2 s t hs hst ht))
  have hsum := finite_ordered hN2 (hw d hd).1 hδ hδhi hη (hw d hd).2 hs hst ht
  dsimp only at hsum hdisc
  have herr := log_error hN2 (hw d hd).1 hδ hδhi hη (hw d hd).2 hε.le
  have hmul := mul_le_mul_of_nonneg_left hdisc hcoef
  have hpoint :
      (∑ p ∈ omega3XPrimes N δ s t d,
        let x := omega3XScale N d p.1 p.2.1 p.2.2
        x*buchstab (log x/log p.2.1)/log p.2.1) ≤
      (N : ℝ)/((d : ℝ)*log ((N : ℝ)^(1/2-δ)/d))*
        omega3XIntegral s t (omega3XPhi N d δ)+ε*((N : ℝ)/log N)/d := by
    nlinarith only [hsum,hmul,herr]
  have hwgt := mul_le_mul_of_nonneg_left hpoint
    (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _)
  convert hwgt using 1
  ring

end
end HighO3
