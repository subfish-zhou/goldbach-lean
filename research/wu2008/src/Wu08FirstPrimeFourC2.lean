import Wu08FirstPrimeFourSieve

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour

/-- The exact complement of the original primorial in the full WF interval.
It has a sign, and is not asserted negligible in this module. -/
def exceptional (N : ℕ) (L : Finset Long) (V P : Finset ℕ)
    (Q η z : ℝ) (t : List ℕ) : ℝ :=
  ∑ d ∈ (Icc 1 ⌊Q⌋₊).filter (fun d => ¬ d ∣ P.prod id),
    externalTerm true P (externalInternalLevel Q η) η z t d*
      bilinearDiscrepancy (products L) V (alpha L) (beta N) N d

/-- SAME full coefficient, no squarefree mask, no replacement of N by N/a. -/
theorem primorial_error_eq (N : ℕ) (L : Finset Long) (V P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hPN : ∀ p ∈ P, p.Coprime N)
    {Q η z : ℝ} (hQ : 0 ≤ Q) (hD : 2 ≤ externalInternalLevel Q η)
    (hη : 0 < η) (hηu : η < 1/8) (t : List ℕ)
    (ht : t ∈ externalTags true P (externalInternalLevel Q η) η z) :
    (∑ d ∈ (P.prod id).divisors,
      externalTerm true P (externalInternalLevel Q η) η z t d*
        bilinearDiscrepancy (products L) V (alpha L) (beta N) N d) =
      signedError (products L) V (Ioc 0 ⌊Q⌋₊) (alpha L) (beta N)
        (fun d => externalTerm true P (externalInternalLevel Q η) η z t d) N -
      exceptional N L V P Q η z t := by
  have h := externalTerm_full_sum_split true P hP z hD hη hηu t ht
    (bilinearDiscrepancy (products L) V (alpha L) (beta N) N)
  rw [externalInternalLevel_level hQ hη hηu] at h
  have he := externalTerm_full_eq_signedError true P (externalInternalLevel Q η)
    η z t N hPN (products L) V (alpha L) (beta N) Q
  change _ = _+exceptional N L V P Q η z t at h
  rw [he] at h
  linarith

/-- Actual finite F10/F11 box upper using Wu04 Lemma 2.6's improved level.
C2 is paid by the existing theorem at order eight; the centre, non-primorial
complement and low outputs remain literal. This is NOT the final integral upper. -/
theorem physical_box_C2_upper (A : ℕ) {Cscale ε : ℝ}
    (hCscale : 1 ≤ Cscale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ J : PrimeC2Interval, ∀ M ν : ℝ,
      1 ≤ M → 4*M*J.scale=x → ε ≤ ν → ν ≤ 1/10+ε/10 → J.scale=x^ν →
      ∀ N : ℕ, 0 < N → (N : ℝ) ≤ Cscale*x → ∀ e : Bool, ∀ L : Finset Long,
      L ⊆ longLabels N e →
      (∀ t ∈ L, M ≤ (longProduct t : ℝ) ∧ (longProduct t : ℝ) ≤ 2*M) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ η z : ℝ, 0 < η → η < 1/8 → (∀ p ∈ P, (p : ℝ) < z) →
      2 ≤ externalInternalLevel (x^((5-5*ν)/9-ε)) η →
      let V := primeSWInterval J.lower J.upper
      let Q := x^((5-5*ν)/9-ε)
      let D := externalInternalLevel Q η
      let S := externalTags true P D η z
      ((box N e L V).card : ℝ) ≤
        (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d*g9IntegerFibreCenter (products L) V (alpha L) (beta N) d) +
        (S.card : ℝ)*(x/log x^A) -
        (∑ t ∈ S, exceptional N L V P Q η z t) + lowRectangle N L V z := by
  filter_upwards [rectangle_C2 1 A hCscale hε, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  intro J M ν hM hMT hεν hν hT N hN hNx e L hL hscale P hP hPN η z hη hηu hcut hD
  dsimp only
  let Q := x^((5-5*ν)/9-ε)
  let D := externalInternalLevel Q η
  let V := primeSWInterval J.lower J.upper
  let S := externalTags true P D η z
  have hQ : 0 ≤ Q := Real.rpow_nonneg (by linarith) _
  have hu := box_weighted_upper N e L V P hP hD hη hηu hcut
  have herror : (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
      externalTerm true P D η z t d*bilinearDiscrepancy (products L) V (alpha L) (beta N) N d) ≤
      (S.card : ℝ)*(x/log x^A) - ∑ t ∈ S, exceptional N L V P Q η z t := by
    calc
      _ = ∑ t ∈ S,
          (signedError (products L) V (Ioc 0 ⌊Q⌋₊) (alpha L) (beta N)
            (fun d => externalTerm true P D η z t d) N - exceptional N L V P Q η z t) := by
        apply sum_congr rfl
        intro t ht
        exact primorial_error_eq N L V P hP hPN hQ hD hη hηu t ht
      _ ≤ ∑ t ∈ S, (x/log x^A - exceptional N L V P Q η z t) := by
        apply sum_le_sum
        intro t ht
        apply sub_le_sub_right
        exact (le_abs_self _).trans (hx J M ν hM hMT hεν hν hT N hN hNx L
          (fun t ht => longLabels_positive (hL ht)) hscale _
          (externalTerm_signedWellFactorable true P z t hQ hD hη hηu ht))
      _ = _ := by rw [sum_sub_distrib]; simp only [sum_const,nsmul_eq_mul]
  change ((box N e L V).card : ℝ) ≤ _
  linarith only [hu,herror]

#print axioms primorial_error_eq
#print axioms physical_box_C2_upper
end Wu08FirstPrimeFour
