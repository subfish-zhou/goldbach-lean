import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimeMain
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment

namespace Wu2008DoubleSieve.LowerTripleGroupedUnit
open Finset Real LiLiuPrereqBuchstab LowerTripleGroupedFinite
open scoped Classical

/-- The full two-coordinate carrier embeds without any third-prime witness or legal gate. -/
theorem actualPairs_subset_slab {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (j : Fin 6) :
    actualPairs N δ p j d ⊆
      (primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)).product
        (primeSlabPrimes ((N:ℝ)^(1/2-δ)/d)) := by
  let R := (N:ℝ)^(1/2-δ)/d
  have hR := (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R^(1/10:ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  intro x hx
  obtain ⟨hx1,hx2,_,_⟩ := mem_pairs.mp hx
  exact mem_product.mpr ⟨hw _ hx1,hw _ hx2⟩

/-- Subset of the Cartesian square preserves every pair, including coincident products. -/
theorem pair_reciprocal_le {R : ℝ} (S : Finset Pair)
    (hsub : S ⊆ (primeSlabPrimes R).product (primeSlabPrimes R))
    (hmass : (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ)) ≤ 5) :
    (∑ x ∈ S, 1/((x.1:ℝ)*x.2)) ≤ 5^2 := by
  calc
    _ ≤ ∑ x ∈ (primeSlabPrimes R).product (primeSlabPrimes R),
        1/((x.1:ℝ)*x.2) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ))^2 := by
      rw [Finset.product_eq_sprod, sum_product, pow_two, sum_mul_sum]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      simp only [one_div_mul_one_div]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hmass _

/-- One original sigma, with both reciprocal prime coordinates paid in full. -/
theorem unitPrimeError_le {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    unitPrimeError N (wuLocalExponent k δ/10) δ Δ V p j ≤
      5^2 / (wuLocalExponent k δ / 10) *
        ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ x ∈ actualPairs N δ p j d, ((N:ℝ)/denominator d x)/(η*log N)) ≤
      ((N:ℝ)/d)/(η*log N) * 5^2 := by
    have hrec := pair_reciprocal_le (actualPairs N δ p j d)
      (actualPairs_subset_slab (by omega) hδ hδhi hb p hp hs hd j) (hmass d hd)
    calc
      _ = ∑ x ∈ actualPairs N δ p j d,
          (((N:ℝ)/d)/(η*log N)) * (1/((x.1:ℝ)*x.2)) := by
        apply sum_congr rfl
        intro x hx
        simp only [denominator, Nat.cast_mul]
        ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ x ∈ actualPairs N δ p j d, 1/((x.1:ℝ)*x.2)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold unitPrimeError boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^2) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

/-- The analytic slab producer supplies every d at one common threshold. -/
theorem unitPrimeError_six_payment (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6, unitPrimeError N (wuLocalExponent k δ/10) δ Δ V p j ≤
        5^2/(wuLocalExponent k δ/10) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, unitPrimeError N (wuLocalExponent k δ/10) δ Δ V p j) ≤
        (6*5^2)/(wuLocalExponent k δ/10) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := HighNonunit.source_cube_mass k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp hs
  have hj := fun j => unitPrimeError_le (hT.trans hN) hδ hδhi hb p hp hs j
    (hm N hN i Δ V hb)
  refine ⟨hj,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => hj j)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_div_assoc, mul_assoc] using hh

/-- Fix tau before all boxes and consume both genuine two-endpoint PNT producers.
The unit main is retained, never multiplied by tau or declared small. -/
theorem unitMass_six_prime_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 6, unitMass N δ Δ V p j ≤ unitPrimeMain N δ Δ V p j +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, unitMass N δ Δ V p j) ≤
        (∑ j : Fin 6, unitPrimeMain N δ Δ V p j) +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C : ℝ := (6*5^2)/(wuLocalExponent k δ/10)
  have hC : 0 < C := div_pos (by positivity)
    (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num))
  obtain ⟨T0,hT0,h0⟩ := unitMass_prime_main k hδ hδhi (div_pos hε hC)
  obtain ⟨T1,_,h1⟩ := unitMass_six_prime_main k hδ hδhi (div_pos hε hC)
  obtain ⟨T2,_,h2⟩ := unitPrimeError_six_payment k hδ hδhi
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs
  have hN0 := (le_max_left T0 _).trans hN
  have hN12 := (le_max_right T0 _).trans hN
  have he := h2 N ((le_max_right T1 T2).trans hN12) i Δ V hb p hp hs
  let X := ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)
  have hX : 0 ≤ X := by
    dsimp only [X, boxConvolutionReciprocalMass]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _)
      (log_pos (by exact_mod_cast (show 1 < N by have := hT0.trans hN0; omega))).le)
      (sum_nonneg (fun _ _ => by positivity))
  have hsingle : ∀ j : Fin 6, unitPrimeError N (wuLocalExponent k δ/10) δ Δ V p j ≤ C * X := by
    intro j
    refine (he.1 j).trans ?_
    change (5^2/(wuLocalExponent k δ/10))*((N:ℝ)/log N)*_ ≤ _
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hX
    dsimp only [C]
    exact div_le_div_of_nonneg_right (by norm_num)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)).le
  have cancel : (ε/C) * (C*X) = ε*X := by field_simp
  have pay (E : ℝ) (hE : E ≤ C*X) : (ε/C)*E ≤ ε*X := by
    simpa only [cancel] using mul_le_mul_of_nonneg_left hE (div_pos hε hC).le
  constructor
  · intro j
    apply (h0 N hN0 i Δ V hb p hp j).trans
    apply add_le_add le_rfl
    simpa only [X, mul_assoc] using pay _ (hsingle j)
  · apply (h1 N ((le_max_left T1 T2).trans hN12) i Δ V hb p hp).trans
    apply add_le_add le_rfl
    simpa only [X, mul_assoc] using
      (pay _ (by simpa only [C, X, mul_assoc] using he.2))

end Wu2008DoubleSieve.LowerTripleGroupedUnit
