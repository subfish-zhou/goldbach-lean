import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeRoughMassScalar
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteErrorPayment

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real LiLiuPrereqBuchstab
open scoped Classical

def tupleCoordinates (t : PrimeTuple) : Fin 4 → ℕ :=
  fun j => (tupleList t).getD j 0

theorem tupleCoordinates_injective {t u : PrimeTuple}
    (h : tupleCoordinates t = tupleCoordinates u) : t = u := by
  have hl := HighNonunit.list_eq_of_getD (tupleList_length t) (tupleList_length u) h
  simpa only [tupleList, List.cons.injEq, and_true, true_and, Prod.ext_iff, and_assoc,
    and_left_comm, and_comm] using hl

theorem tupleCoordinates_ofFn (t : PrimeTuple) :
    List.ofFn (tupleCoordinates t) = tupleList t := by
  change List.ofFn (fun j : Fin (tupleList t).length => (tupleList t).getD j 0) = _
  simp only [List.getD_eq_getElem _ _ (Fin.isLt _)]
  exact List.ofFn_getElem

theorem tupleCoordinates_product (t : PrimeTuple) :
    (∏ j, (tupleCoordinates t j : ℝ)) = ((tupleList t).prod : ℝ) := by
  rw [← tupleCoordinates_ofFn t, Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn]
  rfl

theorem actual_tuple_cube {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 4} {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p j d) :
    ∀ r ∈ tupleList t, r ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d) := by
  let R := (N:ℝ)^(1/2-δ)/d
  have hR := (omega3XPhi_source_bounds hN hδ hδhi hb hd).2.1
  have hS : 0 < p.S := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (hp.one_le_s.trans (hp.s_le_kappa3.trans (hp.kappa3_lt_kappa2.le.trans
      (hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S))))
  have hlo : R^(1/10:ℝ) ≤ wuLocalCutoff N δ d p.S :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le hS hp.S_le_ten)
  have hhi : wuLocalCutoff N δ d p.s ≤ R^(1/2:ℝ) :=
    rpow_le_rpow_of_exponent_le hR.le (one_div_le_one_div_of_le (by norm_num) hs)
  obtain ⟨h3,h2,h1,_,_,hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  have hupper : lastUpper (fun d => wuLocalCutoff N δ d p.kappa3)
      (fun d => wuLocalCutoff N δ d p.s) (FourPrimeUnit.word j) d ≤ R^(1/2:ℝ) := by
    unfold lastUpper
    split_ifs
    · exact rpow_le_rpow_of_exponent_le hR.le
        (one_div_le_one_div_of_le (by norm_num) (hs.trans hp.s_le_kappa3))
    · exact hhi
  intro r hr
  simp only [tupleList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw _ h1
  · exact hw _ h2
  · exact hw _ h3
  · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hq.1,hlo.trans ((mem_primeWindow.mp h3).2.2.1.trans
        (by exact_mod_cast hq.2.1.le)),hq.2.2.2.trans hupper⟩

/-- Complete ordered labels embed; the residual n is never a coordinate. -/
noncomputable def tupleCubeEmbedding {R : ℝ} (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) :
    S ↪ (Fin 4 → primeSlabPrimes R) where
  toFun t j := ⟨tupleCoordinates t.val j, hmem t.val t.property _ (by
    have hj : j.val < (tupleList t.val).length := by rw [tupleList_length]; exact j.isLt
    simp only [tupleCoordinates, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj)⟩
  inj' := by
    intro t u h
    apply Subtype.ext
    apply tupleCoordinates_injective
    funext j
    exact congrArg Subtype.val (congr_fun h j)

theorem tupleCubeEmbedding_weight {R : ℝ} (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) (t : S) :
    primeSlabWeight R (tupleCubeEmbedding S hmem t) =
      1 / ((tupleList t.val).prod : ℝ) := by
  change (∏ j, 1 / (tupleCoordinates t.val j : ℝ)) = _
  rw [prod_div_distrib, prod_const_one, tupleCoordinates_product t.val]

theorem tuple_reciprocal_le {R : ℝ} (S : Finset PrimeTuple)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (hmass : (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ)) ≤ 5) :
    (∑ t ∈ S, 1/((tupleList t).prod : ℝ)) ≤ 5^4 := by
  let E := tupleCubeEmbedding S hmem
  have hsub := sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image E))
    (fun t _ _ => show 0 ≤ primeSlabWeight R t by unfold primeSlabWeight; positivity)
  have he : (∑ t ∈ univ.image E, primeSlabWeight R t) =
      ∑ t ∈ S, 1/((tupleList t).prod : ℝ) := by
    rw [sum_image (fun a _ b _ h => E.injective h)]
    dsimp only [E]
    simp_rw [tupleCubeEmbedding_weight S hmem]
    exact sum_coe_sort S (fun t : PrimeTuple => 1/((tupleList t).prod : ℝ))
  rw [he] at hsub
  exact hsub.trans (by
    rw [show (∑ t : Fin 4 → primeSlabPrimes R, primeSlabWeight R t) =
      (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ))^4 from by
        simpa only [primeSlabWeight, Fintype.card_fin] using primeSlab_product_mass (α := Fin 4) R]
    exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hmass _)

/-- Pointwise original-weight payment; all m labels carry reciprocal weight. -/
theorem finiteErrorMass_le {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 4)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    finiteErrorMass N δ Δ V p j ≤
      5^4 / (wuLocalExponent k δ / 10) *
        ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ legalPrimeTuples N δ p j d, ((N:ℝ)/tupleProduct d t)/log t.1) ≤
      ((N:ℝ)/d)/(η*log N) * 5^4 := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ p j d)
      (fun t ht => actual_tuple_cube (by omega) hδ hδhi hb p hp hs hd (mem_filter.mp ht).1)
      (hmass d hd)
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ p j d,
          (((N:ℝ)/d)/(η*log N)) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := HighNonunit.mother_window_lower (by omega) hδ hδhi hb p hp hd
          (mem_primeTuples.mp (mem_filter.mp ht).1).1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0:ℝ) < N) η) hp'.2
        rw [log_rpow (by positivity : (0:ℝ) < N)] at hy
        have heq : ((N:ℝ)/tupleProduct d t)/log t.1 =
            ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / log t.1 := by
          simp only [tupleProduct_literal, Nat.cast_mul]
          ring
        rw [heq]
        calc
          _ ≤ ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / (η*log N) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hy
          _ = _ := by ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ t ∈ legalPrimeTuples N δ p j d, 1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^4) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

/-- A common actual slab threshold pays each word and their full sum. -/
theorem finiteErrorMass_four_payment (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 4, finiteErrorMass N δ Δ V p j ≤
        5^4/(wuLocalExponent k δ/10) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 4, finiteErrorMass N δ Δ V p j) ≤
        (4*5^4)/(wuLocalExponent k δ/10) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := HighNonunit.source_cube_mass k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp hs
  have hj := fun j => finiteErrorMass_le (hT.trans hN) hδ hδhi hb p hp hs j
    (hm N hN i Δ V hb)
  refine ⟨hj,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 4))) (fun j _ => hj j)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_div_assoc, mul_assoc] using hh

/-- A single tau and threshold consume both scalar producers. Each endpoint has
one epsilon, not four epsilon; no division by the convolution mass occurs. -/
theorem rough_mass_four_finite_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (∀ j : Fin 4, (roughFamily N δ Δ V p j).mass ≤
        finiteBuchstabMain N δ Δ V p j +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 4, (roughFamily N δ Δ V p j).mass) ≤
        (∑ j : Fin 4, finiteBuchstabMain N δ Δ V p j) +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C : ℝ := (4*5^4)/(wuLocalExponent k δ/10)
  have hC : 0 < C := div_pos (by positivity)
    (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num))
  obtain ⟨T0,hT0,h0⟩ := rough_mass_finite_buchstab k hδ hδhi (div_pos hε hC)
  obtain ⟨T1,_,h1⟩ := rough_mass_four_finite_buchstab k hδ hδhi (div_pos hε hC)
  obtain ⟨T2,_,h2⟩ := finiteErrorMass_four_payment k hδ hδhi
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
  have hsingle : ∀ j : Fin 4, finiteErrorMass N δ Δ V p j ≤ C * X := by
    intro j
    refine (he.1 j).trans ?_
    change (5^4/(wuLocalExponent k δ/10))*((N:ℝ)/log N)*_ ≤ _
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

end Wu2008DoubleSieve.FourPrimeNonunit
