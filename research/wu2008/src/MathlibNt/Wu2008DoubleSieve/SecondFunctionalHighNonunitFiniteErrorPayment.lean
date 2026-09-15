import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughMassScalar
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalPrimeSlabUnit

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

def tupleCoordinates (m : ℕ) (t : PrimeTuple) : Fin m → ℕ :=
  fun j => (tupleList t).getD j 0

theorem tupleCoordinates_injective {m : ℕ} {t u : PrimeTuple}
    (ht : (tupleList t).length = m) (hu : (tupleList u).length = m)
    (h : tupleCoordinates m t = tupleCoordinates m u) : t = u := by
  have hl := list_eq_of_getD ht hu h
  have hlen : t.1.length = u.1.length := by
    simp only [tupleList, List.length_append, List.length_cons, List.length_nil] at ht hu
    omega
  have hh := List.append_inj hl hlen
  rcases t with ⟨pre,p,q⟩
  rcases u with ⟨pre',p',q'⟩
  simpa only [List.cons.injEq, and_true, Prod.mk.injEq] using hh

theorem tupleCoordinates_ofFn {m : ℕ} {t : PrimeTuple}
    (ht : (tupleList t).length = m) : List.ofFn (tupleCoordinates m t) = tupleList t := by
  subst m
  rw [show tupleCoordinates (tupleList t).length t =
    (fun j : Fin (tupleList t).length => (tupleList t)[j.val]) from by
      funext j
      exact List.getD_eq_getElem _ _ j.isLt]
  exact List.ofFn_getElem

theorem tupleCoordinates_product {m : ℕ} {t : PrimeTuple}
    (ht : (tupleList t).length = m) :
    (∏ j, (tupleCoordinates m t j : ℝ)) = ((tupleList t).prod : ℝ) := by
  rw [← tupleCoordinates_ofFn ht, Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn]
  rfl

theorem actual_tuple_cube {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {high : Bool} {t : PrimeTuple} (ht : t ∈ actualPrimeTuples N δ p high d) :
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
  obtain ⟨hpre,hp',_,_,hq⟩ := mem_primeTuples.mp ht
  have hw (r : ℕ) (hr : r ∈ primeWindow N (wuLocalCutoff N δ d p.S)
      (wuLocalCutoff N δ d p.s)) : r ∈ primeSlabPrimes R := by
    have hh := mem_primeWindow.mp hr
    exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
      ⟨hh.1,hlo.trans hh.2.2.1,hh.2.2.2.le.trans hhi⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact hw r (((secondFunctionalMother_tuple_mem _ _ _).mp hpre).2.2 r hr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hw _ hp'
    · exact (mem_primesIcc (rpow_nonneg (le_of_lt (lt_trans zero_lt_one hR)) _)).mpr
        ⟨hq.1,hlo.trans ((mem_primeWindow.mp hp').2.2.1.trans
          (by exact_mod_cast hq.2.1.le)),hq.2.2.2.trans hhi⟩

/-- Complete ordered labels embed; the residual n is never a coordinate. -/
noncomputable def tupleCubeEmbedding {m : ℕ} {R : ℝ} (S : Finset PrimeTuple)
    (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) :
    S ↪ (Fin m → primeSlabPrimes R) where
  toFun t j := ⟨tupleCoordinates m t.val j, hmem t.val t.property _ (by
    have hj : j.val < (tupleList t.val).length := by rw [hlen _ t.property]; exact j.isLt
    simp only [tupleCoordinates, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj)⟩
  inj' := by
    intro t u h
    apply Subtype.ext
    apply tupleCoordinates_injective (hlen _ t.property) (hlen _ u.property)
    funext j
    exact congrArg Subtype.val (congr_fun h j)

theorem tupleCubeEmbedding_weight {m : ℕ} {R : ℝ} (S : Finset PrimeTuple)
    (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R) (t : S) :
    primeSlabWeight R (tupleCubeEmbedding S hlen hmem t) =
      1 / ((tupleList t.val).prod : ℝ) := by
  change (∏ j, 1 / (tupleCoordinates m t.val j : ℝ)) = _
  rw [prod_div_distrib, prod_const_one, tupleCoordinates_product (hlen _ t.property)]

theorem tuple_reciprocal_le {m : ℕ} {R : ℝ} (S : Finset PrimeTuple)
    (hlen : ∀ t ∈ S, (tupleList t).length = m)
    (hmem : ∀ t ∈ S, ∀ r ∈ tupleList t, r ∈ primeSlabPrimes R)
    (hmass : (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ)) ≤ 5) :
    (∑ t ∈ S, 1/((tupleList t).prod : ℝ)) ≤ 5^m := by
  let E := tupleCubeEmbedding S hlen hmem
  have hsub := sum_le_sum_of_subset_of_nonneg (subset_univ (univ.image E))
    (fun t _ _ => show 0 ≤ primeSlabWeight R t by unfold primeSlabWeight; positivity)
  have he : (∑ t ∈ univ.image E, primeSlabWeight R t) =
      ∑ t ∈ S, 1/((tupleList t).prod : ℝ) := by
    rw [sum_image (fun a _ b _ h => E.injective h)]
    dsimp only [E]
    simp_rw [tupleCubeEmbedding_weight S hlen hmem]
    exact sum_coe_sort S (fun t : PrimeTuple => 1/((tupleList t).prod : ℝ))
  rw [he] at hsub
  exact hsub.trans (by
    rw [show (∑ t : Fin m → primeSlabPrimes R, primeSlabWeight R t) =
      (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ))^m from by
        simpa only [primeSlabWeight, Fintype.card_fin] using primeSlab_product_mass (α := Fin m) R]
    exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hmass _)

theorem source_cube_mass (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5 := by
  have he : ∀ᶠ R : ℝ in atTop, (∑ q ∈ primeSlabPrimes R, 1/(q:ℝ)) ≤ 5 := by
    filter_upwards [eventually_gt_atTop 1,
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).eventually
        (eventually_ge_atTop primeOrderedMertensStart),
      primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
      with R hR hs he
    have hh := primeSlab_interval_mass hR hs
      (by norm_num : (1/10:ℝ) ≤ 1/10) (by norm_num : (1/10:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) ≤ 1/2)
    change (∑ q ∈ primesIcc (R^(1/10:ℝ)) (R^(1/2:ℝ)), 1/(q:ℝ)) ≤ 5
    linarith
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp he
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (wuLocalExponent_pos k hδ hδhi)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb d hd
  exact hR0 _ ((hT N ((le_max_right _ _).trans hN)).trans
    (omega3XPhi_source_bounds (by omega) hδ hδhi hb hd).1)

/-- Pointwise original-weight payment; all m labels carry reciprocal weight. -/
theorem finiteErrorMass_le {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (high : Bool)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    finiteErrorMass N δ Δ V p high ≤
      5^(if high then 6 else 5) / (wuLocalExponent k δ / 10) *
        ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ legalPrimeTuples N δ p high d, ((N:ℝ)/tupleProduct d t)/log t.2.1) ≤
      ((N:ℝ)/d)/(η*log N) * 5^(if high then 6 else 5) := by
    have hrec := tuple_reciprocal_le (legalPrimeTuples N δ p high d)
      (fun t ht => high_tuple_length high (mem_filter.mp ht).1)
      (fun t ht => actual_tuple_cube (by omega) hδ hδhi hb p hp hs hd (mem_filter.mp ht).1)
      (hmass d hd)
    calc
      _ ≤ ∑ t ∈ legalPrimeTuples N δ p high d,
          (((N:ℝ)/d)/(η*log N)) * (1/((tupleList t).prod : ℝ)) := by
        apply sum_le_sum
        intro t ht
        have hp' := mother_window_lower (by omega) hδ hδhi hb p hp hd
          (mem_primeTuples.mp (mem_filter.mp ht).1).2.1
        have hy := log_le_log (rpow_pos_of_pos (by positivity : (0:ℝ) < N) η) hp'.2
        rw [log_rpow (by positivity : (0:ℝ) < N)] at hy
        have heq : ((N:ℝ)/tupleProduct d t)/log t.2.1 =
            ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / log t.2.1 := by
          simp only [tupleProduct, Nat.cast_mul]
          ring
        rw [heq]
        calc
          _ ≤ ((N:ℝ)/d) * (1/((tupleList t).prod : ℝ)) / (η*log N) :=
            div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hy
          _ = _ := by ring
      _ = (((N:ℝ)/d)/(η*log N)) *
          (∑ t ∈ legalPrimeTuples N δ p high d, 1/((tupleList t).prod : ℝ)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by positivity)
  unfold finiteErrorMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
      (((N:ℝ)/d)/(η*log N) * 5^(if high then 6 else 5)) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

/-- One threshold before N, all boxes, parameters, and both complete words. -/
theorem finiteErrorMass_pair_payment (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      finiteErrorMass N δ Δ V p false + finiteErrorMass N δ Δ V p true ≤
        ((5:ℝ)^5+5^6)/(wuLocalExponent k δ/10) * ((N:ℝ)/log N) *
          boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := source_cube_mass k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp hs
  have h0 := finiteErrorMass_le (hT.trans hN) hδ hδhi hb p hp hs false (hm N hN i Δ V hb)
  have h1 := finiteErrorMass_le (hT.trans hN) hδ hδhi hb p hp hs true (hm N hN i Δ V hb)
  simpa only [Bool.false_eq_true, ↓reduceIte, add_div, add_mul] using add_le_add h0 h1

/-- Scalar312 consumed: original rough raw mass, with arbitrary epsilon on N/log N M_W.
No division by M_W, no exceptional-prime payment, and no Theta claim at this layer. -/
theorem rough_mass_pair_finite_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      (roughFamily N δ Δ V p false).mass + (roughFamily N δ Δ V p true).mass ≤
        finiteBuchstabMain N δ Δ V p false + finiteBuchstabMain N δ Δ V p true +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C := ((5:ℝ)^5+5^6)/(wuLocalExponent k δ/10)
  have hC : 0 < C := div_pos (by positivity)
    (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num))
  obtain ⟨T0,hT0,h0⟩ := rough_mass_pair_finite_buchstab k hδ hδhi (div_pos hε hC)
  obtain ⟨T1,_,h1⟩ := finiteErrorMass_pair_payment k hδ hδhi
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs
  have hraw := h0 N ((le_max_left _ _).trans hN) i Δ V hb p hp
  have herr := mul_le_mul_of_nonneg_left
    (h1 N ((le_max_right _ _).trans hN) i Δ V hb p hp hs) (div_pos hε hC).le
  have hcancel : (ε/C) * (C * ((N:ℝ)/log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) =
      ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
    field_simp
  change (ε/C) * _ ≤ (ε/C) * (C * _ * _) at herr
  rw [hcancel] at herr
  exact hraw.trans (add_le_add le_rfl herr)

end Wu2008DoubleSieve.HighNonunit
