import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleUnitPrimePayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleRoughMassScalar

namespace Wu2008DoubleSieve.LowerTripleGroupedBoundary
open Finset Real LiLiuPrereqBuchstab LowerTripleGroupedFinite LowerTripleGroupedUnit
open scoped Classical

noncomputable def badTriples (N : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) (d : ℕ) : Finset PrimeTriple :=
  (legalPrimeTriples N δ P j d).filter fun t =>
    (t.2.2 : ℝ) < (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1

noncomputable def mainWeight (N d : ℕ) (t : PrimeTriple) : ℝ :=
  buchstab (log ((N : ℝ)/tupleProduct d t) / log t.2.1) *
    ((N : ℝ)/tupleProduct d t) / log t.2.1

/-- Only the closed lower r condition is added; every original gate is retained. -/
noncomputable def unshiftedFiniteBuchstabMain {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ (legalPrimeTriples N δ P j d).filter (fun t =>
      (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)), mainWeight N d t

noncomputable def boundaryMass {i : ℕ} (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (P : SecondFunctionalParameters) (j : Fin 6) : ℝ :=
  ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
    (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
    ∑ t ∈ badTriples N δ P j d, mainWeight N d t

/-- In particular the r=rLo atom belongs to the retained summand. -/
theorem main_split {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) :
    finiteBuchstabMain N δ Δ V P j =
      unshiftedFiniteBuchstabMain N δ Δ V P j + boundaryMass N δ Δ V P j := by
  unfold finiteBuchstabMain unshiftedFiniteBuchstabMain boundaryMass badTriples mainWeight
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  rw [← mul_add, sum_filter, sum_filter, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro t _
  by_cases h : (LowerTripleGrouped.actualBands N δ P j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)
  · simp only [h, not_lt_of_ge h, if_true, if_false, add_zero]
  · simp only [h, lt_of_not_ge h, if_true, if_false, zero_add]

theorem nat_open_unit_unique {a : ℝ} {r s : ℕ}
    (hr : a-1 < (r:ℝ)) (hr' : (r:ℝ) < a)
    (hs : a-1 < (s:ℝ)) (hs' : (s:ℝ) < a) : r = s := by
  have h1 : (r:ℝ) < s+1 := by linarith
  have h2 : (s:ℝ) < r+1 := by linarith
  have h1' : r < s+1 := by exact_mod_cast h1
  have h2' : s < r+1 := by exact_mod_cast h2
  omega

def pairProjection (t : PrimeTriple) : Pair := (t.1,t.2.1)

theorem bad_projection_injective {N d : ℕ} {δ : ℝ} {P : SecondFunctionalParameters}
    {j : Fin 6} : Set.InjOn pairProjection (badTriples N δ P j d : Set PrimeTriple) := by
  intro t ht u hu h
  obtain ⟨ht,htr⟩ := mem_filter.mp ht
  obtain ⟨hu,hur⟩ := mem_filter.mp hu
  obtain ⟨_,_,_,_,_,_,htl,_⟩ := mem_primeTriples.mp (mem_filter.mp ht).1
  obtain ⟨_,_,_,_,_,_,hul,_⟩ := mem_primeTriples.mp (mem_filter.mp hu).1
  have hr := nat_open_unit_unique ((le_max_right _ _).trans_lt htl) htr
    ((le_max_right _ _).trans_lt hul) hur
  have hpair : t.1 = u.1 ∧ t.2.1 = u.2.1 := Prod.mk.inj h
  exact Prod.ext hpair.1 (Prod.ext hpair.2 hr)

theorem bad_projection_subset (N d : ℕ) (δ : ℝ) (P : SecondFunctionalParameters)
    (j : Fin 6) : (badTriples N δ P j d).image pairProjection ⊆ actualPairs N δ P j d := by
  intro x hx
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
  obtain ⟨hp,hq,_,hpq,hpre,_,_,_⟩ :=
    mem_primeTriples.mp (mem_filter.mp (mem_filter.mp ht).1).1
  exact mem_pairs.mpr ⟨hp,hq,hpq,hpre⟩

theorem bad_pair_reciprocal_le {N d : ℕ} {δ : ℝ} {P : SecondFunctionalParameters}
    {j : Fin 6} :
    (∑ t ∈ badTriples N δ P j d, 1/((t.1:ℝ)*t.2.1)) ≤
      ∑ x ∈ actualPairs N δ P j d, 1/((x.1:ℝ)*x.2) := by
  have he : (∑ x ∈ (badTriples N δ P j d).image pairProjection,
      1/((x.1:ℝ)*x.2)) = ∑ t ∈ badTriples N δ P j d, 1/((t.1:ℝ)*t.2.1) :=
    sum_image bad_projection_injective
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg (bad_projection_subset N d δ P j)
    (fun _ _ _ => by positivity)

/-- Buchstab is bounded only after the actual D*q gate has supplied u>=1. -/
theorem legal_weight_le {N d : ℕ} {δ : ℝ} {P : SecondFunctionalParameters}
    {j : Fin 6} {t : PrimeTriple} (hd : 0 < d)
    (ht : t ∈ legalPrimeTriples N δ P j d) :
    mainWeight N d t ≤ ((N:ℝ)/tupleProduct d t)/log t.2.1 := by
  obtain ⟨ht,hgate⟩ := mem_filter.mp ht
  have hD : (0:ℝ) < tupleProduct d t := by exact_mod_cast tupleProduct_pos hd ht
  have hq := (mem_primeWindow.mp (mem_primeTriples.mp ht).2.1).1
  have hq1 : (1:ℝ) < t.2.1 := by exact_mod_cast hq.one_lt
  have hlog : 0 < log (t.2.1:ℝ) := log_pos hq1
  have hqX : (t.2.1:ℝ) ≤ (N:ℝ)/tupleProduct d t := by
    apply (le_div_iff₀ hD).mpr
    rw [mul_comm]
    exact_mod_cast hgate
  have hu : 1 ≤ log ((N:ℝ)/tupleProduct d t)/log t.2.1 := by
    apply (le_div_iff₀ hlog).mpr
    simpa only [one_mul] using log_le_log (by positivity : (0:ℝ) < t.2.1) hqX
  unfold mainWeight
  calc
    _ ≤ 1 * ((N:ℝ)/tupleProduct d t)/log t.2.1 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (buchstab_le_one hu)
        (by positivity)) hlog.le
    _ = _ := by rw [one_mul]

/-- One bad atom per labelled pair gains N^(-eta), before sigma summation. -/
theorem bad_weight_le {k i N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hp : P.MotherAdmissible)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {j : Fin 6} {t : PrimeTriple} (ht : t ∈ badTriples N δ P j d) :
    mainWeight N d t ≤
      (((N:ℝ)/d)/((wuLocalExponent k δ/10)*log N)) *
        (N:ℝ)^(-(wuLocalExponent k δ/10)) * (1/((t.1:ℝ)*t.2.1)) := by
  let η := wuLocalExponent k δ/10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNpos : (0:ℝ) < N := by positivity
  have hlegal := (mem_filter.mp ht).1
  have hactual := (mem_filter.mp hlegal).1
  have hdp := boxConvolutionSupport_pos
    (fun _ _ h => (mem_convolutionWuWindows.mp h).1.pos) hd
  have hq := (HighNonunit.mother_window_lower (by omega) hδ hδhi hb P hp hd
    (mem_primeTriples.mp hactual).2.1).2
  have hlog := log_le_log (rpow_pos_of_pos hNpos η) hq
  rw [log_rpow hNpos] at hlog
  have hrq : (t.2.1:ℝ) < t.2.2 :=
    (le_max_left _ _).trans_lt (mem_primeTriples.mp hactual).2.2.2.2.2.2.1
  have hr : 1/(t.2.2:ℝ) ≤ (N:ℝ)^(-η) := by
    rw [rpow_neg hNpos.le, ← one_div]
    exact one_div_le_one_div_of_le (rpow_pos_of_pos hNpos η) (hq.trans hrq.le)
  calc
    _ ≤ ((N:ℝ)/tupleProduct d t)/log t.2.1 := legal_weight_le hdp hlegal
    _ ≤ ((N:ℝ)/tupleProduct d t)/(η*log N) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hlog
    _ = ((((N:ℝ)/d)/(η*log N)) * (1/((t.1:ℝ)*t.2.1))) * (1/(t.2.2:ℝ)) := by
      simp only [tupleProduct, Nat.cast_mul]
      ring
    _ ≤ ((((N:ℝ)/d)/(η*log N)) * (1/((t.1:ℝ)*t.2.1))) * (N:ℝ)^(-η) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

/-- The full original sigma is multiplied once, with no division by its mass. -/
theorem boundaryMass_le {k i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (P : SecondFunctionalParameters)
    (hp : P.MotherAdmissible) (hs : 2 ≤ P.s) (j : Fin 6)
    (hmass : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      (∑ q ∈ primeSlabPrimes ((N:ℝ)^(1/2-δ)/d), 1/(q:ℝ)) ≤ 5) :
    boundaryMass N δ Δ V P j ≤
      (5^2/(wuLocalExponent k δ/10)) * (N:ℝ)^(-(wuLocalExponent k δ/10)) *
        ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ/10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlogN : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hinner (d : ℕ) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
      (∑ t ∈ badTriples N δ P j d, mainWeight N d t) ≤
        (((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η) * 5^2 := by
    have hrec := bad_pair_reciprocal_le (N := N) (d := d) (δ := δ) (P := P) (j := j)
    have hpair := pair_reciprocal_le (actualPairs N δ P j d)
      (actualPairs_subset_slab (by omega) hδ hδhi hb P hp hs hd j) (hmass d hd)
    calc
      _ ≤ ∑ t ∈ badTriples N δ P j d,
          ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η)) * (1/((t.1:ℝ)*t.2.1)) :=
        sum_le_sum (fun t ht => bad_weight_le hN hδ hδhi hb P hp hd ht)
      _ = ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η)) *
          (∑ t ∈ badTriples N δ P j d, 1/((t.1:ℝ)*t.2.1)) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hrec.trans hpair) (by positivity)
  unfold boundaryMass boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ((((N:ℝ)/d)/(η*log N)) * (N:ℝ)^(-η) * 5^2) :=
      mul_le_mul_of_nonneg_left (hinner d hd) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [η]; ring

/-- One threshold, preceding all boxes, parameters and j, supplies the slab mass. -/
theorem boundaryMass_six_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible → 2 ≤ P.s →
      (∀ j : Fin 6, boundaryMass N δ Δ V P j ≤
        (5^2/(wuLocalExponent k δ/10)) * (N:ℝ)^(-(wuLocalExponent k δ/10)) *
          ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, boundaryMass N δ Δ V P j) ≤
        ((6*5^2)/(wuLocalExponent k δ/10)) * (N:ℝ)^(-(wuLocalExponent k δ/10)) *
          ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hm⟩ := HighNonunit.source_cube_mass k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hp hs
  have hj := fun j => boundaryMass_le (hT.trans hN) hδ hδhi hb P hp hs j (hm N hN i Δ V hb)
  refine ⟨hj,?_⟩
  have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => hj j)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_div_assoc, mul_assoc] using hh

/-- Actual shifted-to-unshifted transport. Both endpoints spend one epsilon. -/
theorem finiteMain_six_boundary_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible → 2 ≤ P.s →
      (∀ j : Fin 6, finiteBuchstabMain N δ Δ V P j ≤
        unshiftedFiniteBuchstabMain N δ Δ V P j +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) ∧
      (∑ j : Fin 6, finiteBuchstabMain N δ Δ V P j) ≤
        (∑ j : Fin 6, unshiftedFiniteBuchstabMain N δ Δ V P j) +
          ε * ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ/10
  let C : ℝ := (6*5^2)/η
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hlim : Filter.Tendsto (fun N : ℕ => C*(N:ℝ)^(-η)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hη).comp tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨T0,hT0⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  obtain ⟨T1,hT1,h1⟩ := boundaryMass_six_bound k hδ hδhi
  refine ⟨max T0 T1,hT1.trans (le_max_right _ _),?_⟩
  intro N hN i Δ V hb P hp hs
  have hN1 := (le_max_right T0 T1).trans hN
  have hbnd := h1 N hN1 i Δ V hb P hp hs
  have hc : C*(N:ℝ)^(-η) ≤ ε := (hT0 N ((le_max_left T0 T1).trans hN)).le
  let X := ((N:ℝ)/log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)
  have hX : 0 ≤ X := by
    dsimp only [X, boxConvolutionReciprocalMass]
    have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by have := hT1.trans hN1; omega))
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hlog.le) (sum_nonneg (fun _ _ => by positivity))
  have hsingle (j : Fin 6) : boundaryMass N δ Δ V P j ≤ ε*X := by
    apply (hbnd.1 j).trans
    change (5^2/η)*(N:ℝ)^(-η)*((N:ℝ)/log N)*_ ≤ _
    rw [mul_assoc ((5:ℝ)^2/η*(N:ℝ)^(-η))]
    apply mul_le_mul_of_nonneg_right _ hX
    apply le_trans _ hc
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by norm_num) hη.le) (rpow_nonneg (Nat.cast_nonneg _) _)
  constructor
  · intro j
    rw [main_split]
    exact add_le_add le_rfl (by simpa only [X,mul_assoc] using hsingle j)
  · simp_rw [main_split]
    rw [sum_add_distrib]
    apply add_le_add le_rfl
    apply hbnd.2.trans
    change C*(N:ℝ)^(-η)*((N:ℝ)/log N)*_ ≤ _
    simpa only [X,mul_assoc] using mul_le_mul_of_nonneg_right hc hX

end Wu2008DoubleSieve.LowerTripleGroupedBoundary
