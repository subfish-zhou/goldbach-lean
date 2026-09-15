import Wu18938Campaign.M1.Confirmed.TripleBoundary
import Wu18938Campaign.M1.Confirmed.PayloadNormalization
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFiniteToClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleKThetaNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Triple

open Wu2008DoubleSieve LowerTripleGroupedFinite LowerTripleGroupedBoundary
  LowerTripleSourceK LowerTripleContinuous Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem finite_inner_closed {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (∑ t ∈ (legalPrimeTriples N δ p j d).filter
      (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ)),
      buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) *
        ((N : ℝ) / tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d))) * sourceClosedK N d δ p j := by
  have hd0 := hb.support_pos hd
  have hR := (hb.support_geometry (by omega) hη hδ hd).2.2.1
  have hg := roughBox_log_geometry hb (by omega) hη hδ hd
  have hphi : 2 ≤ omega3XPhi N d δ := by linarith [hg.2.2.1]
  let S := (legalPrimeTriples N δ p j d).filter
    (fun t => (LowerTripleGrouped.actualBands N δ p j d).2.2.2.2.1 ≤ (t.2.2 : ℝ))
  have hactual (t : S) : t.val ∈ actualPrimeTriples N δ p j d :=
    (mem_filter.mp (mem_filter.mp t.property).1).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    fun t ht => tuple_cube hb (by omega) hη hδ p hp hs hd (hactual ⟨t,ht⟩)
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (hactual t)
    rw [tupleProduct_literal] at hh
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    simp only [hz,mul_zero,lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTriples.mp (hactual t)).2.1).1.one_lt
  have hscale : 0 ≤ (N : ℝ) / (d * log ((N : ℝ) ^ (1 / 2 - δ) / d)) :=
    div_nonneg (Nat.cast_nonneg N) (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  unfold sourceClosedK closedPrimeKj
  rw [closedPrimeK_sum]
  apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hmem) 1
  · intro t
    exact tuple_embedding_closed_domain hR S hmem t j (hactual t) (mem_filter.mp t.property).2
  · intro t
    exact tupleCubeEmbedding_kernel (by omega) hd0 hR hphi S hmem t (hprod t) (hprime t)

theorem finite_closed {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s) (j : Fin 6) :
    unshiftedFiniteBuchstabMain N δ Δ V p j ≤ closedKMass N δ Δ V p j := by
  unfold unshiftedFiniteBuchstabMain closedKMass
  exact sum_le_sum (fun d hd => by
    simpa only [mul_assoc,mainWeight] using mul_le_mul_of_nonneg_left
      (finite_inner_closed hb hN hη hδ p hp hs j hd)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d)))

theorem closed_uniform (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), ∀ j : Fin 6,
      |sourceClosedK N d δ p j - sourceIntegralK N d δ p j| < ε := by
  obtain ⟨R0,_,hR0⟩ := closedPrimeK_six_uniform (max 2 (1 / η)) (le_max_left _ _) ε he
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb p hp hs d hd
  have hg := roughBox_log_geometry hb (by omega) hη hδ hd
  have hlarge := (hT N (by omega)).trans (hb.remaining d hd)
  exact hR0 _ hlarge _ ⟨by linarith [hg.2.2.1],hg.2.2.2.trans (le_max_right _ _)⟩
    _ _ _ _ _ (mother_compact_parameters p hp hs)

theorem closed_mass_eq_mass (N : ℕ) (δ Δ : ℝ) {i : ℕ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) :
    closedKMass N δ Δ V p j =
      HighSourcePayload.mass N δ Δ V (fun d => sourceClosedK N d δ p j) := by
  unfold closedKMass HighSourcePayload.mass
  simp only [div_mul_eq_div_div]

theorem mass_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      (LowerTripleGrouped.roughFamily N δ Δ V p j).mass ≤ integralKMass N δ Δ V p j +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  have he3 : 0 < ε / 3 := by positivity
  obtain ⟨T0,hT04,h0⟩ := mass_paid m hη hδ he3
  obtain ⟨T1,_,h1⟩ := boundary_paid m hη hδ he3
  obtain ⟨T2,_,h2⟩ := closed_uniform m hη hδ (mul_pos he3 hη)
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp hs j
  have hm := h0 N (by omega) i Δ V hb p hp hs j
  have hbnd := h1 N (by omega) i Δ V hb p hp hs j
  have hc := finite_closed hb (by omega) hη hδ p hp hs j
  have herr := (abs_le.mp (roughBox_payload_error hb (by omega) hη hδ he3.le
    (fun d => sourceClosedK N d δ p j) (fun d => sourceIntegralK N d δ p j)
    (fun d hd => (h2 N (by omega) i Δ V hb p hp hs d hd j).le))).2
  rw [← closed_mass_eq_mass,← integralKMass_eq_mass] at herr
  linarith only [hm,hbnd,hc,herr]

theorem integral_density (m : ℕ) {η δ ρ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hρ : 0 < ρ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass ≤ integralKMass N δ Δ V p j *
        (((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))) *
          wuSingularSeries N / log N) +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let A := (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) * (8 / (1 - 2 * δ))
  have hA : 0 < A := mul_pos (mul_pos (by linarith) (by positivity))
    (div_pos (by norm_num) (by linarith))
  obtain ⟨T0,hT04,h0⟩ := rough_density m hη hδ hδhi hρ (half_pos he)
  obtain ⟨T1,_,h1⟩ := mass_integral m hη hδ (div_pos he hA)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb p hp hs j
  have hC : 0 ≤ wuSingularSeries N / log N := div_nonneg
    (wuSingularSeries_pos N (by omega)).le
    (log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hd := h0 N (by omega) heven i Δ V hb p hp j
  have hr := h1 N (by omega) i Δ V hb p hp hs j
  have ht := mul_le_mul_of_nonneg_left (roughBox_reciprocal_theta hb (by omega) hη hδ) he.le
  have hh := mul_le_mul_of_nonneg_right hr (mul_nonneg hA.le hC)
  simp only [add_mul] at hh
  have hcancel : ((ε / A) * ((N : ℝ) / log N) *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) *
      (A * (wuSingularSeries N / log N)) =
      ε * (wuSingularSeries N / log N * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by field_simp
  rw [hcancel] at hh
  rw [mul_div_assoc] at hd ⊢
  linarith only [hd,hh,ht]

theorem source_theta (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      (LowerTripleGrouped.sourceFamily N δ Δ V p j).primeMass ≤
        (2 / (1 - 2 * δ)) * sourceKTheta N δ Δ V p j +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨ρ,hr,T0,hT04,h0⟩ := roughBox_payload_density_slack m hη hδ hδhi
    (by positivity : (0 : ℝ) ≤ 10 * (4 : ℝ) ^ 3) (half_pos he)
  obtain ⟨T1,_,h1⟩ := integral_density m hη hδ hδhi hr (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb p hp hs j
  have hd := h1 N (by omega) heven i Δ V hb p hp hs j
  have ht := h0 N (by omega) i Δ V hb (fun d => sourceIntegralK N d δ p j)
    (fun d _ => sourceIntegralK_bounds N d δ p hp hs j)
  rw [← integralKMass_eq_mass] at ht
  change _ ≤ (2 / (1 - 2 * δ)) * sourceKTheta N δ Δ V p j + _ at ht
  rw [mul_div_assoc] at hd
  nlinarith only [hd,ht]

theorem gamma_theta (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s → ∀ j : Fin 6,
      secondFunctionalMotherGammaSum p N δ (convolutionWuWindows N Δ V) (10 + j.val) ≤
        (2 / (1 - 2 * δ)) * sourceKTheta N δ Δ V p j +
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT4,ht⟩ := source_theta m hη hδ hδhi he
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hb p hp hs j
  exact (gamma_source hb (by omega) hη hδ heven p hp j).trans
    (ht N hN heven i Δ V hb p hp hs j)

end Wu18938Campaign.M1.Confirmed.Triple
