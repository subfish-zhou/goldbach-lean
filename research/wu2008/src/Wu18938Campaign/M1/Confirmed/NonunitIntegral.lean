import Wu18938Campaign.M1.Confirmed.UnitIntegral
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitFiniteToClosedK
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighKernelPayloads

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve HighNonunit HighNonunitLegal Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem roughBox_finite_inner_closed {m i N d : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (high : Bool) (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    (∑ t ∈ legalPrimeTuples N δ p high d,
      buchstab (log ((N : ℝ) / tupleProduct d t) / log t.2.1) *
        ((N : ℝ) / tupleProduct d t) / log t.2.1) ≤
      ((N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d)) * sourceClosedK N d δ p high := by
  have hd0 := hb.support_pos hd
  have hR := (hb.support_geometry (by omega) hη hδ hd).2.2.1
  let S := legalPrimeTuples N δ p high d
  have hlen : ∀ t ∈ S, (tupleList t).length = if high then 6 else 5 :=
    fun t ht => high_tuple_length high (mem_filter.mp ht).1
  have hmem : ∀ t ∈ S, ∀ r ∈ tupleList t,
      r ∈ primeSlabPrimes ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    fun t ht => roughBox_tuple_cube hb (by omega) hη hδ p hp hs hd (mem_filter.mp ht).1
  have hprod (t : S) : 0 < (tupleList t.val).prod := by
    have hh := tupleProduct_pos hd0 (mem_filter.mp t.property).1
    by_contra hz
    have he := Nat.eq_zero_of_not_pos hz
    simp only [tupleProduct, he, mul_zero, lt_self_iff_false] at hh
  have hprime (t : S) : 1 < t.val.2.1 :=
    (mem_primeWindow.mp (mem_primeTuples.mp (mem_filter.mp t.property).1).2.1).1.one_lt
  have hgate (t : S) : tupleProduct d t.val * t.val.2.1 ≤ N := (mem_filter.mp t.property).2
  have hscale : 0 ≤ (N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    div_nonneg (div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg d)) (log_pos hR).le
  cases high with
  | false =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 3) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK20 _ _ _ _ _
    rw [finiteTransport_closed20]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 3
    · intro t
      exact tuple_embedding_D20 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2
  | true =>
    have hk (t : S) := tupleCubeEmbedding_legal_kernel (m := 4) (by omega) hd0 hR
      S hlen hmem t (hprod t) (hprime t) (hgate t)
    change _ ≤ _ * closedPrimeK21 _ _ _ _
    rw [finiteTransport_closed21]
    apply tuple_sum_le_closed_mask hR hscale S (tupleCubeEmbedding S hlen hmem) 4
    · intro t
      exact tuple_embedding_D21 hR S hlen hmem t (mem_filter.mp t.property).1 (hk t).1
    · intro t
      exact (hk t).2.2

theorem roughBox_buchstab_closed {m i N : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) (hs : 2 ≤ p.s)
    (high : Bool) :
    finiteBuchstabMain N δ Δ V p high ≤ sourceClosedKMass N δ Δ V p high := by
  unfold finiteBuchstabMain sourceClosedKMass
  exact sum_le_sum (fun d hd => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (roughBox_finite_inner_closed hb hN hη hδ p hp hs high hd)
      (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d)))

theorem roughBox_closed_pair_uniform (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      |(sourceClosedK N d δ p false + sourceClosedK N d δ p true) -
        (sourceLegalK N d δ p false + sourceLegalK N d δ p true)| < ε := by
  obtain ⟨R0, _, hR0⟩ := closedPrimeK_pair_uniform (max 2 (1 / η)) (le_max_left _ _) ε he
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop R0))
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN i Δ V hb p hp hs d hd
  have hg := roughBox_log_geometry hb (by omega) hη hδ hd
  have hlarge := (hT N (by omega)).trans (hb.remaining d hd)
  obtain ⟨ha, haa, _, hbs⟩ := HighUnitSource.parameter_log_cap_bounds hp hs
  simpa only [sourceClosedK, sourceLegalK, Bool.false_eq_true, ↓reduceIte] using
    hR0 _ hlarge _ ⟨by linarith [hg.2.2.1], hg.2.2.2.trans (le_max_right _ _)⟩
      _ _ _ ha haa hbs

theorem roughBox_payload_error {m i N : ℕ} {η δ Δ ε : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (he : 0 ≤ ε) (f g : ℕ → ℝ)
    (herr : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      |f d - g d| ≤ ε * η) :
    |HighSourcePayload.mass N δ Δ V f - HighSourcePayload.mass N δ Δ V g| ≤
      ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  unfold HighSourcePayload.mass
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        |(convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d)) * f d -
          (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d)) * g d| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        ε * ((N : ℝ) / log N) * ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) / d) := by
      apply sum_le_sum
      intro d hd
      have hl := (roughBox_log_geometry hb hN hη hδ hd).1
      have hc : 0 ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
          ((N : ℝ) / d / log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by positivity
      rw [← mul_sub, abs_mul, abs_of_nonneg hc]
      apply (mul_le_mul_of_nonneg_left (herr d hd) hc).trans
      have hs := mul_le_mul_of_nonneg_left (roughBox_log_scale hb hN hη hδ hd he)
        (Nat.cast_nonneg (convolutionCoeff (convolutionWuWindows N Δ V) d))
      convert hs using 1 <;> ring
    _ = _ := by rw [← mul_sum]; rfl

theorem roughBox_nonunit_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      finiteBuchstabMain N δ Δ V p false + finiteBuchstabMain N δ Δ V p true ≤
        HighSourcePayload.mass N δ Δ V
          (fun d => sourceLegalK N d δ p false + sourceLegalK N d δ p true) +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT4, ht⟩ := roughBox_closed_pair_uniform m hη hδ (mul_pos he hη)
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb p hp hs
  have hm := add_le_add (roughBox_buchstab_closed hb (by omega) hη hδ p hp hs false)
    (roughBox_buchstab_closed hb (by omega) hη hδ p hp hs true)
  have herr := (abs_le.mp (roughBox_payload_error hb (by omega) hη hδ he.le
    (fun d => sourceClosedK N d δ p false + sourceClosedK N d δ p true)
    (fun d => sourceLegalK N d δ p false + sourceLegalK N d δ p true)
    (fun d hd => (ht N hN i Δ V hb p hp hs d hd).le))).2
  have heq : sourceClosedKMass N δ Δ V p false + sourceClosedKMass N δ Δ V p true =
      HighSourcePayload.mass N δ Δ V
        (fun d => sourceClosedK N d δ p false + sourceClosedK N d δ p true) := by
    simp only [sourceClosedKMass, HighSourcePayload.mass, mul_add, sum_add_distrib]
  rw [heq] at hm
  linarith only [hm, herr]

end Wu18938Campaign.M1.Confirmed
