import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitR1Payment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitErrorPayment

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Restriction changes labels only, not the physical prime fibre. -/
theorem r1Family_primes {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (high good : Bool) (x : Profile) :
    (r1Family N δ Δ V p high good).primes x =
      (sourceFamily N δ Δ V p high).primes x := by
  cases good <;> rfl

/-- Strict small outputs of either actual family inject into the original closed sum.
Output primality is retained, and no equality of strict and closed thresholds is used. -/
theorem r1Family_small_le_closedSmall {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (high good : Bool) (Z : ℝ) :
    (r1Family N δ Δ V p high good).small Z ≤
      closedSmall N δ p (convolutionWuWindows N Δ V) high Z := by
  let L := r1Family N δ Δ V p high good
  let W := convolutionWuWindows N Δ V
  have hd : ∀ d ∈ boxConvolutionSupport W, 0 < d :=
    fun _ hd => boxConvolutionSupport_pos
      (fun _ _ hq => (mem_convolutionWuWindows.mp hq).1.pos) hd
  have hsub := r1Family_subset (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
  have hdata := r1Family_data (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
  unfold LabelledPhysical.Family.small closedSmall
  calc
    _ ≤ ∑ x ∈ L.labels, (convolutionCoeff W x.1 : ℝ) *
        ((actualFibre N δ p x).filter (fun q => ((N-cofactor x*q : ℕ) : ℝ) ≤ Z)).card := by
      apply sum_le_sum
      intro x hx
      rw [(hdata x).1]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Nat.cast_le.mpr
      apply card_le_card
      intro q hq
      obtain ⟨hq, hp, hz⟩ := mem_filter.mp hq
      have hpr := (actualFamily_fibres p W high hd (mem_filter.mp (hsub hx)).1).2
      apply mem_filter.mpr
      refine ⟨?_, ?_⟩
      · rw [← hpr]
        apply mem_filter.mpr
        constructor
        · exact (r1Family_primes p high good x) ▸ hq
        · simpa only [(hdata x).2] using hp
      · exact le_of_lt (by simpa only [(hdata x).2] using hz)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun x hx => (mem_filter.mp (hsub hx)).1) (fun _ _ _ => by positivity)

/-- Full weighted fixed-cofactor sigma and relative-to-N roughness for the actual
original family and its explicit good restriction, with a common source threshold. -/
theorem source_error_inputs (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let η := wuLocalExponent k δ / 10
      let H := max 1 (1/η)
      (∀ high good : Bool,
        let L := r1Family N δ Δ V p high good
        (∀ x ∈ L.labels, ∀ q, q.Prime → q ∣ L.cofactor x → q.Coprime N →
          (N : ℝ)^η ≤ (q : ℝ)) ∧
        (∀ e, (∑ x ∈ L.labels.filter (fun x => L.cofactor x = e), L.weight x) ≤ H^(k+5))) ∧
      (∀ Z : ℝ, 0 ≤ Z → Z < N →
        closedSmall N δ p (convolutionWuWindows N Δ V) false Z +
        closedSmall N δ p (convolutionWuWindows N Δ V) true Z ≤ 2*H^(k+6)*Z) := by
  obtain ⟨T0,hT0,hm⟩ := source_all_multiplicities k hδ hδhi
  obtain ⟨T1,_,hu⟩ := actual_family_uniform k hδ hδhi
  refine ⟨max T0 T1, hT0.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  have hm' := hm N hN0 i Δ V hb p hp
  have hu' := (hu N hN1 i Δ V hb).2 p hp
  refine ⟨?_, hm'.2⟩
  intro high good
  let L := r1Family N δ Δ V p high good
  have hsub := r1Family_subset (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
  have hdata := r1Family_data (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
  constructor
  · intro x hx q hq hdiv hcop
    rw [(hdata x).2] at hdiv
    exact ((hu' high).2.2 x (hsub hx)).2.2 q hq hdiv hcop
  · intro e
    have hs : L.labels.filter (fun x => L.cofactor x = e) ⊆
        (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter (fun x => cofactor x = e) := by
      intro x hx
      obtain ⟨hx,he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp (hsub hx)).1, (hdata x).2.symm.trans he⟩
    calc
      _ = ∑ x ∈ L.labels.filter (fun x => L.cofactor x = e),
          (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_congr rfl (fun x _ => (hdata x).1)
      _ ≤ ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
          (fun x => cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ (max 1 (1/(wuLocalExponent k δ / 10)))^(k+arity high) := (hm'.1 high).1 e
      _ ≤ _ := pow_le_pow_right₀ (le_max_left 1 _) (by cases high <;> simp [arity])

end Wu2008DoubleSieve.HighNonunit
