import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighNonunit
open Finset

/-- The original closed small-output sum, with its unchanged convolution coefficient. -/
noncomputable def closedSmall {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) (Z : ℝ) : ℝ :=
  ∑ x ∈ actualProfiles N δ p W high, (convolutionCoeff W x.1 : ℝ) *
    ((actualFibre N δ p x).filter (fun q => ((N-cofactor x*q : ℕ) : ℝ) ≤ Z)).card

/-- Output primality supplies the lower endpoint; all closed upper atoms are retained. -/
theorem small_card_disintegration (N Z : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (x : Profile) :
    (∑ ell ∈ Icc 1 Z, ((actualFibre N δ p x).filter
      (fun q => N-cofactor x*q = ell)).card) =
      ((actualFibre N δ p x).filter (fun q => N-cofactor x*q ≤ Z)).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext q
  simp only [mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · intro h
    have hp : (N-cofactor x*q).Prime := (mem_filter.mp h.1).2.2.2.2.2.2
    exact ⟨h.1,hp.pos,h.2⟩

/-- Exact real/floor disintegration of the actual weighted carrier. -/
theorem closedSmall_disintegration {i : ℕ} (N : ℕ) (δ : ℝ) (p : SecondFunctionalParameters)
    (W : Fin i → Finset ℕ) (high : Bool) {Z : ℝ} (hZ : 0 ≤ Z) :
    closedSmall N δ p W high Z =
      ∑ ell ∈ Icc 1 ⌊Z⌋₊, ∑ x ∈ actualProfiles N δ p W high,
        (convolutionCoeff W x.1 : ℝ) *
          ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card := by
  rw [sum_comm]
  unfold closedSmall
  apply sum_congr rfl
  intro x _
  rw [← mul_sum, ← Nat.cast_sum, small_card_disintegration]
  simp only [Nat.le_floor_iff hZ]

/-- Finite output grouping pays the number of integer outputs once, not per profile. -/
theorem closedSmall_le_of_output_bound {i N : ℕ} {δ C Z : ℝ}
    (p : SecondFunctionalParameters) (W : Fin i → Finset ℕ) (high : Bool)
    (hZ : 0 ≤ Z) (hC : 0 ≤ C)
    (h : ∀ ell, (∑ x ∈ actualProfiles N δ p W high, (convolutionCoeff W x.1 : ℝ) *
      ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card) ≤ C) :
    closedSmall N δ p W high Z ≤ C*Z := by
  rw [closedSmall_disintegration N δ p W high hZ]
  calc
    _ ≤ ∑ _ell ∈ Icc 1 ⌊Z⌋₊, C := sum_le_sum (fun ell _ => h ell)
    _ = C*(⌊Z⌋₊ : ℝ) := by simp [mul_comm]
    _ ≤ C*Z := mul_le_mul_of_nonneg_left (Nat.floor_le hZ) hC

/-- Explicit emptiness beyond N follows from the positive original product. -/
theorem actual_output_fibre_empty {k i N ell : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (p : SecondFunctionalParameters)
    (hp : p.MotherAdmissible) (high : Bool) {x : Profile}
    (hx : x ∈ actualProfiles N δ p (convolutionWuWindows N Δ V) high) (hell : N ≤ ell) :
    (actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hq,he⟩ := mem_filter.mp hq
  have hpr : q.Prime := (mem_filter.mp hq).2.1
  have hg := actual_profile_data hN hδ hδhi hb p hp high hx
  have hpos : 0 < cofactor x*q := Nat.mul_pos hg.2.2.2.2.1 hpr.pos
  omega

/-- Joint actual endpoint: full fixed-e sigma, fixed outputs, closed Small, and both words.
All source-box and mother-window conditions are supplied before the counting theorems.
The common threshold is fixed before N, boxes, parameters, words and real cutoffs. -/
theorem source_all_multiplicities (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let W := convolutionWuWindows N Δ V
      let H := max 1 (1/(wuLocalExponent k δ / 10))
      (∀ high : Bool,
        (∀ e, (∑ x ∈ (actualProfiles N δ p W high).filter (fun x => cofactor x = e),
          (convolutionCoeff W x.1 : ℝ)) ≤ H^(k+arity high)) ∧
        (∀ ell, (∑ x ∈ actualProfiles N δ p W high, (convolutionCoeff W x.1 : ℝ) *
          ((actualFibre N δ p x).filter (fun q => N-cofactor x*q = ell)).card) ≤ H^(k+arity high+1)) ∧
        (∀ Z : ℝ, 0 ≤ Z → Z < N → closedSmall N δ p W high Z ≤ H^(k+arity high+1)*Z)) ∧
      (∀ Z : ℝ, 0 ≤ Z → Z < N →
        closedSmall N δ p W false Z + closedSmall N δ p W true Z ≤ 2*H^(k+6)*Z) := by
  obtain ⟨T,hT,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  let W := convolutionWuWindows N Δ V
  let H := max 1 (1/(wuLocalExponent k δ / 10))
  have hf (high : Bool) := hm N hN i Δ V hb p hp high
  have hsmall (high : Bool) (Z : ℝ) (hZ : 0 ≤ Z) :
      closedSmall N δ p W high Z ≤ H^(k+arity high+1)*Z :=
    closedSmall_le_of_output_bound p W high hZ (by dsimp [H]; positivity) (hf high).2
  refine ⟨fun high => ⟨(hf high).1, (hf high).2, fun Z hZ _ => hsmall high Z hZ⟩, ?_⟩
  intro Z hZ _
  have h0 := hsmall false Z hZ
  have h1 := hsmall true Z hZ
  have hH : 1 ≤ H := le_max_left _ _
  have hpw : H^(k+arity false+1) ≤ H^(k+6) :=
    pow_le_pow_right₀ hH (by simp [arity])
  have he : k+arity true+1 = k+6 := by simp [arity]
  rw [he] at h1
  have hb0 := h0.trans (mul_le_mul_of_nonneg_right hpw hZ)
  change closedSmall N δ p W false Z + closedSmall N δ p W true Z ≤ 2*H^(k+6)*Z
  calc
    _ ≤ H^(k+6)*Z + H^(k+6)*Z := add_le_add hb0 h1
    _ = _ := by ring

end Wu2008DoubleSieve.HighNonunit
