import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSquarePayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitExceptionPayment

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- The residual is a divisor of the original full cofactor. -/
theorem residual_dvd_cofactor (x : Profile) : x.2.2.2 ∣ cofactor x := by
  exact (dvd_mul_left x.2.2.2 x.1).trans (dvd_mul_right _ _)

/-- Masked nonrough residuals in the good part force a square in the full cofactor. -/
theorem masked_good_nonrough_square {N : ℕ} {Y : ℝ} {x : Profile}
    (hs : Sifted (x.1*x.2.1.prod*N) x.2.2.2 x.2.2.1)
    (hc : (cofactor x).Coprime N) (hn : ¬ profileRough x)
    (hrel : ∀ r, r.Prime → r ∣ cofactor x → r.Coprime N → Y ≤ (r : ℝ)) :
    LabelledPhysical.Sq (cofactor x) Y := by
  obtain ⟨r, hr, hrn, hsmall⟩ : ∃ r : ℕ, r.Prime ∧ r ∣ x.2.2.2 ∧
      (r : ℝ) < x.2.2.1 := by
    simpa only [profileRough, LiLiuPrereqBuchstab.Rough, not_forall,
      Classical.not_imp, not_le, exists_prop] using hn
  have hre : r ∣ cofactor x := hrn.trans (residual_dvd_cofactor x)
  have hrN : r.Coprime N := hc.of_dvd_left hre
  have hmask : r ∣ x.1*x.2.1.prod*N := by
    by_contra h
    exact hs r hr (hr.coprime_iff_not_dvd.mpr h) hsmall hrn
  have hrpre : r ∣ x.1*x.2.1.prod :=
    (hr.dvd_mul.mp hmask).resolve_right (hr.coprime_iff_not_dvd.mp hrN)
  refine ⟨r, hr, hrel r hr hre hrN, ?_⟩
  have hd := (Nat.mul_dvd_mul hrpre hrn).trans
    (dvd_mul_right (x.1*x.2.1.prod*x.2.2.2) x.2.2.1)
  simpa only [pow_two, cofactor, List.prod_append, List.prod_singleton,
    mul_assoc, mul_left_comm, mul_comm] using hd

end Wu2008DoubleSieve.HighNonunit

namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset
open scoped Classical

/-- Prime-layer purification only: a raw square majorant and a prime bad-N term. -/
theorem primeMass_le_restrict_add_square_add_bad {α : Type*} {N : ℕ}
    (L : Family α N) (P : α → Prop) (Y : ℝ)
    (hs : ∀ x ∈ L.labels, (L.cofactor x).Coprime N → ¬ P x → Sq (L.cofactor x) Y) :
    L.primeMass ≤ (L.restrictLabels P).primeMass + L.squareRawMass Y +
      L.noncoprimePart.primeMass := by
  let f := fun x => L.weight x *
    (((L.primes x).filter (fun q => (N-L.cofactor x*q).Prime)).card : ℝ)
  let g := fun x => L.weight x * ((L.primes x).card : ℝ)
  change (∑ x ∈ L.labels, f x) ≤ (∑ x ∈ L.labels.filter P, f x) +
    (∑ x ∈ L.labels.filter (fun x => Sq (L.cofactor x) Y), g x) +
    ∑ x ∈ L.labels.filter (fun x => ¬ (L.cofactor x).Coprime N), f x
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro x hx
  have hf : 0 ≤ f x := mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _)
  have hg : 0 ≤ g x := mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _)
  have hfg : f x ≤ g x := mul_le_mul_of_nonneg_left
    (by exact_mod_cast card_filter_le (L.primes x) _) (L.weight_nonneg x hx)
  by_cases hp : P x
  · simp only [if_pos hp]
    split_ifs <;> linarith
  · by_cases hc : (L.cofactor x).Coprime N
    · simp only [if_neg hp, if_pos (hs x hx hc hp), if_neg (not_not.mpr hc)]
      linarith
    · simp only [if_neg hp, if_pos hc]
      split_ifs <;> linarith

end Wu2008DoubleSieve.LabelledPhysical.Family

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Uniform original-family purification, before either exceptional payment. -/
theorem source_primeMass_rough_square_bad (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ high : Bool,
      (sourceFamily N δ Δ V p high).primeMass ≤
        (roughFamily N δ Δ V p high).primeMass +
        (sourceFamily N δ Δ V p high).squareRawMass ((N : ℝ)^(wuLocalExponent k δ/10)) +
        (sourceFamily N δ Δ V p high).noncoprimePart.primeMass := by
  obtain ⟨T,hT,hu⟩ := actual_family_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp high
  apply LabelledPhysical.Family.primeMass_le_restrict_add_square_add_bad
  intro x hx hc hn
  have hi := ((hu N hN i Δ V hb).2 p hp high).2.2 x hx
  exact masked_good_nonrough_square hi.2.1 hc hn hi.2.2

/-- Both square raw exceptions and bad-N prime exceptions are paid internally,
with a single epsilon for the two original prime masses. -/
theorem source_prime_pair_le_rough (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (sourceFamily N δ Δ V p false).primeMass +
        (sourceFamily N δ Δ V p true).primeMass ≤
        (roughFamily N δ Δ V p false).primeMass +
        (roughFamily N δ Δ V p true).primeMass +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := source_primeMass_rough_square_bad k hδ hδhi
  obtain ⟨T1,_,h1⟩ := source_squareRawMass_payment k hδ hδhi (half_pos hε)
  obtain ⟨T2,_,h2⟩ := source_bad_primeMass_pair_theta_relative k hδ hδhi (half_pos hε)
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb p hp
  have hN0 := (le_max_left T0 (max T1 T2)).trans hN
  have hN12 := (le_max_right T0 (max T1 T2)).trans hN
  have ha := h0 N hN0 i Δ V hb p hp false
  have hb' := h0 N hN0 i Δ V hb p hp true
  have hs := h1 N ((le_max_left _ _).trans hN12) i Δ V hb p hp
  have he := h2 N ((le_max_right _ _).trans hN12) i Δ V hb p hp
  dsimp only at hs
  linarith

/-- The original two actual sources, not their raw envelopes, reach canonical rough prime mass. -/
theorem actual_source_pair_le_rough (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      actualSource N δ p (convolutionWuWindows N Δ V) false +
        actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        (roughFamily N δ Δ V p false).primeMass +
        (roughFamily N δ Δ V p true).primeMass +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hu⟩ := source_prime_pair_le_rough k hδ hδhi hε
  refine ⟨T,hT,?_⟩
  intro N hN he i Δ V hb p hp hs
  exact (add_le_add (mother_source_le_family p hp hs (hT.trans hN) he hδ hδhi hb false)
    (mother_source_le_family p hp hs (hT.trans hN) he hδ hδhi hb true)).trans
      (hu N hN i Δ V hb p hp)

/-- Full density on canonical rough raw mass, with one epsilon for all payments.
This is not a purification inequality for the original raw mass. -/
theorem actual_source_pair_rough_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      actualSource N δ p (convolutionWuWindows N Δ V) false +
        actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        ((roughFamily N δ Δ V p false).mass + (roughFamily N δ Δ V p true).mass) *
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
            wuSingularSeries N/log N) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,h0⟩ := actual_source_pair_le_rough k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,h1⟩ := rough_prime_pair_density k hδ hδhi hρ (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN he i Δ V hb p hp hs
  have ha := h0 N ((le_max_left _ _).trans hN) he i Δ V hb p hp hs
  have hd := h1 N ((le_max_right _ _).trans hN) he i Δ V hb p hp
  linarith

end Wu2008DoubleSieve.HighNonunit
