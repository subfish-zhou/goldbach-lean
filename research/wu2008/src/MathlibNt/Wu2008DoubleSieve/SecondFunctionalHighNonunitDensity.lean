import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitExceptionPayment
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Both good families consume the actual finite sieve, with one total error. -/
theorem source_good_prime_pair_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let Q := (N : ℝ)^(1/2-δ)
      let L0 := (sourceFamily N δ Δ V p false).coprimePart
      let L1 := (sourceFamily N δ Δ V p true).coprimePart
      L0.primeMass + L1.primeMass ≤
        (L0.mass + L1.mass) * ordinaryRosserMainSum true N 1 (⌊Q⌋₊+1) (sqrt Q) +
          ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hr⟩ := source_R1_pair_theta_relative k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,he⟩ := source_R2_small_payment k hδ hδhi (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb p hp
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  let Q := (N : ℝ)^(1/2-δ)
  let D := ⌊Q⌋₊+1
  let Z := sqrt Q
  let L0 := r1Family N δ Δ V p false true
  let L1 := r1Family N δ Δ V p true true
  obtain ⟨hD,hZD,_,_,_,_,_,hsmall⟩ := he N hN1 i Δ V hb p hp true true
  have h0 := L0.prime_upper_finite heven D Z hD hZD
  have h1 := L1.prime_upper_finite heven D Z hD hZD
  have hR1 := hr N hN0 i Δ V hb p hp true Z
  change L0.primeMass + L1.primeMass ≤ (L0.mass + L1.mass) *
    ordinaryRosserMainSum true N 1 D Z + ε * boxTheta N Q (convolutionWuWindows N Δ V)
  change L0.R2 D Z + L1.R2 D Z + (L0.small Z + L1.small Z) ≤
    (ε/2) * boxTheta N Q (convolutionWuWindows N Δ V) at hsmall
  change L0.R1 D Z + L1.R1 D Z ≤
    (ε/2) * boxTheta N Q (convolutionWuWindows N Δ V) at hR1
  nlinarith only [h0,h1,hsmall,hR1]

/-- Original prime masses are controlled by the actual GOOD raw masses.
The discarded bad prime outputs have been paid; no claim on bad raw mass is made. -/
theorem source_prime_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (sourceFamily N δ Δ V p false).primeMass +
        (sourceFamily N δ Δ V p true).primeMass ≤
        ((sourceFamily N δ Δ V p false).coprimePart.mass +
          (sourceFamily N δ Δ V p true).coprimePart.mass) *
          (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
            wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hpaid⟩ := source_good_prime_pair_paid k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hexc⟩ := sourceFamily_pair_le_good_primeMass k hδ hδhi (half_pos hε)
  obtain ⟨T2,_,hden⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb p hp
  have hN0 := (le_max_left T0 _).trans hN
  have hN1 := (le_max_left T1 T2).trans ((le_max_right T0 _).trans hN)
  have hN2 := (le_max_right T1 T2).trans ((le_max_right T0 _).trans hN)
  have hf := hpaid N hN0 heven i Δ V hb p hp
  have he := hexc N hN1 i Δ V hb p hp
  have hx : 0 ≤ (sourceFamily N δ Δ V p false).coprimePart.mass +
      (sourceFamily N δ Δ V p true).coprimePart.mass := by
    apply add_nonneg <;> unfold LabelledPhysical.Family.mass <;>
      apply sum_nonneg <;> intro x hx <;>
      exact mul_nonneg (LabelledPhysical.Family.weight_nonneg _ x hx) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (hden N hN2 heven) hx
  dsimp only at hf he hm ⊢
  linarith

/-- Actual nonunit sources consume the complete density chain, with original sigma,
unchanged fixed-delta factor, actual good raw mass and a single total epsilon. -/
theorem mother_nonunit_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → 2 ≤ p.s →
      actualSource N δ p (convolutionWuWindows N Δ V) false +
        actualSource N δ p (convolutionWuWindows N Δ V) true ≤
        ((sourceFamily N δ Δ V p false).coprimePart.mass +
          (sourceFamily N δ Δ V p true).coprimePart.mass) *
          (((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))) *
            wuSingularSeries N / log N) +
          ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_prime_pair_density k hδ hδhi hρ hε
  refine ⟨T,hT,?_⟩
  intro N hN heven i Δ V hb p hp hs
  exact (add_le_add (mother_source_le_family p hp hs (hT.trans hN) heven hδ hδhi hb false)
    (mother_source_le_family p hp hs (hT.trans hN) heven hδ hδhi hb true)).trans
      (hd N hN heven i Δ V hb p hp)

end Wu2008DoubleSieve.HighNonunit
