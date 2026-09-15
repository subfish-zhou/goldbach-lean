import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeR1Transport
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeErrorPayment
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeExceptionPayment
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset Real
open scoped Classical

/-- The actual finite sieve consumes the three paid errors on each restricted family. -/
theorem source_restricted_prime_four_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P : Fin 4 → Gamma16Profile → Prop,
      let Q := (N : ℝ)^(1/2-δ)
      let L := fun j => (sourceFamily N δ Δ V p j).restrictLabels (P j)
      (∑ j : Fin 4, (L j).primeMass) ≤
        (∑ j : Fin 4, (L j).mass) * ordinaryRosserMainSum true N 1 (⌊Q⌋₊+1) (sqrt Q) +
          ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hr⟩ := source_restricted_R1_four_theta k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,he⟩ := source_restricted_R2_small_payment k hδ hδhi (half_pos hε)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp P
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  let Q := (N : ℝ)^(1/2-δ)
  let D := ⌊Q⌋₊+1
  let Z := sqrt Q
  let L := fun j => (sourceFamily N δ Δ V p j).restrictLabels (P j)
  obtain ⟨hD,hZD,_,_,_,_,herr⟩ := he N hN1 i Δ V hb p hp P
  have hR1 := hr N hN0 i Δ V hb p hp P Z
  have hf := sum_le_sum (s := (univ : Finset (Fin 4)))
    (fun j _ => (L j).prime_upper_finite hn D Z hD hZD)
  simp only [sum_add_distrib, ← sum_mul] at hf
  change (∑ j : Fin 4, (L j).R1 D Z) ≤
    (ε/2)*boxTheta N Q (convolutionWuWindows N Δ V) at hR1
  change (∑ j : Fin 4, (L j).R2 D Z) + (∑ j : Fin 4, (L j).small Z) ≤
    (ε/2)*boxTheta N Q (convolutionWuWindows N Δ V) at herr
  dsimp only at hf ⊢
  linarith only [hf,hR1,herr]

/-- The leading factor multiplies the actual restricted raw mass, never a source upper bound. -/
theorem source_restricted_prime_four_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P : Fin 4 → Gamma16Profile → Prop,
      let L := fun j => (sourceFamily N δ Δ V p j).restrictLabels (P j)
      (∑ j : Fin 4, (L j).primeMass) ≤ (∑ j : Fin 4, (L j).mass) *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hf⟩ := source_restricted_prime_four_paid k hδ hδhi hε
  obtain ⟨T1,_,hd⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp P
  have hf' := hf N ((le_max_left _ _).trans hN) hn i Δ V hb p hp P
  have hd' := hd N ((le_max_right _ _).trans hN) hn
  have hm : 0 ≤ ∑ j : Fin 4, ((sourceFamily N δ Δ V p j).restrictLabels (P j)).mass := by
    apply sum_nonneg
    intro j _
    exact sum_nonneg (fun x hx => mul_nonneg
      (((sourceFamily N δ Δ V p j).restrictLabels (P j)).weight_nonneg x hx) (Nat.cast_nonneg _))
  exact hf'.trans (add_le_add (mul_le_mul_of_nonneg_left hd' hm) le_rfl)

/-- Selecting one word changes no data on that word and makes the other label sums empty. -/
theorem sum_single_label_filter {N : ℕ} (L : Fin 4 → LabelledPhysical.Family Gamma16Profile N)
    (j : Fin 4) (P : Gamma16Profile → Prop) (F : LabelledPhysical.Family Gamma16Profile N → ℝ)
    (hz : ∀ M : LabelledPhysical.Family Gamma16Profile N,
      F (M.restrictLabels (fun _ => False)) = 0) :
    (∑ a : Fin 4, F ((L a).restrictLabels (fun x => a=j ∧ P x))) = F ((L j).restrictLabels P) := by
  rw [sum_eq_single j]
  · simp
  · intro a _ ha
    have he : (fun x => a=j ∧ P x) = (fun _ => False) := by funext x; simp [ha]
    rw [he]
    exact hz (L a)
  · simp

/-- The same threshold controls every individual restricted word as well. -/
theorem source_restricted_prime_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      ∀ P : Gamma16Profile → Prop,
      let L := (sourceFamily N δ Δ V p j).restrictLabels P
      L.primeMass ≤ L.mass *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_restricted_prime_four_density k hδ hδhi hρ hε
  refine ⟨T,hT,?_⟩
  intro N hN hn i Δ V hb p hp j P
  have h := hd N hN hn i Δ V hb p hp (fun a x => a=j ∧ P x)
  have he := sum_single_label_filter (sourceFamily N δ Δ V p) j P (fun M => M.primeMass)
    (by intro M; simp [LabelledPhysical.Family.primeMass,LabelledPhysical.Family.restrictLabels])
  have hm := sum_single_label_filter (sourceFamily N δ Δ V p) j P (fun M => M.mass)
    (by intro M; simp [LabelledPhysical.Family.mass,LabelledPhysical.Family.restrictLabels])
  dsimp only at h
  rw [he,hm] at h
  exact h

/-- Original prime masses reach canonical rough RAW masses after the exception budget. -/
theorem source_rough_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      let A := (1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N
      let Θ := boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V)
      (∀ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).mass * A + ε*Θ) ∧
      (∑ j : Fin 4, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 4, (roughFamily N δ Δ V p j).mass) * A + ε*Θ := by
  obtain ⟨T0,hT0,hpuri⟩ := source_prime_purification k hδ hδhi (half_pos hε)
  obtain ⟨T1,_,hsingle⟩ := source_restricted_prime_density k hδ hδhi hρ (half_pos hε)
  obtain ⟨T2,_,hfour⟩ := source_restricted_prime_four_density k hδ hδhi hρ (half_pos hε)
  refine ⟨max T0 (max T1 T2),hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp
  have hN0 := (le_max_left T0 _).trans hN
  have hN12 := (le_max_right T0 _).trans hN
  have hu := hpuri N hN0 i Δ V hb p hp
  constructor
  · intro j
    have hd := hsingle N ((le_max_left T1 T2).trans hN12) hn i Δ V hb p hp j profileRough
    have hj := hu.1 j
    change (roughFamily N δ Δ V p j).primeMass ≤ _ at hd
    simp only [roughFamily] at hj hd ⊢
    linarith
  · have hd := hfour N ((le_max_right T1 T2).trans hN12) hn i Δ V hb p hp (fun _ => profileRough)
    have hj := hu.2
    change (∑ j : Fin 4, (roughFamily N δ Δ V p j).primeMass) ≤ _ at hd
    simp only [roughFamily] at hj hd ⊢
    linarith

/-- Every actual original word has the same canonical rough-mass density bound. -/
theorem mother_source_rough_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 4,
      actualSource N δ p (convolutionWuWindows N Δ V) j ≤ (roughFamily N δ Δ V p j).mass *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*wuSingularSeries N/log N) +
        ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_rough_density k hδ hδhi hρ hε
  refine ⟨T,hT,?_⟩
  intro N hN hn i Δ V hb p hp j
  have hs := actual_source_le (N := N) (δ := δ) p (convolutionWuWindows N Δ V)
    (fun d h => (omega3_source_support_le_Q (by have := hT.trans hN; omega) hδ hδhi hb h).1)
    (hT.trans hN) hn j
  have hj := (hd N hN hn i Δ V hb p hp).1 j
  rw [(sourceFamily_dictionary N δ Δ V p j).1] at hj
  exact hs.trans hj

end Wu2008DoubleSieve.FourPrimeNonunit
