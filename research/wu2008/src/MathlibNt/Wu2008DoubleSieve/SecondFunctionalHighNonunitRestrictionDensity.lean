import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRestriction
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitErrorPayment
import MathlibNt.Wu2008DoubleSieve.Omega3SourceDensity

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Reapply generic R1 to every actual label restriction; no R1 subset inequality. -/
theorem source_restrict_R1_theta_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ high : Bool, ∀ P : Profile → Prop, ∀ Z : ℝ,
        ((sourceFamily N δ Δ V p high).restrictLabels P).R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+5)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1,hT1,hd⟩ := LabelledPhysical.Family.R1_theta_relative k hδ hδhi hε hη
    (show 0 ≤ F by dsimp [F,H]; positivity)
  obtain ⟨T2,_,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp high P Z
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNtwo : 2 ≤ N := by have := hT1.trans hN1; omega
  let L := (sourceFamily N δ Δ V p high).restrictLabels P
  have hsub : L.labels ⊆ (sourceFamily N δ Δ V p high).labels := filter_subset _ _
  have hdata (x : Profile) : L.weight x =
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) ∧
      L.cofactor x = cofactor x := ⟨rfl,rfl⟩
  have hf := (hm N hN2 i Δ V hb p hp high).1
  apply hd N hN1 i Δ V hb Profile L _ _ _ Z
  · intro x hx
    have hg := actual_source_geometry hNtwo hδ hδhi hb p hp high (hsub hx)
    rw [(hdata x).2]
    exact ⟨hg.power_lower,hg.power_upper⟩
  · intro x hx
    rw [(hdata x).1]
    exact_mod_cast actual_coefficient_pos (mem_filter.mp (hsub hx)).1
  · intro e
    have hs : L.layerFibre e ⊆
        (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter (fun x => cofactor x = e) := by
      intro x hx
      obtain ⟨hx,he⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp (hsub hx)).1, (hdata x).2.symm.trans he⟩
    calc
      _ = ∑ x ∈ L.layerFibre e, (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_congr rfl (fun x _ => (hdata x).1)
      _ ≤ ∑ x ∈ (actualProfiles N δ p (convolutionWuWindows N Δ V) high).filter
          (fun x => cofactor x = e), (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ H^(k+arity high) := hf e
      _ ≤ F := pow_le_pow_right₀ (le_max_left 1 _) (by cases high <;> simp [arity])

/-- Every pair of data-preserving restrictions has one total error budget. -/
theorem source_restrict_prime_pair_paid (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P0 P1 : Profile → Prop,
      let L0 := (sourceFamily N δ Δ V p false).restrictLabels P0
      let L1 := (sourceFamily N δ Δ V p true).restrictLabels P1
      let Q := (N : ℝ)^(1/2-δ)
      L0.primeMass + L1.primeMass ≤
        (L0.mass + L1.mass) * ordinaryRosserMainSum true N 1 (⌊Q⌋₊+1) (sqrt Q) +
          ε * boxTheta N Q (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hr⟩ := source_restrict_R1_theta_relative k hδ hδhi
    (show 0 < ε/4 by positivity)
  obtain ⟨T1,_,he⟩ := source_R2_small_payment k hδ hδhi
    (show 0 < ε/2 by positivity)
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp P0 P1
  have hN0 := (le_max_left T0 T1).trans hN
  have hN1 := (le_max_right T0 T1).trans hN
  let Q := (N : ℝ)^(1/2-δ)
  let D := ⌊Q⌋₊+1
  let Z := sqrt Q
  let A0 := sourceFamily N δ Δ V p false
  let A1 := sourceFamily N δ Δ V p true
  let L0 := A0.restrictLabels P0
  let L1 := A1.restrictLabels P1
  obtain ⟨hD,hZ,_,_,_,_,_,hpaid⟩ := he N hN1 i Δ V hb p hp false false
  have h0 := L0.prime_upper_finite hn D Z hD hZ
  have h1 := L1.prime_upper_finite hn D Z hD hZ
  have hr0 := hr N hN0 i Δ V hb p hp false P0 Z
  have hr1 := hr N hN0 i Δ V hb p hp true P1 Z
  have he' : L0.R2 D Z + L1.R2 D Z + (L0.small Z + L1.small Z) ≤
      (ε/2)*boxTheta N Q (convolutionWuWindows N Δ V) := by
    calc
      _ ≤ A0.R2 D Z + A1.R2 D Z + (A0.small Z + A1.small Z) := by
        linarith only [A0.restrictLabels_R2_le P0 D Z, A1.restrictLabels_R2_le P1 D Z,
          A0.restrictLabels_small_le P0 Z, A1.restrictLabels_small_le P1 Z]
      _ ≤ _ := hpaid
  change L0.primeMass + L1.primeMass ≤
    (L0.mass + L1.mass) * ordinaryRosserMainSum true N 1 D Z +
      ε * boxTheta N Q (convolutionWuWindows N Δ V)
  nlinarith only [h0,h1,hr0,hr1,he']

/-- Actual restricted masses, not original or coprime masses, are the density main term. -/
theorem source_restrict_prime_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ P0 P1 : Profile → Prop,
      let L0 := (sourceFamily N δ Δ V p false).restrictLabels P0
      let L1 := (sourceFamily N δ Δ V p true).restrictLabels P1
      L0.primeMass + L1.primeMass ≤ (L0.mass + L1.mass) *
        ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
          wuSingularSeries N/log N) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT0,hf⟩ := source_restrict_prime_pair_paid k hδ hδhi hε
  obtain ⟨T1,_,hd⟩ := omega3_source_rosser_density hδ hδhi hρ
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN hn i Δ V hb p hp P0 P1
  have hf' := hf N ((le_max_left _ _).trans hN) hn i Δ V hb p hp P0 P1
  have hd' := hd N ((le_max_right _ _).trans hN) hn
  let L0 := (sourceFamily N δ Δ V p false).restrictLabels P0
  let L1 := (sourceFamily N δ Δ V p true).restrictLabels P1
  have hm (L : LabelledPhysical.Family Profile N) : 0 ≤ L.mass :=
    sum_nonneg (fun x hx => mul_nonneg (L.weight_nonneg x hx) (Nat.cast_nonneg _))
  have hx := mul_le_mul_of_nonneg_left hd' (add_nonneg (hm L0) (hm L1))
  exact hf'.trans (add_le_add hx le_rfl)

end Wu2008DoubleSieve.HighNonunit
