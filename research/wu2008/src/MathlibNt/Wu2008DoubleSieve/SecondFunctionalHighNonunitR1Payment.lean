import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitActualFamily
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveSmall
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledCoprimeOutputFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledR1Relative

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Explicit choice of the original family or its coprime part.
Using the coprime part in a PRIME-MASS bound still requires its separate exceptional term. -/
noncomputable def r1Family {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high coprimeOnly : Bool) : LabelledPhysical.Family Profile N :=
  if coprimeOnly then (sourceFamily N δ Δ V p high).coprimePart
  else sourceFamily N δ Δ V p high

theorem r1Family_subset {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (high coprimeOnly : Bool) :
    (r1Family N δ Δ V p high coprimeOnly).labels ⊆ (sourceFamily N δ Δ V p high).labels := by
  cases coprimeOnly
  · exact Subset.rfl
  · exact filter_subset _ _

theorem r1Family_data {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (high coprimeOnly : Bool) (x : Profile) :
    (r1Family N δ Δ V p high coprimeOnly).weight x =
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) ∧
    (r1Family N δ Δ V p high coprimeOnly).cofactor x = cofactor x := by
  cases coprimeOnly <;> exact ⟨rfl,rfl⟩

/-- Actual nonunit families supply all power, positivity and full original-sigma fibre bounds.
The common threshold is chosen before boxes, mother parameters, words and sieve cutoffs. -/
theorem source_R1_theta_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ high coprimeOnly : Bool, ∀ Z : ℝ,
        (r1Family N δ Δ V p high coprimeOnly).R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  let η := wuLocalExponent k δ / 10
  let H := max 1 (1/η)
  let F := H^(k+5)
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T1,hT1,hd⟩ := LabelledPhysical.Family.R1_theta_relative k hδ hδhi hε hη
    (show 0 ≤ F by dsimp [F,H]; positivity)
  obtain ⟨T2,_,hm⟩ := source_multiplicities k hδ hδhi
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb p hp high good Z
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hNtwo : 2 ≤ N := by have := hT1.trans hN1; omega
  let L := r1Family N δ Δ V p high good
  have hsub := r1Family_subset (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
  have hdata := r1Family_data (N := N) (δ := δ) (Δ := Δ) (V := V) p high good
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

/-- The two actual words together use one total epsilon, for either explicit family choice. -/
theorem source_R1_pair_theta_relative (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      ∀ good : Bool, ∀ Z : ℝ,
        (r1Family N δ Δ V p false good).R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z +
        (r1Family N δ Δ V p true good).R1 (⌊(N:ℝ)^(1/2-δ)⌋₊+1) Z ≤
          ε * boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_R1_theta_relative k hδ hδhi (show 0 < ε/2 by positivity)
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp good Z
  have h0 := hd N hN i Δ V hb p hp false good Z
  have h1 := hd N hN i Δ V hb p hp true good Z
  linarith

end Wu2008DoubleSieve.HighNonunit
