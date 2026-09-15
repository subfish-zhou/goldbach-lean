import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRestrictionDensity
import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniform

namespace Wu2008DoubleSieve.HighNonunit
open Finset Real
open scoped Classical

/-- Global roughness of the actual residual, at its actual penultimate prime. -/
def profileRough (x : Profile) : Prop :=
  LiLiuPrereqBuchstab.Rough (x.2.2.1 : ℝ) x.2.2.2

/-- No new coprimality gate: only the residual roughness test is added. -/
noncomputable def roughFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (high : Bool) : LabelledPhysical.Family Profile N :=
  (sourceFamily N δ Δ V p high).restrictLabels profileRough

theorem mem_roughFamily_labels {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (high : Bool) (x : Profile) :
    x ∈ (roughFamily N δ Δ V p high).labels ↔
      x ∈ (sourceFamily N δ Δ V p high).labels ∧ profileRough x := by
  exact mem_filter

/-- Density for the rough family itself; original-source purification is separate. -/
theorem rough_prime_pair_density (k : ℕ) {δ ρ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (roughFamily N δ Δ V p false).primeMass +
        (roughFamily N δ Δ V p true).primeMass ≤
        ((roughFamily N δ Δ V p false).mass + (roughFamily N δ Δ V p true).mass) *
          ((1+ρ)*(1+ρ*exp (-eulerMascheroniConstant))*(8/(1-2*δ))*
            wuSingularSeries N/log N) +
        ε * boxTheta N ((N : ℝ)^(1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T,hT,hd⟩ := source_restrict_prime_pair_density k hδ hδhi hρ hε
  exact ⟨T,hT,fun N hN he i Δ V hb p hp => hd N hN he i Δ V hb p hp profileRough profileRough⟩

end Wu2008DoubleSieve.HighNonunit
