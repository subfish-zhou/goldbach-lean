import WR2GammaHighTailUnitGeometry
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledMissingMass

noncomputable section
namespace WuPaper.R2GammaHigh.TailUnit
open Wu2008DoubleSieve HighUnitSieve Finset SecondFunctionalUnitPrimeFibre
open scoped Classical

variable {n N : ℕ} {δ : ℝ}
variable (row : Fin 3)
variable (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1/100)
variable (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
variable (j : Fin n) (b : ℕ → ℝ)

/-- The real original-weight family; all local geometry is produced from the source box. -/
noncomputable def sourceFamily :
    LabelledPhysical.Family (Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)) N where
  labels := family N (windows row N) P j b
  weight := fun c => (convolutionCoeff (windows row N) c.1 : ℝ)
  cofactor := cofactor
  lower := lower j
  upper := upper N b
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := fun c hc => by
    have h := source_profile_geometry row hN hδ hδhi P j b hc
    exact ⟨h.positive,h.lower_two,h.feasible,h.physical⟩

theorem sourceFamily_primes {c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)}
    (hc : c ∈ family N (windows row N) P j b) :
    (sourceFamily row hN hδ hδhi P j b).primes c = fibre (lower j c) (upper N b c) := by
  have h := source_profile_geometry row hN hδ hδhi P j b hc
  exact (interval_eq_profile h.positive h.lower_two h.feasible h.physical).symm

theorem sourceFamily_mass :
    (sourceFamily row hN hδ hδhi P j b).mass =
      intervalMass N (windows row N)
        (family N (windows row N) P j b) j b := by
  unfold LabelledPhysical.Family.mass intervalMass
  apply sum_congr rfl
  intro c hc
  rw [sourceFamily_primes row hN hδ hδhi P j b hc]
  rfl

theorem sourceFamily_primeMass :
    (sourceFamily row hN hδ hδhi P j b).primeMass =
      outputMass N (windows row N)
        (family N (windows row N) P j b) j b := by
  unfold LabelledPhysical.Family.primeMass outputMass
  apply sum_congr rfl
  intro c hc
  rw [sourceFamily_primes row hN hδ hδhi P j b hc]
  rfl

/-- The sieve's strict small-output term is bounded by the proved closed real carrier. -/
theorem sourceFamily_small_le (Z : ℝ) :
    (sourceFamily row hN hδ hδhi P j b).small Z ≤
      smallOutputMassReal N Z (windows row N)
        (family N (windows row N) P j b) j b := by
  unfold LabelledPhysical.Family.small smallOutputMassReal
  apply sum_le_sum
  intro c hc
  rw [sourceFamily_primes row hN hδ hδhi P j b hc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hsub :
      (fibre (lower j c) (upper N b c)).filter
        (fun q => (N-cofactor c*q).Prime ∧ ((N-cofactor c*q : ℕ) : ℝ) < Z) ⊆
      (fibre (lower j c) (upper N b c)).filter
        (fun q => (N-cofactor c*q).Prime ∧ ((N-cofactor c*q : ℕ) : ℝ) ≤ Z) := by
    intro q hq
    obtain ⟨hq,hp,hz⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨hq,hp,hz.le⟩
  exact_mod_cast card_le_card hsub

/-- The finite sieve inequality now consumes the actual original source family. -/
theorem source_family_prime_upper (heven : Even N) (D : ℕ) (Z : ℝ)
    (hD : 1 < D) (hZD : Z ≤ (D : ℝ)) :
    let W := windows row N
    let S := family N W P j b
    let L := sourceFamily row hN hδ hδhi P j b
    outputMass N W S j b ≤ intervalMass N W S j b * ordinaryRosserMainSum true N 1 D Z +
      L.R1 D Z + L.R2 D Z + smallOutputMassReal N Z W S j b := by
  dsimp only
  have h := (sourceFamily row hN hδ hδhi P j b).prime_upper_finite heven D Z hD hZD
  rw [sourceFamily_mass, sourceFamily_primeMass] at h
  exact h.trans (by linarith [sourceFamily_small_le row hN hδ hδhi P j b Z])

end WuPaper.R2GammaHigh.TailUnit
#print axioms WuPaper.R2GammaHigh.TailUnit.source_family_prime_upper
