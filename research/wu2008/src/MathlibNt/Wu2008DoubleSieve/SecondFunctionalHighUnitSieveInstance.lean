import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSieveMultiplicity
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledMissingMass

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitSieve
open Finset SecondFunctionalUnitPrimeFibre

variable {i k n N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
variable (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
variable (hb : wuSourceBox k δ N i Δ V)
variable (P : ∀ d : ℕ, Finset (Fin n → primeSlabPrimes ((N : ℝ) ^ (1/2-δ)/d)))
variable (j : Fin n) (b : ℕ → ℝ)

/-- The real original-weight family; all local geometry is produced from the source box. -/
noncomputable def sourceFamily :
    LabelledPhysical.Family (Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)) N where
  labels := family N (convolutionWuWindows N Δ V) P j b
  weight := fun c => (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)
  cofactor := cofactor
  lower := lower j
  upper := upper N b
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := fun c hc => by
    have h := source_profile_geometry hN hδ hδhi hb P j b hc
    exact ⟨h.positive,h.lower_two,h.feasible,h.physical⟩

theorem sourceFamily_primes {c : Profile n (fun d => (N : ℝ) ^ (1/2-δ)/d)}
    (hc : c ∈ family N (convolutionWuWindows N Δ V) P j b) :
    (sourceFamily hN hδ hδhi hb P j b).primes c = fibre (lower j c) (upper N b c) := by
  have h := source_profile_geometry hN hδ hδhi hb P j b hc
  exact (interval_eq_profile h.positive h.lower_two h.feasible h.physical).symm

theorem sourceFamily_mass :
    (sourceFamily hN hδ hδhi hb P j b).mass =
      intervalMass N (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
  unfold LabelledPhysical.Family.mass intervalMass
  apply sum_congr rfl
  intro c hc
  rw [sourceFamily_primes hN hδ hδhi hb P j b hc]
  rfl

theorem sourceFamily_primeMass :
    (sourceFamily hN hδ hδhi hb P j b).primeMass =
      outputMass N (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
  unfold LabelledPhysical.Family.primeMass outputMass
  apply sum_congr rfl
  intro c hc
  rw [sourceFamily_primes hN hδ hδhi hb P j b hc]
  rfl

/-- The sieve's strict small-output term is bounded by the proved closed real carrier. -/
theorem sourceFamily_small_le (Z : ℝ) :
    (sourceFamily hN hδ hδhi hb P j b).small Z ≤
      smallOutputMassReal N Z (convolutionWuWindows N Δ V)
        (family N (convolutionWuWindows N Δ V) P j b) j b := by
  unfold LabelledPhysical.Family.small smallOutputMassReal
  apply sum_le_sum
  intro c hc
  rw [sourceFamily_primes hN hδ hδhi hb P j b hc]
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
    let W := convolutionWuWindows N Δ V
    let S := family N W P j b
    let L := sourceFamily hN hδ hδhi hb P j b
    outputMass N W S j b ≤ intervalMass N W S j b * ordinaryRosserMainSum true N 1 D Z +
      L.R1 D Z + L.R2 D Z + smallOutputMassReal N Z W S j b := by
  dsimp only
  have h := (sourceFamily hN hδ hδhi hb P j b).prime_upper_finite heven D Z hD hZD
  rw [sourceFamily_mass, sourceFamily_primeMass] at h
  exact h.trans (by linarith [sourceFamily_small_le hN hδ hδhi hb P j b Z])

omit P j b in
/-- Both actual mother words consume the new sieve, with precisely the original X. -/
theorem mother_prime_pair_upper (p : SecondFunctionalParameters)
    (heven : Even N) (D : ℕ) (Z : ℝ) (hD : 1 < D) (hZD : Z ≤ (D : ℝ)) :
    let W := convolutionWuWindows N Δ V
    let R := fun d : ℕ => (N : ℝ) ^ (1/2-δ)/d
    let a2 := fun _ : ℕ => 1/p.kappa2
    let a3 := fun _ : ℕ => 1/p.kappa3
    let b := fun _ : ℕ => 1/p.s
    let P20 := fun d => HighUnit.primePrefix20 (R d) (a2 d) (a3 d) (b d)
    let P21 := fun d => HighUnit.primePrefix21 (R d) (a3 d) (b d)
    let L20 := sourceFamily hN hδ hδhi hb P20 (Fin.last 3) b
    let L21 := sourceFamily hN hδ hδhi hb P21 (Fin.last 4) b
    HighUnitPrimeOutput.envelope20 N W R a2 a3 b + HighUnitPrimeOutput.envelope21 N W R a3 b ≤
      (HighUnit.boxedSigma20 N δ W a2 a3 b + HighUnit.boxedSigma21 N δ W a3 b) *
        ordinaryRosserMainSum true N 1 D Z + (L20.R1 D Z + L21.R1 D Z) +
        (L20.R2 D Z + L21.R2 D Z) +
        (smallOutputMassReal N Z W (family20 N W R a2 a3 b) (Fin.last 3) b +
          smallOutputMassReal N Z W (family21 N W R a3 b) (Fin.last 4) b) := by
  dsimp only
  have h20 := source_family_prime_upper hN hδ hδhi hb
    (fun d => HighUnit.primePrefix20 ((N : ℝ) ^ (1/2-δ)/d) (1/p.kappa2) (1/p.kappa3) (1/p.s))
    (Fin.last 3) (fun _ => 1/p.s) heven D Z hD hZD
  have h21 := source_family_prime_upper hN hδ hδhi hb
    (fun d => HighUnit.primePrefix21 ((N : ℝ) ^ (1/2-δ)/d) (1/p.kappa3) (1/p.s))
    (Fin.last 4) (fun _ => 1/p.s) heven D Z hD hZD
  obtain ⟨hM20,hM21,hE20,hE21⟩ := source_dictionary hN hδ hδhi hb
    (fun _ => 1/p.kappa2) (fun _ => 1/p.kappa3) (fun _ => 1/p.s)
  dsimp only at hM20 hM21 hE20 hE21 h20 h21
  rw [hM20,hM21,hE20,hE21]
  change _ ≤ _ at h20 h21
  dsimp only [family20,family21] at *
  nlinarith

end Wu2008DoubleSieve.HighUnitSieve
