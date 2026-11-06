import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledMissingMass
import MathlibNt.Wu2008DoubleSieve.Omega3SharedPrimeRoughness

/-! Relative-to-N roughness pays only the original additive missing mass. -/
namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset Real
open scoped Classical
universe u
variable {α : Type u} {N : ℕ} (L : Family α N)

theorem missing_le_relative {q : ℕ} {Y F : ℝ} (hY : 0 < Y) (hF : 0 ≤ F)
    (hq : 0 < q) (hqN : q ≤ N) (hcop : q.Coprime N)
    (hrough : ∀ c ∈ L.labels, ∀ p, p.Prime → p ∣ L.cofactor c → p.Coprime N → Y ≤ (p : ℝ))
    (hfibre : ∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) :
    L.missing q ≤ F * N * ((1 + log N) * log N / (Y * log 2)) := by
  let E := L.labels.image L.cofactor
  have hE : ∀ e ∈ E, 0 < e ∧ e ≤ N := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨(L.geometry c hc).1, L.cofactor_le hc⟩
  have hEr : ∀ e ∈ E, ∀ p, p.Prime → p ∣ e → p.Coprime N → Y ≤ (p : ℝ) := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact hrough c hc
  exact (L.missing_le_reciprocal q hfibre).trans (mul_le_mul_of_nonneg_left
    (omega3_relative_rough_non_coprime_reciprocal_le N q E hY hq hqN hcop hE hEr) (by positivity))

/-- One Euler constant works for every label type, geometry and original weight. -/
theorem R2_euler_relative :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N →
      ∀ (α : Type u) (L : Family α N) (D : ℕ) (Z Y F : ℝ),
      Z ≤ N → 0 < Y → 0 ≤ F →
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      (∀ c ∈ L.labels, ∀ p, p.Prime → p ∣ L.cofactor c → p.Coprime N → Y ≤ (p : ℝ)) →
      (∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) →
      L.R2 D Z ≤ C * F * N * ((1 + log N) * log N ^ 4 / (Y * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN α L D Z Y F hZ hY hF hqN hrough hfibre
  have hs := sum_le_sum (s := omega3SieveModuli N D Z) (fun q hq =>
    mul_le_mul_of_nonneg_left
      (L.missing_le_relative hY hF (omega3SieveModuli_properties hq).1 (hqN q hq)
        (omega3SieveModuli_properties hq).2.2.1 hrough hfibre)
      (show 0 ≤ (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) by positivity))
  rw [← sum_mul] at hs
  have hm : (∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
      C * log N ^ 3 :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)).trans
      (hmass N hN Z hZ)
  have hn : 0 ≤ F * N * ((1 + log N) * log N / (Y * log 2)) := by
    have := log_natCast_nonneg N
    positivity
  exact hs.trans ((mul_le_mul_of_nonneg_right hm hn).trans_eq (by ring))



end Wu2008DoubleSieve.LabelledPhysical.Family
