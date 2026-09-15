import MathlibNt.Wu2008DoubleSieve.Gamma16Layers
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative

/-! # Missing noncoprime prime mass, using the existing rough reciprocal theorem -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem gamma16_family_missing_le {i N q : ℕ} {δ Y F : ℝ}
    (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
    (hY : 0 < Y) (hF : 0 ≤ F) (hq : 0 < q) (hqN : q ≤ N)
    (hgeom : ∀ c ∈ L, 0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
      ∀ p, p.Prime → p ∣ omega3CofactorValue c → Y ≤ (p : ℝ))
    (hfibre : ∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ F) :
    gamma16FamilyMissing N δ W L q ≤ F * N * ((1 + log N) * log N / (Y * log 2)) := by
  let E := L.image omega3CofactorValue
  have hE : ∀ e ∈ E, 0 < e ∧ e ≤ N := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨(hgeom c hc).1, (hgeom c hc).2.1⟩
  have hrough : ∀ e ∈ E, ∀ p, p.Prime → p ∣ e → Y ≤ (p : ℝ) := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact (hgeom c hc).2.2
  have hinner (e : ℕ) :
      (∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
        (convolutionCoeff W c.1 : ℝ) * (if ¬(omega3CofactorValue c).Coprime q then
          ((omega3CofactorPrimeFibreLE N δ (5 / 2) c).card : ℝ) else 0)) ≤
        if ¬e.Coprime q then F * N * (1 / (e : ℝ)) else 0 := by
    by_cases hb : ¬e.Coprime q
    · rw [if_pos hb]
      calc
        _ ≤ ∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
            (convolutionCoeff W c.1 : ℝ) * ((N : ℝ) / e) := by
          apply sum_le_sum
          intro c hc
          obtain ⟨hc, he⟩ := mem_filter.mp hc
          rw [he, if_pos hb]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          simpa only [he] using omega3_prime_fibre_card_le (δ := δ) (s := 5 / 2) (hgeom c hc).1
        _ = (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) * ((N : ℝ) / e) :=
          (sum_mul ..).symm
        _ ≤ F * ((N : ℝ) / e) := mul_le_mul_of_nonneg_right (hfibre e) (by positivity)
        _ = _ := by ring
    · rw [if_neg hb]
      apply le_of_eq
      apply sum_eq_zero
      intro c hc
      rw [(mem_filter.mp hc).2, if_neg hb, mul_zero]
  calc
    _ = ∑ c ∈ L, (convolutionCoeff W c.1 : ℝ) *
        (if ¬(omega3CofactorValue c).Coprime q then
          ((omega3CofactorPrimeFibreLE N δ (5 / 2) c).card : ℝ) else 0) := by
      simp only [gamma16FamilyMissing, sum_filter, mul_ite, mul_zero]
    _ = ∑ e ∈ E, ∑ c ∈ L.filter (fun c => omega3CofactorValue c = e),
        (convolutionCoeff W c.1 : ℝ) * (if ¬(omega3CofactorValue c).Coprime q then
          ((omega3CofactorPrimeFibreLE N δ (5 / 2) c).card : ℝ) else 0) :=
      (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) _).symm
    _ ≤ ∑ e ∈ E, if ¬e.Coprime q then F * N * (1 / (e : ℝ)) else 0 :=
      sum_le_sum (fun e _ => hinner e)
    _ = F * N * ∑ e ∈ E.filter (fun e => ¬e.Coprime q), 1 / (e : ℝ) := by
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (omega3_rough_non_coprime_reciprocal_le N q E hY hq hqN hE hrough) (by positivity)

theorem gamma16_family_R2_euler :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      ∀ (i : ℕ) (δ Z Y F : ℝ) (W : Fin i → Finset ℕ) (L : Finset Omega3CofactorIndex)
        (D : ℕ), Z ≤ N → 0 < Y → 0 ≤ F →
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      (∀ c ∈ L, 0 < omega3CofactorValue c ∧ omega3CofactorValue c ≤ N ∧
        ∀ p, p.Prime → p ∣ omega3CofactorValue c → Y ≤ (p : ℝ)) →
      (∀ e, (∑ c ∈ omega3LayerFibre L e, (convolutionCoeff W c.1 : ℝ)) ≤ F) →
      gamma16FamilyR2 N D δ Z W L ≤
        C * F * N * ((1 + log N) * log N ^ 4 / (Y * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN i δ Z Y F W L D hZ hY hF hqN hgeom hfibre
  have hs := sum_le_sum (s := omega3SieveModuli N D Z) (fun q hq =>
    mul_le_mul_of_nonneg_left
      (gamma16_family_missing_le (δ := δ) W L hY hF (omega3SieveModuli_properties hq).1
        (hqN q hq) hgeom hfibre)
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

end Wu2008DoubleSieve