import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledPhysicalSieve
import MathlibNt.Wu2008DoubleSieve.Omega3NonCoprimeRelative

/-! Original-weight cofactor multiplicities pay only the additive missing mass. -/
namespace Wu2008DoubleSieve.LabelledPhysical.Family
open Finset Real
open scoped Classical
universe u
variable {α : Type u} {N : ℕ} (L : Family α N)

theorem cofactor_le {c : α} (hc : c ∈ L.labels) : L.cofactor c ≤ N := by
  have h := L.geometry c hc
  have hA : (0 : ℝ) ≤ L.cofactor c := Nat.cast_nonneg _
  have hb : 1 ≤ L.upper c := by linarith [h.2.1, h.2.2.1]
  exact_mod_cast (le_mul_of_one_le_right hA hb).trans h.2.2.2

/-- The true interval cardinality, including empty fibres, is bounded by N/A. -/
theorem primes_card_le {c : α} (hc : c ∈ L.labels) :
    ((L.primes c).card : ℝ) ≤ (N : ℝ) / L.cofactor c := by
  have hsub : L.primes c ⊆ Icc 1 (N / L.cofactor c) := by
    intro p hp
    have hprime := (mem_filter.mp hp).2.1
    exact mem_Icc.mpr ⟨hprime.one_lt.le,
      (Nat.le_div_iff_mul_le (L.geometry c hc).1).mpr (by simpa only [mul_comm] using L.output_le hc hp)⟩
  have hcard : (L.primes c).card ≤ N / L.cofactor c := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  exact (show ((L.primes c).card : ℝ) ≤ (N / L.cofactor c : ℕ) by exact_mod_cast hcard).trans Nat.cast_div_le

/-- Grouping by the actual cofactor retains every original weighted label. -/
theorem missing_le_reciprocal {F : ℝ} (q : ℕ)
    (hfibre : ∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) :
    L.missing q ≤ F * N *
      ∑ e ∈ (L.labels.image L.cofactor).filter (fun e => ¬e.Coprime q), 1 / (e : ℝ) := by
  let E := L.labels.image L.cofactor
  have hinner (e : ℕ) :
      (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
        L.weight c * (if ¬(L.cofactor c).Coprime q then ((L.primes c).card : ℝ) else 0)) ≤
        if ¬e.Coprime q then F * N * (1 / (e : ℝ)) else 0 := by
    by_cases hb : ¬e.Coprime q
    · rw [if_pos hb]
      calc
        _ ≤ ∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
            L.weight c * ((N : ℝ) / e) := by
          apply sum_le_sum
          intro c hc
          obtain ⟨hc, he⟩ := mem_filter.mp hc
          rw [he, if_pos hb]
          apply mul_le_mul_of_nonneg_left _ (L.weight_nonneg c hc)
          simpa only [he] using L.primes_card_le hc
        _ = (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) * ((N : ℝ) / e) :=
          (sum_mul ..).symm
        _ ≤ F * ((N : ℝ) / e) := mul_le_mul_of_nonneg_right (hfibre e) (by positivity)
        _ = _ := by ring
    · rw [if_neg hb]
      apply le_of_eq
      apply sum_eq_zero
      intro c hc
      rw [(mem_filter.mp hc).2, if_neg hb, mul_zero]
  calc
    _ = ∑ c ∈ L.labels, L.weight c *
        (if ¬(L.cofactor c).Coprime q then ((L.primes c).card : ℝ) else 0) := by
      simp only [missing, sum_filter, mul_ite, mul_zero]
    _ = ∑ e ∈ E, ∑ c ∈ L.labels.filter (fun c => L.cofactor c = e),
        L.weight c * (if ¬(L.cofactor c).Coprime q then ((L.primes c).card : ℝ) else 0) :=
      (sum_fiberwise_of_maps_to (fun _ hc => mem_image_of_mem _ hc) _).symm
    _ ≤ ∑ e ∈ E, if ¬e.Coprime q then F * N * (1 / (e : ℝ)) else 0 :=
      sum_le_sum (fun e _ => hinner e)
    _ = _ := by
      rw [sum_filter, mul_sum]
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring

theorem missing_le {q : ℕ} {Y F : ℝ} (hY : 0 < Y) (hF : 0 ≤ F)
    (hq : 0 < q) (hqN : q ≤ N)
    (hrough : ∀ c ∈ L.labels, ∀ p, p.Prime → p ∣ L.cofactor c → Y ≤ (p : ℝ))
    (hfibre : ∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) :
    L.missing q ≤ F * N * ((1 + log N) * log N / (Y * log 2)) := by
  let E := L.labels.image L.cofactor
  have hE : ∀ e ∈ E, 0 < e ∧ e ≤ N := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨(L.geometry c hc).1, L.cofactor_le hc⟩
  have hEr : ∀ e ∈ E, ∀ p, p.Prime → p ∣ e → Y ≤ (p : ℝ) := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact hrough c hc
  exact (L.missing_le_reciprocal q hfibre).trans (mul_le_mul_of_nonneg_left
    (omega3_rough_non_coprime_reciprocal_le N q E hY hq hqN hE hEr) (by positivity))

/-- One Euler constant works for every label type, geometry and original weight. -/
theorem R2_euler :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N →
      ∀ (α : Type u) (L : Family α N) (D : ℕ) (Z Y F : ℝ),
      Z ≤ N → 0 < Y → 0 ≤ F →
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      (∀ c ∈ L.labels, ∀ p, p.Prime → p ∣ L.cofactor c → Y ≤ (p : ℝ)) →
      (∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) →
      L.R2 D Z ≤ C * F * N * ((1 + log N) * log N ^ 4 / (Y * log 2)) := by
  obtain ⟨C, hC, hmass⟩ := omega3_sieve_euler_mass
  refine ⟨C, hC, ?_⟩
  intro N hN α L D Z Y F hZ hY hF hqN hrough hfibre
  have hs := sum_le_sum (s := omega3SieveModuli N D Z) (fun q hq =>
    mul_le_mul_of_nonneg_left
      (L.missing_le hY hF (omega3SieveModuli_properties hq).1 (hqN q hq) hrough hfibre)
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

/-- Composed finite prime endpoint: F occurs in the additive error, never in X. -/
theorem prime_upper_euler :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N → Even N →
      ∀ (α : Type u) (L : Family α N) (D : ℕ) (Z Y F : ℝ),
      1 < D → Z ≤ (D : ℝ) → Z ≤ N → 0 < Y → 0 ≤ F →
      (∀ q ∈ omega3SieveModuli N D Z, q ≤ N) →
      (∀ c ∈ L.labels, ∀ p, p.Prime → p ∣ L.cofactor c → Y ≤ (p : ℝ)) →
      (∀ e, (∑ c ∈ L.labels.filter (fun c => L.cofactor c = e), L.weight c) ≤ F) →
      L.primeMass ≤ L.mass * ordinaryRosserMainSum true N 1 D Z + L.R1 D Z +
        C * F * N * ((1 + log N) * log N ^ 4 / (Y * log 2)) + L.small Z := by
  obtain ⟨C, hC, hR2⟩ := R2_euler.{u}
  refine ⟨C, hC, ?_⟩
  intro N hN he α L D Z Y F hD hZD hZN hY hF hqN hrough hfibre
  have h := L.prime_upper_finite he D Z hD hZD
  have h2 := hR2 N hN α L D Z Y F hZN hY hF hqN hrough hfibre
  linarith

end Wu2008DoubleSieve.LabelledPhysical.Family
