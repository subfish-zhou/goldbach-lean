import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothMainTerm
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import Mathlib.Data.Finset.NatDivisors

/-!
# Global bounds for the actual smooth U and V error terms

These bounds apply to arbitrary signed coefficients of fixed divisor order,
arbitrary subsets of the real-endpoint supports, and every integer residue.
No well-factorability, squarefree support, or error estimate is assumed.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

/-- Submultiplicativity of the ordinary divisor count, without coprimality. -/
theorem card_divisors_mul_le (q r : ℕ) :
    (q * r).divisors.card ≤ q.divisors.card * r.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

/-- A signed fixed-order sequence has the elementary global absolute mean. -/
theorem sum_abs_le_fouvryTau_mean {k : ℕ} (hk : 1 ≤ k)
    {T : ℝ} (hT : 1 ≤ T) (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊)
    (β : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) :
    (∑ n ∈ N, |β n|) ≤ T * (1 + Real.log T) ^ (k - 1) := by
  calc
    _ ≤ ∑ n ∈ N, (fouvryTau k n : ℝ) := sum_le_sum hβ
    _ ≤ ∑ n ∈ Ioc 0 ⌊T⌋₊, (fouvryTau k n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := sum_fouvryTau_le_real hk hT

theorem coprimeMass_abs_le_sum_abs (N : Finset ℕ) (β : ℕ → ℝ) (q : ℕ) :
    |coprimeMass N β q| ≤ ∑ n ∈ N, |β n| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n _
  split_ifs <;> simp

theorem coprimeMass_of_abs_le_sum_abs (N : Finset ℕ) (β : ℕ → ℝ) (q : ℕ) :
    coprimeMass N (fun n => |β n|) q ≤ ∑ n ∈ N, |β n| := by
  apply sum_le_sum
  intro n _
  split_ifs <;> simp

/-- The exact modulus weight appearing after divisor-count submultiplicativity
has a global logarithmic mean, uniform in the changing residue. -/
theorem sum_reduced_abs_mul_card_divisors_div_totient_le
    (j : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (c : ℕ → ℝ) (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    (∑ q ∈ reducedModuli Q a,
      |c q| * (q.divisors.card : ℝ) / q.totient) ≤ (1 + Real.log L) ^ (4 * j) := by
  calc
    _ ≤ ∑ q ∈ reducedModuli Q a, (fouvryTau (2 * j) q : ℝ) / q.totient := by
      apply sum_le_sum
      intro q hq
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc
        _ ≤ (fouvryTau j q : ℝ) * fouvryTau 2 q := by
          rw [fouvryTau_two]
          exact mul_le_mul_of_nonneg_right (hc q (mem_filter.mp hq).1) (Nat.cast_nonneg _)
        _ ≤ _ := by
          exact_mod_cast (by simpa [Nat.mul_comm] using fouvryTau_mul_le j 2 q)
    _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau (2 * j) q : ℝ) / q.totient :=
      sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hQ)
        (fun _ _ _ => by positivity)
    _ ≤ _ := by
      simpa only [← Nat.mul_assoc, show 2 * 2 = 4 from rfl] using
        sum_fouvryTau_div_totient_le_real (2 * j) hL

/-- The actual U envelope has only logarithmic dependence on the modulus
endpoint, and retains arbitrary fixed beta and modulus divisor orders. -/
theorem smoothUErrorEnvelope_le_fouvryTau
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {T L : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L)
    (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    smoothUErrorEnvelope N Q β c a ≤
      (T * (1 + Real.log T) ^ (k - 1)) ^ 2 * (1 + Real.log L) ^ (8 * j) := by
  let B := T * (1 + Real.log T) ^ (k - 1)
  let w := fun q : ℕ => |c q| * (q.divisors.card : ℝ) / q.totient
  have hlogT := Real.log_nonneg hT
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw : ∀ q, 0 ≤ w q := fun q => by dsimp [w]; positivity
  have hmass : ∀ q, |coprimeMass N β q| ≤ B := fun q =>
    (coprimeMass_abs_le_sum_abs N β q).trans (sum_abs_le_fouvryTau_mean hk hT N hN β hβ)
  calc
    _ ≤ ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a, B ^ 2 * (w q * w r) := by
      apply sum_le_sum
      intro q _
      apply sum_le_sum
      intro r _
      have hd : ((q * r).divisors.card : ℝ) ≤
          (q.divisors.card : ℝ) * r.divisors.card := by
        exact_mod_cast card_divisors_mul_le q r
      calc
        _ ≤ (|c q| * |c r| / ((q.totient : ℝ) * r.totient) * B * B) *
            ((q.divisors.card : ℝ) * r.divisors.card) := by
          simp only [uModulusCoefficient, abs_mul, abs_div, Nat.abs_cast]
          gcongr
          · exact hmass q
          · exact hmass r
        _ = _ := by dsimp [w]; ring
    _ = B ^ 2 * (∑ q ∈ reducedModuli Q a, w q) ^ 2 := by
      rw [pow_two (∑ q ∈ reducedModuli Q a, w q), sum_mul_sum]
      simp only [mul_sum]
    _ ≤ B ^ 2 * ((1 + Real.log L) ^ (4 * j)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact pow_le_pow_left₀ (sum_nonneg (fun q _ => hw q))
        (sum_reduced_abs_mul_card_divisors_div_totient_le j hL Q hQ c hc a) 2
    _ = _ := by rw [← pow_mul]; congr 2; omega

/-- The actual V envelope costs one power of the modulus endpoint, not two. -/
theorem smoothVErrorEnvelope_le_fouvryTau
    {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) {T L : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L)
    (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    smoothVErrorEnvelope N Q β c a ≤
      (T * (1 + Real.log T) ^ (k - 1)) ^ 2 * L *
        (1 + Real.log L) ^ (5 * j - 1) := by
  let B := T * (1 + Real.log T) ^ (k - 1)
  let w := fun q : ℕ => |c q| * (q.divisors.card : ℝ) / q.totient
  have hlogT := Real.log_nonneg hT
  have hlogL := Real.log_nonneg hL
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw : ∀ q, 0 ≤ w q := fun q => by dsimp [w]; positivity
  have hmass : ∀ q, |coprimeMass N β q| ≤ B := fun q =>
    (coprimeMass_abs_le_sum_abs N β q).trans (sum_abs_le_fouvryTau_mean hk hT N hN β hβ)
  have habs : ∀ q, coprimeMass N (fun n => |β n|) q ≤ B := fun q =>
    (coprimeMass_of_abs_le_sum_abs N β q).trans (sum_abs_le_fouvryTau_mean hk hT N hN β hβ)
  calc
    _ ≤ ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a, B ^ 2 * (|c q| * w r) := by
      apply sum_le_sum
      intro q _
      apply sum_le_sum
      intro r _
      calc
        _ ≤ (|c q| * |c r| / (r.totient : ℝ) * B) * B * (r.divisors.card : ℝ) := by
          simp only [vModulusCoefficient, abs_mul, abs_div, Nat.abs_cast]
          gcongr
          · exact sum_nonneg (fun n _ => by split_ifs <;> positivity)
          · exact hmass r
          · exact habs q
        _ = _ := by dsimp [w]; ring
    _ = B ^ 2 * (∑ q ∈ reducedModuli Q a, |c q|) * (∑ r ∈ reducedModuli Q a, w r) := by
      rw [mul_assoc, sum_mul_sum]
      simp only [mul_sum]
    _ ≤ B ^ 2 * (L * (1 + Real.log L) ^ (j - 1)) *
        (1 + Real.log L) ^ (4 * j) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact sum_abs_le_fouvryTau_mean hj hL _ ((filter_subset _ _).trans hQ) c
          (fun q hq => hc q (mem_filter.mp hq).1)
      · exact sum_reduced_abs_mul_card_divisors_div_totient_le j hL Q hQ c hc a
      · exact sum_nonneg (fun r _ => hw r)
      · positivity
    _ = _ := by
      rw [show 5 * j - 1 = (j - 1) + 4 * j by omega, pow_add]
      ring

/-- A global bound for the signed U error itself, with a constant chosen
before all changing arithmetic data and both fixed divisor orders. -/
theorem dispersionU_smooth_fouvryTau_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, ∀ T L : ℝ, 1 ≤ T → 1 ≤ L →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      |dispersionU S N Q (fun m => scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤
        C * ((T * (1 + Real.log T) ^ (k - 1)) ^ 2 * (1 + Real.log L) ^ (8 * j)) := by
  obtain ⟨C, hC, h⟩ := dispersionU_smooth_uniform_error
  refine ⟨C, hC, fun M hM S hS k hk j T L hT hL N Q hN hQ β c hβ hc a => ?_⟩
  exact (h M hM S hS N Q β c a
    (fun q hq => (mem_Ioc.mp (hQ hq)).1.ne')).trans
    (mul_le_mul_of_nonneg_left
      (smoothUErrorEnvelope_le_fouvryTau hk j hT hL N Q hN hQ β c hβ hc a) hC.le)

/-- A global bound for the signed V error itself; no error-envelope premise
is left to the consumer. -/
theorem dispersionV_smooth_fouvryTau_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ k j : ℕ, 1 ≤ k → 1 ≤ j → ∀ T L : ℝ, 1 ≤ T → 1 ≤ L →
      ∀ N Q : Finset ℕ, N ⊆ Ioc 0 ⌊T⌋₊ → Q ⊆ Ioc 0 ⌊L⌋₊ →
      ∀ β c : ℕ → ℝ, (∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) →
      (∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) → ∀ a : ℤ,
      |dispersionV S N Q (fun m => scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤
        C * ((T * (1 + Real.log T) ^ (k - 1)) ^ 2 * L *
          (1 + Real.log L) ^ (5 * j - 1)) := by
  obtain ⟨C, hC, h⟩ := dispersionV_smooth_uniform_error
  refine ⟨C, hC, fun M hM S hS k j hk hj T L hT hL N Q hN hQ β c hβ hc a => ?_⟩
  exact (h M hM S hS N Q β c a
    (fun q hq => (mem_Ioc.mp (hQ hq)).1.ne')).trans
    (mul_le_mul_of_nonneg_left
      (smoothVErrorEnvelope_le_fouvryTau hk hj hT hL N Q hN hQ β c hβ hc a) hC.le)

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
