

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIEnergy

/-!
 # Vaughan's small range and all-character bookkeeping

This module closes the finite small-range lane left by the structured Vaughan
ledgers.  It also records the exact, purely finite interfaces needed to pass
from conductor-level primitive characters to all characters.  No prime-number
theorem or Bombieri--Vinogradov conclusion is stated or used.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The literal support of the small Vaughan coefficient inside `[1,N]`. -/
def vaughanSmallSupport (N v : ℕ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) N).filter (fun n => n.toNat ≤ v)

@[simp]
theorem mem_vaughanSmallSupport {N v : ℕ} {n : ℤ} :
    n ∈ vaughanSmallSupport N v ↔ 1 ≤ n ∧ n ≤ N ∧ n.toNat ≤ v := by
  simp [vaughanSmallSupport, and_assoc]

/-- The small coefficient vanishes off its literal `n.toNat ≤ v` support. -/
theorem vaughanSmallCoeff_eq_zero_of_v_lt_toNat
    (b : ℤ → ℂ) (v : ℕ) {n : ℤ} (hn : v < n.toNat) :
    vaughanSmallCoeff b v n = 0 := by
  simp [vaughanSmallCoeff, vaughanSmall, not_le.mpr hn]

/-- On its support, the small coefficient is exactly `b(n) Λ(n)`. -/
theorem vaughanSmallCoeff_eq_of_toNat_le
    (b : ℤ → ℂ) (v : ℕ) {n : ℤ} (hn : n.toNat ≤ v) :
    vaughanSmallCoeff b v n =
      b n * (ArithmeticFunction.vonMangoldt n.toNat : ℂ) := by
  simp [vaughanSmallCoeff, vaughanSmall, hn]

/-- There are at most `v` positive integers in the small support. -/
theorem card_vaughanSmallSupport_le (N v : ℕ) :
    (vaughanSmallSupport N v).card ≤ v := by
  have hsub : vaughanSmallSupport N v ⊆ Finset.Icc (1 : ℤ) (v : ℤ) := by
    intro n hn
    rw [mem_vaughanSmallSupport] at hn
    rw [Finset.mem_Icc]
    refine ⟨hn.1, ?_⟩
    have hn0 : 0 ≤ n := by omega
    rw [← Int.toNat_of_nonneg hn0]
    exact_mod_cast hn.2.2
  calc
    (vaughanSmallSupport N v).card ≤ (Finset.Icc (1 : ℤ) (v : ℤ)).card :=
      Finset.card_le_card hsub
    _ = v := by simp

/-- Exact finite energy identity: all terms outside the literal small support
are zero, and no estimate has yet been applied. -/
theorem vaughanSmallCoeff_energy_eq_support (b : ℤ → ℂ) (N v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) =
      ∑ n ∈ vaughanSmallSupport N v,
        ‖b n‖ ^ 2 * ArithmeticFunction.vonMangoldt n.toNat ^ 2 := by
  calc
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) =
        ∑ n ∈ Finset.Icc (1 : ℤ) N,
          if n.toNat ≤ v then
            ‖b n‖ ^ 2 * ArithmeticFunction.vonMangoldt n.toNat ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnv : n.toNat ≤ v
      · rw [if_pos hnv, vaughanSmallCoeff_eq_of_toNat_le b v hnv,
          norm_mul, mul_pow]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      · rw [if_neg hnv, vaughanSmallCoeff_eq_zero_of_v_lt_toNat b v
          (Nat.lt_of_not_ge hnv)]
        simp
    _ = _ := by
      rw [← Finset.sum_filter]
      rfl

private theorem vonMangoldt_le_log_v_succ {n : ℤ} {v : ℕ}
    (hn : 1 ≤ n) (hnv : n.toNat ≤ v) :
    ArithmeticFunction.vonMangoldt n.toNat ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
  have hn0 : 0 ≤ n := by omega
  have hnpos : (0 : ℝ) < n.toNat := by
    have : 0 < n.toNat := by omega
    exact_mod_cast this
  have hnv' : (n.toNat : ℝ) ≤ ((v + 1 : ℕ) : ℝ) := by
    exact_mod_cast (hnv.trans (Nat.le_succ v))
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.strictMonoOn_log.monotoneOn (by simpa using hnpos)
      (by simp only [Set.mem_Ioi]; positivity) hnv')

/-- Weighted small-lane energy estimate with the exact support and the explicit
`log(v+1)^2` loss. -/
theorem vaughanSmallCoeff_energy_le_log_support (b : ℤ → ℂ) (N v : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) ≤
      Real.log ((v + 1 : ℕ) : ℝ) ^ 2 *
        ∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2 := by
  rw [vaughanSmallCoeff_energy_eq_support, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [mem_vaughanSmallSupport] at hn
  have hΛ := vonMangoldt_le_log_v_succ hn.1 hn.2.2
  have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
  have hlog0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le v))
  have hsq : ArithmeticFunction.vonMangoldt n.toNat ^ 2 ≤
      Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  nlinarith [sq_nonneg ‖b n‖]

/-- Uniform-coefficient form of the small-lane producer.  Both the support
length `v` and the logarithmic loss are explicit. -/
theorem vaughanSmallCoeff_energy_le_v_mul_log_sq
    (b : ℤ → ℂ) (N v : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ vaughanSmallSupport N v, ‖b n‖ ≤ B) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, ‖vaughanSmallCoeff b v n‖ ^ 2) ≤
      (v : ℝ) * B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by
  rw [vaughanSmallCoeff_energy_eq_support]
  have hlog0 : 0 ≤ Real.log ((v + 1 : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le v))
  calc
    (∑ n ∈ vaughanSmallSupport N v,
        ‖b n‖ ^ 2 * ArithmeticFunction.vonMangoldt n.toNat ^ 2) ≤
        ∑ _n ∈ vaughanSmallSupport N v,
          B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mem_vaughanSmallSupport] at hn
      have hb' := hb n (mem_vaughanSmallSupport.mpr hn)
      have hΛ := vonMangoldt_le_log_v_succ hn.1 hn.2.2
      have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n.toNat)
      have hbSq : ‖b n‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg (b n)]
      have hΛSq : ArithmeticFunction.vonMangoldt n.toNat ^ 2 ≤
          Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      exact (mul_le_mul_of_nonneg_right hbSq (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hΛSq (sq_nonneg B))
    _ = ((vaughanSmallSupport N v).card : ℝ) * B ^ 2 *
        Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by
      simp
      ring
    _ ≤ (v : ℝ) * B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2 := by
      have hcard : ((vaughanSmallSupport N v).card : ℝ) ≤ v := by
        exact_mod_cast card_vaughanSmallSupport_le N v
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (sq_nonneg B)) (sq_nonneg _)

/-- The existing Vaughan prefix ledger with its final opaque lane replaced by
the proved small-support energy.  This remains a coefficient-energy ledger,
not a Bombieri--Vinogradov conclusion. -/
theorem weighted_vaughan_prefix_large_sieve_small_closed_ledger
    (b : ℤ → ℂ) (N Q u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanLambdaCoeff b) 0 N q χ) ≤
      3 * (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
        ((∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeICutoffEnergy n.toNat u v) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeIIDivisorEnergy n.toNat u v) +
          Real.log ((v + 1 : ℕ) : ℝ) ^ 2 *
            ∑ n ∈ vaughanSmallSupport N v, ‖b n‖ ^ 2) := by
  refine (weighted_vaughan_prefix_large_sieve_structured_ledger
    b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · gcongr
    exact vaughanSmallCoeff_energy_le_log_support b N v
  · unfold primitiveLargeSieveConstant
    positivity

/-- Uniform-coefficient specialization of the closed small lane, displaying
the exact `v · B² · log(v+1)²` budget. -/
theorem weighted_vaughan_prefix_large_sieve_small_closed_uniform_ledger
    (b : ℤ → ℂ) (N Q u v : ℕ) (B : ℝ) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hb : ∀ n ∈ vaughanSmallSupport N v, ‖b n‖ ≤ B) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare (vaughanLambdaCoeff b) 0 N q χ) ≤
      3 * (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
        ((∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeICutoffEnergy n.toNat u v) +
          (∑ n ∈ Finset.Icc (1 : ℤ) N,
            ‖b n‖ ^ 2 * vaughanTypeIIDivisorEnergy n.toNat u v) +
          (v : ℝ) * B ^ 2 * Real.log ((v + 1 : ℕ) : ℝ) ^ 2) := by
  refine (weighted_vaughan_prefix_large_sieve_structured_ledger
    b N Q u v hQ).trans ?_
  apply mul_le_mul_of_nonneg_left
  · gcongr
    exact vaughanSmallCoeff_energy_le_v_mul_log_sq b N v B hB hb
  · unfold primitiveLargeSieveConstant
    positivity

/-! ## Exact conductor and principal-character bookkeeping -/

/-- The nonprincipal characters at level `q`, as a concrete finite set. -/
noncomputable def nonprincipalCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.erase 1

@[simp]
theorem mem_nonprincipalCharacters {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ nonprincipalCharacters q ↔ χ ≠ 1 := by
  simp [nonprincipalCharacters]

/-- Exact finite principal/nonprincipal decomposition.  This is the interface
at which a main term must be split off before any nonprincipal estimate is
applied. -/
theorem sum_allCharacters_eq_principal_add_nonprincipal
    {q : ℕ} {A : Type*} [AddCommMonoid A]
    (F : DirichletCharacter ℂ q → A) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      F 1 + ∑ χ ∈ nonprincipalCharacters q, F χ := by
  exact (Finset.add_sum_erase Finset.univ F
    (Finset.mem_univ (1 : DirichletCharacter ℂ q))).symm

/-- For nonzero level, nonprincipality is equivalently conductor different
from one. -/
theorem mem_nonprincipalCharacters_iff_conductor_ne_one
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} :
    χ ∈ nonprincipalCharacters q ↔ χ.conductor ≠ 1 := by
  rw [mem_nonprincipalCharacters]
  exact not_congr DirichletCharacter.eq_one_iff_conductor_eq_one

/-- The explicit error made when replacing a level-`q` character by its
primitive character at the conductor. -/
def conductorChangeLevelError {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  b n * χ (n : ZMod q) -
    b n * χ.primitiveCharacter (n : ZMod χ.conductor)

/-- The conductor-change error is supported only on integers not coprime to the
original level. -/
theorem conductorChangeLevelError_eq_zero_of_isCoprime
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) {n : ℤ}
    (hn : IsCoprime n q) :
    conductorChangeLevelError χ b n = 0 := by
  unfold conductorChangeLevelError
  rw [χ.primitiveCharacter_apply_of_isCoprime hn]
  ring

/-- Pointwise exact recovery of an arbitrary character term from the
conductor-level primitive term plus its explicit bad-prime correction. -/
theorem characterTerm_eq_conductorPrimitive_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (n : ℤ) :
    b n * χ (n : ZMod q) =
      b n * χ.primitiveCharacter (n : ZMod χ.conductor) +
        conductorChangeLevelError χ b n := by
  unfold conductorChangeLevelError
  ring

/-- Finite interval form of conductor/change-level recovery.  A primitive
character estimate controls the first sum; the second sum is an explicit
correction supported on `¬ IsCoprime n q`. -/
theorem characterInterval_eq_conductorPrimitive_add_error
    {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ (n : ZMod q)) =
      (∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * χ.primitiveCharacter (n : ZMod χ.conductor)) +
      ∑ n ∈ Finset.Icc (M + 1) (M + N),
        conductorChangeLevelError χ b n := by
  calc
    _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (b n * χ.primitiveCharacter (n : ZMod χ.conductor) +
            conductorChangeLevelError χ b n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact characterTerm_eq_conductorPrimitive_add_error χ b n
    _ = _ := by rw [Finset.sum_add_distrib]

/-- The principal contribution is the literal `χ = 1` summand; every remaining
summand has nontrivial conductor.  This is a finite identity, not a PNT main-term
asymptotic. -/
theorem sum_characterIntervals_eq_principal_add_nonprincipal
    (q : ℕ) (b : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ (n : ZMod q)) =
      (∑ n ∈ Finset.Icc (M + 1) (M + N),
        b n * (1 : DirichletCharacter ℂ q) (n : ZMod q)) +
      ∑ χ ∈ nonprincipalCharacters q,
        ∑ n ∈ Finset.Icc (M + 1) (M + N), b n * χ (n : ZMod q) := by
  exact sum_allCharacters_eq_principal_add_nonprincipal _

end

end AnalyticNumberTheory.LargeSieve
