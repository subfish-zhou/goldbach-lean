import MathlibNt.AnalyticNumberTheory.LargeSieve.HighConductorDyadicPrimitive
import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal

/-!
# Actual high-conductor Type-II ledger on one canonical shell

The outer row lies in `[2^k,2^(k+1))`; the collected inner coefficient is
cut off by the physical condition `r*t ≤ N`.  Thus every row has the common
short length `N / 2^k`.  The theorem below applies the canonical prefix-maximal
primitive large sieve row by row and keeps the conductor range `R < d ≤ Q`.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- Canonical outer Type-II shell. -/
def vaughanTypeIIFixedShell (k : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ k) (2 ^ (k + 1))

/-- Common inner length forced by the closed lower endpoint of the shell. -/
def vaughanTypeIIFixedShellLength (N k : ℕ) : ℕ := N / 2 ^ k

/-- One actual collected row, including its physical product cutoff. -/
def vaughanTypeIICollectedRowCoefficient
    (N r : ℕ) (c : ℕ → ℕ → ℂ) (t : ℤ) : ℂ :=
  if _ht : 0 < t then
    if r * t.toNat ≤ N then c r t.toNat else 0
  else 0

/-- Outer coefficient energy on the actual shell. -/
def vaughanTypeIIFixedShellOuterEnergy
    (k : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ r ∈ vaughanTypeIIFixedShell k, ‖a r‖ ^ 2

/-- Summed energy of all physically collected rows at the canonical short
length. -/
def vaughanTypeIIFixedShellTensorEnergy
    (N k : ℕ) (c : ℕ → ℕ → ℂ) : ℝ :=
  ∑ r ∈ vaughanTypeIIFixedShell k,
    ∑ t ∈ Finset.Icc (1 : ℤ) (vaughanTypeIIFixedShellLength N k),
      ‖vaughanTypeIICollectedRowCoefficient N r c t‖ ^ 2

/-- The actual fixed-shell Type-II square for one character and one prefix. -/
def vaughanTypeIIFixedShellPrefixSquare
    (N k y d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  ‖∑ r ∈ vaughanTypeIIFixedShell k,
      a r * ∑ t ∈ Finset.Icc (1 : ℤ) (y : ℤ),
        vaughanTypeIICollectedRowCoefficient N r c t * χ.1 (t : ZMod d)‖ ^ 2

/-- The literal maximum over all prefixes of the canonical short row. -/
def vaughanTypeIIFixedShellPrefixMaxSquare
    (N k d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  ((Finset.range (vaughanTypeIIFixedShellLength N k + 1)).image
    (fun y => vaughanTypeIIFixedShellPrefixSquare N k y d a c χ)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- AP-normalized amplitude of the actual shell. -/
def highConductorVaughanTypeIIFixedShellAmplitude
    (N k d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  Real.sqrt (vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ)

private theorem highConductor_subset_full {R Q : ℕ} :
    Finset.Ioc R Q ⊆ Finset.Icc 1 Q := by
  intro d hd
  simp only [Finset.mem_Ioc, Finset.mem_Icc] at hd ⊢
  omega

/-- The physical cutoff and shell lower endpoint force support in the common
short interval. -/
theorem vaughanTypeIICollectedRowCoefficient_eq_zero_of_length_lt
    {N k r t : ℕ} {c : ℕ → ℕ → ℂ}
    (hr : r ∈ vaughanTypeIIFixedShell k)
    (ht : vaughanTypeIIFixedShellLength N k < t) :
    vaughanTypeIICollectedRowCoefficient N r c (t : ℤ) = 0 := by
  unfold vaughanTypeIICollectedRowCoefficient
  by_cases ht0 : t = 0
  · subst t
    simp
  · rw [dif_pos (by exact_mod_cast Nat.pos_of_ne_zero ht0)]
    simp only [Int.toNat_natCast]
    rw [if_neg]
    intro hprod
    have hrlo : 2 ^ k ≤ r := (Finset.mem_Ico.mp hr).1
    have hp : 0 < 2 ^ k := pow_pos (by norm_num : 0 < (2 : ℕ)) k
    have hpowprod : 2 ^ k * t ≤ N :=
      (Nat.mul_le_mul_right t hrlo).trans hprod
    have htle : t ≤ N / 2 ^ k :=
      (Nat.le_div_iff_mul_le hp).2 (by simpa [mul_comm] using hpowprod)
    exact (not_le_of_gt ht) htle

private theorem norm_sum_mul_sq_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a z : ι → ℂ) :
    ‖∑ i ∈ s, a i * z i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * (∑ i ∈ s, ‖z i‖ ^ 2) := by
  exact finiteComplexCauchy s a z

/-- Row Cauchy for the literal collected shell, with each row controlled by its
own complete canonical prefix maximum. -/
theorem vaughanTypeIIFixedShellPrefixMaxSquare_le_rowLedger
    (N k d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ ≤
      vaughanTypeIIFixedShellOuterEnergy k a *
        ∑ r ∈ vaughanTypeIIFixedShell k,
          primitiveCharacterPrefixMaxSquare
            (vaughanTypeIICollectedRowCoefficient N r c) 0
            (vaughanTypeIIFixedShellLength N k) d χ := by
  unfold vaughanTypeIIFixedShellPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyL : y ≤ vaughanTypeIIFixedShellLength N k := by
    simpa [Finset.mem_range] using hy
  unfold vaughanTypeIIFixedShellPrefixSquare
  let z : ℕ → ℂ := fun r =>
    ∑ t ∈ Finset.Icc (1 : ℤ) (y : ℤ),
      vaughanTypeIICollectedRowCoefficient N r c t * χ.1 (t : ZMod d)
  calc
    ‖∑ r ∈ vaughanTypeIIFixedShell k, a r * z r‖ ^ 2 ≤
        (∑ r ∈ vaughanTypeIIFixedShell k, ‖a r‖ ^ 2) *
          ∑ r ∈ vaughanTypeIIFixedShell k, ‖z r‖ ^ 2 :=
      norm_sum_mul_sq_le (vaughanTypeIIFixedShell k) a z
    _ ≤ (∑ r ∈ vaughanTypeIIFixedShell k, ‖a r‖ ^ 2) *
          ∑ r ∈ vaughanTypeIIFixedShell k,
            primitiveCharacterPrefixMaxSquare
              (vaughanTypeIICollectedRowCoefficient N r c) 0
              (vaughanTypeIIFixedShellLength N k) d χ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro r hr
        simpa [z, primitiveCharacterPrefixSquare] using
          primitiveCharacterPrefixSquare_le_max
            (vaughanTypeIICollectedRowCoefficient N r c) 0 hyL χ
      · positivity
    _ = _ := rfl

/-- **Actual collected-shell Type-II square ledger.**  Primitive conductors stay
in `R < d ≤ Q`; row Cauchy is followed by the canonical row-prefix tensor large
sieve at the physically shortened length `N / 2^k`.  No
`HighConductorTypeIISquareSaving` premise occurs. -/
theorem highConductorVaughanTypeIIFixedShell_squareLedger_le
    (R Q N k : ℕ) (hQ : 0 < Q)
    (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ) :
    highConductorPrimitiveSquareLedger R Q
        (fun d => highConductorVaughanTypeIIFixedShellAmplitude N k d a c) ≤
      (((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q *
        (vaughanTypeIIFixedShellOuterEnergy k a *
          vaughanTypeIIFixedShellTensorEnergy N k c) := by
  let L := vaughanTypeIIFixedShellLength N k
  unfold highConductorPrimitiveSquareLedger
  calc
    (∑ d ∈ Finset.Ioc R Q, ((d : ℝ) / d.totient) *
        ∑ χ : PrimitiveCharacter d,
          highConductorVaughanTypeIIFixedShellAmplitude N k d a c χ ^ 2) ≤
      ∑ d ∈ Finset.Ioc R Q, ((d : ℝ) / d.totient) *
        ∑ χ : PrimitiveCharacter d,
          vaughanTypeIIFixedShellOuterEnergy k a *
            ∑ r ∈ vaughanTypeIIFixedShell k,
              primitiveCharacterPrefixMaxSquare
                (vaughanTypeIICollectedRowCoefficient N r c) 0 L d χ := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro χ hχ
        rw [highConductorVaughanTypeIIFixedShellAmplitude,
          Real.sq_sqrt]
        · exact vaughanTypeIIFixedShellPrefixMaxSquare_le_rowLedger N k d a c χ
        · unfold vaughanTypeIIFixedShellPrefixMaxSquare
          apply Finset.le_max'
          exact Finset.mem_image.mpr ⟨0, by simp,
            by simp [vaughanTypeIIFixedShellPrefixSquare]⟩
      · positivity
    _ ≤ vaughanTypeIIFixedShellOuterEnergy k a *
        ∑ r ∈ vaughanTypeIIFixedShell k,
          ∑ d ∈ Finset.Icc 1 Q, ((d : ℝ) / d.totient) *
            ∑ χ : PrimitiveCharacter d,
              primitiveCharacterPrefixMaxSquare
                (vaughanTypeIICollectedRowCoefficient N r c) 0 L d χ := by
      calc
        _ = vaughanTypeIIFixedShellOuterEnergy k a *
            ∑ r ∈ vaughanTypeIIFixedShell k,
              ∑ d ∈ Finset.Ioc R Q, ((d : ℝ) / d.totient) *
                ∑ χ : PrimitiveCharacter d,
                  primitiveCharacterPrefixMaxSquare
                    (vaughanTypeIICollectedRowCoefficient N r c) 0 L d χ := by
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro d hd
              rw [Finset.sum_comm]
              ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro r hr
            apply Finset.sum_le_sum_of_subset_of_nonneg highConductor_subset_full
            intro d hd hnot
            exact mul_nonneg (by positivity)
              (Finset.sum_nonneg fun χ hχ =>
                primitiveCharacterPrefixMaxSquare_nonneg _ _ _ _ χ)
          · exact Finset.sum_nonneg fun r hr => sq_nonneg ‖a r‖
    _ ≤ vaughanTypeIIFixedShellOuterEnergy k a *
        ∑ r ∈ vaughanTypeIIFixedShell k,
          ((((Nat.log2 L + 1 : ℕ) : ℝ) ^ 2) *
            primitiveLargeSieveConstant L Q *
              ∑ t ∈ Finset.Icc (1 : ℤ) L,
                ‖vaughanTypeIICollectedRowCoefficient N r c t‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro r hr
        simpa using weighted_primitive_prefix_maximal
          (vaughanTypeIICollectedRowCoefficient N r c) 0 L Q hQ
      · exact Finset.sum_nonneg fun r hr => sq_nonneg ‖a r‖
    _ = _ := by
      simp only [vaughanTypeIIFixedShellTensorEnergy]
      dsimp [L]
      simp only [Finset.mul_sum]
      ring

/-- The AP-normalized `1/φ(d)` mean is converted by the genuine conductor
Cauchy connector to the proved actual fixed-shell square ledger. -/
theorem highConductorVaughanTypeIIFixedShell_mean_sq_le
    (R Q N k : ℕ) (hQ : 0 < Q)
    (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ) :
    (highConductorPrimitiveMean R Q
      (fun d => highConductorVaughanTypeIIFixedShellAmplitude N k d a c)) ^ 2 ≤
      highConductorHarmonicTail R Q *
        (((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) ^ 2 *
          primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q *
          (vaughanTypeIIFixedShellOuterEnergy k a *
            vaughanTypeIIFixedShellTensorEnergy N k c)) := by
  exact (highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger R Q _).trans
    (mul_le_mul_of_nonneg_left
      (highConductorVaughanTypeIIFixedShell_squareLedger_le R Q N k hQ a c)
      (Finset.sum_nonneg fun d hd => by positivity))

/-- The shortened large-sieve diagonal pays the shell cardinality scale without
losing `2^k`: `2^k * (N / 2^k) ≤ N`. -/
theorem vaughanTypeIIFixedShell_diagonal_scale (N k : ℕ) :
    2 ^ k * vaughanTypeIIFixedShellLength N k ≤ N := by
  simpa [vaughanTypeIIFixedShellLength] using Nat.mul_div_le N (2 ^ k)

/-- Exact diagonal/modulus audit after paying a shell energy bounded by `2^k`.
The shortened diagonal is at most `N`; the modulus term remains `2^k Q²`.
No power of the conductor cutoff `R` appears in this rowwise large-sieve step. -/
theorem vaughanTypeIIFixedShell_largeSieve_scale (N Q k : ℕ) :
    (2 ^ k : ℝ) *
        primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q ≤
      (N : ℝ) + (2 ^ k : ℝ) *
        (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
          (Q : ℝ) ^ 2 := by
  have hdiag :
      (2 ^ k : ℝ) * (vaughanTypeIIFixedShellLength N k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast vaughanTypeIIFixedShell_diagonal_scale N k
  -- Distribute the shell scale; the modulus term is identical on both sides.
  unfold primitiveLargeSieveConstant
  rw [mul_add, ← mul_assoc]
  exact add_le_add_left hdiag _

end
end AnalyticNumberTheory.LargeSieve
