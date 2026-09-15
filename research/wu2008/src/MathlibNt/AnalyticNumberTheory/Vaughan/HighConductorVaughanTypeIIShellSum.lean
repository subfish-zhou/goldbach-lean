import MathlibNt.AnalyticNumberTheory.Vaughan.HighConductorVaughanTypeIIFixedShell
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedTypeIIActualDecomposition

/-!
# Actual high-conductor Type-II shell-sum ledger

This module partitions the literal collected outer rows `1 ≤ r < 2^K` into
canonical shells.  It retains the conductor window `R < d ≤ Q` and the actual
short length `N / 2^k` separately for every shell.  No full Type-II saving
premise is used.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- The complete collected Type-II prefix before the canonical outer-shell
partition. -/
def vaughanTypeIICollectedPrefix
    (N K y d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℂ :=
  ∑ k ∈ Finset.range K,
    ∑ r ∈ vaughanTypeIIFixedShell k,
      a r * ∑ t ∈ Finset.Icc (1 : ℤ)
          (min y (vaughanTypeIIFixedShellLength N k) : ℤ),
        vaughanTypeIICollectedRowCoefficient N r c t * χ.1 (t : ZMod d)

/-- Canonical powers-of-two shells partition the literal positive outer range. -/
theorem sum_Ico_one_pow_two_eq_sum_vaughanTypeIIFixedShells
    (K : ℕ) (f : ℕ → ℂ) :
    (∑ r ∈ Finset.Ico 1 (2 ^ K), f r) =
      ∑ k ∈ Finset.range K, ∑ r ∈ vaughanTypeIIFixedShell k, f r := by
  induction K with
  | zero => simp [vaughanTypeIIFixedShell]
  | succ K ih =>
      have hp : 1 ≤ 2 ^ K := by
        exact pow_pos (by norm_num : 0 < (2 : ℕ)) K
      have hset :
          Finset.Ico 1 (2 ^ (K + 1)) =
            Finset.Ico 1 (2 ^ K) ∪ Finset.Ico (2 ^ K) (2 ^ (K + 1)) := by
        ext r
        simp only [Finset.mem_Ico, Finset.mem_union]
        omega
      have hdis : Disjoint (Finset.Ico 1 (2 ^ K))
          (Finset.Ico (2 ^ K) (2 ^ (K + 1))) := by
        rw [Finset.disjoint_left]
        intro r hr₁ hr₂
        simp only [Finset.mem_Ico] at hr₁ hr₂
        omega
      rw [hset, Finset.sum_union hdis, ih, Finset.sum_range_succ]
      simp [vaughanTypeIIFixedShell]

/-- The existing collected-row expression decomposes exactly into its canonical
shell expressions; this is an identity, not a decomposition premise. -/
theorem vaughanTypeIICollectedPrefix_eq_shellSum
    (N K y d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    vaughanTypeIICollectedPrefix N K y d a c χ =
      ∑ k ∈ Finset.range K,
        ∑ r ∈ vaughanTypeIIFixedShell k,
          a r * ∑ t ∈ Finset.Icc (1 : ℤ)
              (min y (vaughanTypeIIFixedShellLength N k) : ℤ),
            vaughanTypeIICollectedRowCoefficient N r c t * χ.1 (t : ZMod d) := by
  rfl

/-- Literal complete-prefix square of the collected outer range. -/
def vaughanTypeIICollectedPrefixSquare
    (N K y d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  ‖vaughanTypeIICollectedPrefix N K y d a c χ‖ ^ 2

/-- Maximum over the same physical prefixes used by every fixed-shell row. -/
def vaughanTypeIICollectedPrefixMaxSquare
    (N K d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  ((Finset.range (N + 1)).image
    (fun y => vaughanTypeIICollectedPrefixSquare N K y d a c χ)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Shell-sum square majorant.  Every summand retains its own physical length
`N / 2^k` through `vaughanTypeIIFixedShellPrefixMaxSquare`. -/
def vaughanTypeIIShellSumMajorantSquare
    (N K d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  (K : ℝ) * ∑ k ∈ Finset.range K,
    vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ

/-- AP-normalized amplitude attached to the honest shell-sum majorant. -/
def highConductorVaughanTypeIIShellSumAmplitude
    (N K d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) : ℝ :=
  Real.sqrt (vaughanTypeIIShellSumMajorantSquare N K d a c χ)

private theorem norm_sum_sq_le_card_mul_sum_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le _ _
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (∑ i ∈ s, (1 : ℝ) ^ 2) * (∑ i ∈ s, ‖z i‖ ^ 2) :=
      by simpa only [one_mul] using
        Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖z i‖)
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by simp

private theorem vaughanTypeIIFixedShellPrefixSquare_nonneg
    (N k y d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    0 ≤ vaughanTypeIIFixedShellPrefixSquare N k y d a c χ := by
  unfold vaughanTypeIIFixedShellPrefixSquare
  positivity

private theorem vaughanTypeIIFixedShellPrefixMaxSquare_nonneg
    (N k d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    0 ≤ vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ := by
  unfold vaughanTypeIIFixedShellPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨0, by simp,
    by simp [vaughanTypeIIFixedShellPrefixSquare]⟩

lemma vaughanTypeIIShellSumMajorantSquare_nonneg
    (N K d : ℕ) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    0 ≤ vaughanTypeIIShellSumMajorantSquare N K d a c χ := by
  unfold vaughanTypeIIShellSumMajorantSquare
  exact mul_nonneg (Nat.cast_nonneg K)
    (Finset.sum_nonneg fun k hk =>
      vaughanTypeIIFixedShellPrefixMaxSquare_nonneg N k d a c χ)

/-- The exact collected-shell decomposition, followed only by finite shell
Cauchy, bounds every physical prefix by the shell-sum majorant. -/
theorem vaughanTypeIICollectedPrefixSquare_le_shellSumMajorant
    (N K y d : ℕ) (_hy : y ≤ N) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (χ : PrimitiveCharacter d) :
    vaughanTypeIICollectedPrefixSquare N K y d a c χ ≤
      vaughanTypeIIShellSumMajorantSquare N K d a c χ := by
  rw [vaughanTypeIICollectedPrefixSquare,
    vaughanTypeIICollectedPrefix_eq_shellSum]
  let z : ℕ → ℂ := fun k =>
    ∑ r ∈ vaughanTypeIIFixedShell k,
      a r * ∑ t ∈ Finset.Icc (1 : ℤ)
          (min y (vaughanTypeIIFixedShellLength N k) : ℤ),
        vaughanTypeIICollectedRowCoefficient N r c t * χ.1 (t : ZMod d)
  calc
    ‖∑ k ∈ Finset.range K, z k‖ ^ 2 ≤
        (K : ℝ) * ∑ k ∈ Finset.range K, ‖z k‖ ^ 2 := by
      simpa using norm_sum_sq_le_card_mul_sum_sq (Finset.range K) z
    _ ≤ (K : ℝ) * ∑ k ∈ Finset.range K,
        vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro k hk
        unfold vaughanTypeIIFixedShellPrefixMaxSquare
        simpa [z, vaughanTypeIIFixedShellPrefixSquare] using
          (Finset.le_max'
            ((Finset.range (vaughanTypeIIFixedShellLength N k + 1)).image
              (fun z => vaughanTypeIIFixedShellPrefixSquare N k z d a c χ))
            (vaughanTypeIIFixedShellPrefixSquare N k
              (min y (vaughanTypeIIFixedShellLength N k)) d a c χ)
            (Finset.mem_image.mpr ⟨_, by simp, rfl⟩))
      · positivity
    _ = vaughanTypeIIShellSumMajorantSquare N K d a c χ := rfl

/-- **High-conductor Type-II shell-sum square ledger.**  The conductor block
`R < d ≤ Q` remains literal on the left.  On the right each shell keeps its
own length `N / 2^k`; no complete-saving premise occurs. -/
theorem highConductorVaughanTypeIIShellSum_squareLedger_le
    (R Q N K : ℕ) (hQ : 0 < Q)
    (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ) :
    highConductorPrimitiveSquareLedger R Q
        (fun d => highConductorVaughanTypeIIShellSumAmplitude N K d a c) ≤
      (K : ℝ) * ∑ k ∈ Finset.range K,
        ((((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q *
          (vaughanTypeIIFixedShellOuterEnergy k a *
            vaughanTypeIIFixedShellTensorEnergy N k c)) := by
  unfold highConductorPrimitiveSquareLedger
  have hsqrt : ∀ d (χ : PrimitiveCharacter d),
      (Real.sqrt (vaughanTypeIIShellSumMajorantSquare N K d a c χ)) ^ 2 =
        vaughanTypeIIShellSumMajorantSquare N K d a c χ := fun d χ =>
    Real.sq_sqrt (vaughanTypeIIShellSumMajorantSquare_nonneg N K d a c χ)
  have hchars (d : ℕ) :
      (∑ χ : PrimitiveCharacter d,
        vaughanTypeIIShellSumMajorantSquare N K d a c χ) =
      (K : ℝ) * ∑ k ∈ Finset.range K,
        ∑ χ : PrimitiveCharacter d,
          vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ := by
    simp only [vaughanTypeIIShellSumMajorantSquare, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hsqrtFixed (k d : ℕ) (χ : PrimitiveCharacter d) :
      (Real.sqrt (vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ)) ^ 2 =
        vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ :=
    Real.sq_sqrt (vaughanTypeIIFixedShellPrefixMaxSquare_nonneg N k d a c χ)
  have hdexpand (d : ℕ) :
      ((d : ℝ) / d.totient) *
          ((K : ℝ) * ∑ k ∈ Finset.range K,
            ∑ χ : PrimitiveCharacter d,
              vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ) =
        ∑ k ∈ Finset.range K, (K : ℝ) *
          (((d : ℝ) / d.totient) *
            ∑ χ : PrimitiveCharacter d,
              vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ) := by
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [highConductorVaughanTypeIIShellSumAmplitude, hsqrt, hchars]
  calc
    (∑ d ∈ Finset.Ioc R Q, ((d : ℝ) / d.totient) *
        ((K : ℝ) * ∑ k ∈ Finset.range K,
          ∑ χ : PrimitiveCharacter d,
            vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ)) =
      (K : ℝ) * ∑ k ∈ Finset.range K,
        ∑ d ∈ Finset.Ioc R Q, ((d : ℝ) / d.totient) *
          ∑ χ : PrimitiveCharacter d,
            vaughanTypeIIFixedShellPrefixMaxSquare N k d a c χ := by
      simp_rw [hdexpand]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) * ∑ k ∈ Finset.range K,
        ((((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q *
          (vaughanTypeIIFixedShellOuterEnergy k a *
            vaughanTypeIIFixedShellTensorEnergy N k c)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro k hk
        have hfixed :=
          highConductorVaughanTypeIIFixedShell_squareLedger_le R Q N k hQ a c
        unfold highConductorPrimitiveSquareLedger at hfixed
        simp_rw [highConductorVaughanTypeIIFixedShellAmplitude,
          hsqrtFixed k] at hfixed
        exact hfixed
      · positivity

/-- The genuine conductor Cauchy connector converts the shell-sum square ledger
into the AP-normalized mean-square statement while retaining `R` through the
harmonic tail. -/
theorem highConductorVaughanTypeIIShellSum_mean_sq_le
    (R Q N K : ℕ) (hQ : 0 < Q)
    (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ) :
    (highConductorPrimitiveMean R Q
      (fun d => highConductorVaughanTypeIIShellSumAmplitude N K d a c)) ^ 2 ≤
      highConductorHarmonicTail R Q *
        ((K : ℝ) * ∑ k ∈ Finset.range K,
          ((((Nat.log2 (vaughanTypeIIFixedShellLength N k) + 1 : ℕ) : ℝ) ^ 2) *
            primitiveLargeSieveConstant (vaughanTypeIIFixedShellLength N k) Q *
            (vaughanTypeIIFixedShellOuterEnergy k a *
              vaughanTypeIIFixedShellTensorEnergy N k c))) := by
  exact (highConductorPrimitiveMean_sq_le_harmonic_mul_squareLedger R Q _).trans
    (mul_le_mul_of_nonneg_left
      (highConductorVaughanTypeIIShellSum_squareLedger_le R Q N K hQ a c)
      (Finset.sum_nonneg fun d hd => by positivity))

/-! ## Connector to the production hyperbolic collected-shell decomposition -/

/-- The shell sum occurring on the right of the production exact
hyperbolic-prefix decomposition.  Unlike `vaughanTypeIICollectedPrefix`, this
uses the actual canonical rectangle family and the actual collected-prefix
maxima from `VaughanDirectAPNormalizedTypeIIActualDecomposition`. -/
def vaughanTypeIIProductionActualCollectedShellSum
    (N Q u v : ℕ) : ℝ :=
  ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    apNormalizedVaughanActualCollectedShellMean N Q u v kl.1 kl.2

/-- The production direct Type-II mean is connected to the actual collected
shell sum by the already-proved exact hyperbolic decomposition, rather than by
a conclusion-shaped decomposition premise. -/
theorem apNormalizedVaughanTypeIIMean_le_productionActualCollectedShellSum
    (N Q u v : ℕ) :
    apNormalizedVaughanTypeIIMean N Q u v ≤
      vaughanTypeIIProductionActualCollectedShellSum N Q u v := by
  exact apNormalizedVaughanTypeIIMean_le_active_collected_shells N Q u v

end
end AnalyticNumberTheory.LargeSieve
