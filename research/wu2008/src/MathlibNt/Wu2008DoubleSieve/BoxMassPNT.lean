import MathlibNt.Wu2008DoubleSieve.ConvolutionWuBoxes

/-!
# True-li prefix estimates for shrinking prime boxes

The only analytic prime-distribution input is the frozen, unconditional
Richert (4.18) theorem, specialized to modulus one. The normalization is the
literal integral from `2`, not the proxy `x / log x`.
-/

namespace Wu2008DoubleSieve

open Finset Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable def boxPrimePrefix (x : ℕ) : Finset ℕ :=
  (range (x + 1)).filter Nat.Prime

theorem mem_boxPrimePrefix {x p : ℕ} :
    p ∈ boxPrimePrefix x ↔ p.Prime ∧ p ≤ x := by
  simp only [boxPrimePrefix, mem_filter, mem_range, Nat.lt_succ_iff, and_comm]

theorem boxPrimePrefix_card_eq_primesInAP (x : ℕ) :
    (boxPrimePrefix x).card =
      MathlibNt.SieveTheory.BombieriVinogradov.primesInAP x 1 0 := by
  unfold boxPrimePrefix MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
  congr 1
  ext p
  simp [Nat.ModEq]
  exact fun _ _ => Nat.mod_one p

/-- Arbitrary inverse-log true-li PNT, uniformly over integer prefixes.
The constant and threshold precede *both* the ambient and prefix endpoints. -/
theorem boxPrimePrefix_trueLi (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ x : ℕ, 2 ≤ x → x ≤ X →
        |((boxPrimePrefix x).card : ℝ) - logarithmicIntegral x| ≤
          C * (X : ℝ) / Real.log X ^ A := by
  obtain ⟨B, _, C, hC, hBV⟩ := richert418 A hA
  have hcut : ∀ᶠ X : ℕ in atTop,
      1 ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff X B := by
    filter_upwards [convolutionModulusCutoff_eventually_le_pan B
      (show (0 : ℝ) < 1 / 4 by norm_num),
      eventually_ge_atTop (1 : ℕ)] with X hX hX1
    apply le_trans _ hX
    unfold convolutionModulusCutoff
    apply (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg X) _)).mpr
    simpa only [Nat.cast_one] using
      Real.one_le_rpow (show (1 : ℝ) ≤ X by exact_mod_cast hX1)
        (show (0 : ℝ) ≤ 1 / 2 - 1 / 4 by norm_num)
  refine ⟨C, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hBV, hcut, eventually_ge_atTop (2 : ℕ)] with X hBVX hcutX hX
  intro x hx hxX
  have hres : 0 ∈ AnalyticNumberTheory.Sieve.unitResidues 1 := by
    simp [AnalyticNumberTheory.Sieve.unitResidues]
  calc
    _ = |primeAPError x 1 0| := by
      simp [primeAPError, boxPrimePrefix_card_eq_primesInAP]
    _ ≤ primeAPPrefixMaxError X 1 :=
      (abs_primeAPError_le_residueMax hres).trans
        (primeAPResidueMaxError_le_prefixMax (mem_Icc.mpr ⟨hx, hxX⟩))
    _ ≤ ∑ q ∈ Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff X B),
        primeAPPrefixMaxError X q :=
      single_le_sum (fun q _ => primeAPPrefixMaxError_nonneg X q)
        (mem_Icc.mpr ⟨le_rfl, hcutX⟩)
    _ ≤ C * (X : ℝ) / Real.log X ^ A := hBVX hX

end Wu2008DoubleSieve
