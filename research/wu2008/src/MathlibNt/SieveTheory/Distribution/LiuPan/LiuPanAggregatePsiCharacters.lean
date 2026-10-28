import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbel
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SumIntegralComparisons
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Character reduction for Liu's aggregate psi term

This module gives exact finite character identities for the aggregate
source-convolution psi discrepancy.  It separates the principal character
before any absolute value or character Cauchy--Schwarz inequality, and then
regroups the nonprincipal part by primitive conductor.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset ArithmeticFunction
open Filter
open AnalyticNumberTheory.Sieve
open _root_.AnalyticNumberTheory.LargeSieve

/-- The source prefix twisted by a Dirichlet character. -/
noncomputable def liuPanSourceCharacterPrefix
    (A q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ Icc 1 A, (f a : ℂ) * χ (a : ZMod q)

/-- The von Mangoldt prefix twisted by a Dirichlet character. -/
noncomputable def liuPanLambdaCharacterPrefix
    (t q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ range (t + 1), (Λ n : ℂ) * χ (n : ZMod q)

/-- The logarithmically normalized von Mangoldt prefix twisted by a Dirichlet
character.  The totalized terms at `0` and `1` vanish. -/
noncomputable def liuPanLogLambdaCharacterPrefix
    (t q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ range (t + 1),
    ((Λ n / Real.log (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod q)











/-- The exact principal-character contribution to the aggregate discrepancy. -/
noncomputable def liuPanAggregatePrincipalPsiTerm
    (t A q : ℕ) (f : ℕ → ℝ) : ℂ :=
  liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) *
    (liuPanLambdaCharacterPrefix t q (1 : DirichletCharacter ℂ q) - (t : ℂ)) /
      (Nat.totient q : ℂ)

/-- The exact nonprincipal character contribution, with the source and von
Mangoldt prefixes still paired character by character. -/
noncomputable def liuPanAggregateNonprincipalPsiTerm
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
      star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
        liuPanLambdaCharacterPrefix t q χ

/-- The canonical finite character expansion.  Modulus zero is assigned zero;
the positive-modulus theorem below identifies this with the actual aggregate
discrepancy. -/
noncomputable def liuPanAggregatePsiCharacterExpansion
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else liuPanAggregatePrincipalPsiTerm t A q f +
    liuPanAggregateNonprincipalPsiTerm t A q l f

@[simp] theorem liuPanAggregatePsiCharacterExpansion_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiCharacterExpansion t A 0 l f = 0 := by
  simp [liuPanAggregatePsiCharacterExpansion]


/-! ## The exact principal correction -/

/-- The ordinary finite Chebyshev psi prefix. -/
noncomputable def liuPanPsiPrefix (t : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), Λ n


/-- The ordinary Chebyshev PNT remainder at a natural argument. -/
noncomputable def liuPanPNTError (t : ℕ) : ℝ :=
  liuPanPsiPrefix t - t

/-- The totalized inverse-log Abel transform of the ordinary PNT remainder. -/
noncomputable def liuPanLogPNTError (t : ℕ) : ℝ :=
  (Real.log (t : ℝ))⁻¹ * liuPanPNTError t +
    ∑ n ∈ range t, liuPanInverseLogAbelWeight n * liuPanPNTError n











/-- Totalized inverse-log Abel weights remove the exceptional argument zero. -/
@[simp] theorem liuPanLogPNTError_zero : liuPanLogPNTError 0 = 0 := by
  simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix]

/-- Totalized inverse-log Abel weights remove the exceptional argument one. -/
@[simp] theorem liuPanLogPNTError_one : liuPanLogPNTError 1 = 0 := by
  simp [liuPanLogPNTError, liuPanPNTError, liuPanPsiPrefix,
    ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]

/-- The part of psi supported on integers not coprime to the modulus.  Since
von Mangoldt is supported on prime powers, these are exactly the prime-power
terms whose prime divides `q`. -/
noncomputable def liuPanPsiNoncoprimeCorrection (t q : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), if n.Coprime q then 0 else Λ n

/-- The logarithmically normalized noncoprime prime-power correction.  The
terms at `0` and `1` vanish, so this is a total finite sum. -/
noncomputable def liuPanLogNoncoprimeCorrection (t q : ℕ) : ℝ :=
  ∑ n ∈ range (t + 1), if n.Coprime q then 0
    else Λ n / Real.log (n : ℝ)

/-- Discrete Abel summation for the noncoprime prime-power correction. -/
theorem liuPanLogNoncoprimeCorrection_eq_discreteAbel (t q : ℕ) :
    liuPanLogNoncoprimeCorrection t q =
      (Real.log (t : ℝ))⁻¹ * liuPanPsiNoncoprimeCorrection t q +
        ∑ n ∈ range t, liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q := by
  let c : ℕ → ℝ := fun n => if n.Coprime q then 0 else Λ n
  have h := Finset.sum_range_by_parts
    (fun n : ℕ => (Real.log (n : ℝ))⁻¹) c (t + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h
  rw [show liuPanLogNoncoprimeCorrection t q =
      ∑ n ∈ range (t + 1), (Real.log (n : ℝ))⁻¹ * c n by
    unfold liuPanLogNoncoprimeCorrection c
    apply sum_congr rfl
    intro n hn
    by_cases hcop : n.Coprime q <;>
      simp [hcop, div_eq_inv_mul]]
  rw [h]
  change
    (Real.log (t : ℝ))⁻¹ * liuPanPsiNoncoprimeCorrection t q -
        ∑ n ∈ range t,
          ((Real.log (n + 1 : ℕ))⁻¹ - (Real.log (n : ℝ))⁻¹) *
            liuPanPsiNoncoprimeCorrection n q =
      _
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hn2 : 2 ≤ n
  · simp only [liuPanInverseLogAbelWeight, if_pos hn2]
    ring
  · interval_cases n
    · simp [liuPanInverseLogAbelWeight, liuPanPsiNoncoprimeCorrection]
    · have hsmall : liuPanPsiNoncoprimeCorrection 1 q = 0 := by
        norm_num [liuPanPsiNoncoprimeCorrection, Finset.sum_range_succ,
          ArithmeticFunction.vonMangoldt_apply, not_isPrimePow_zero]
      simp [liuPanInverseLogAbelWeight, hsmall]










/-- Modulus one has no noncoprime prime-power correction. -/
@[simp] theorem liuPanLogNoncoprimeCorrection_one (t : ℕ) :
    liuPanLogNoncoprimeCorrection t 1 = 0 := by
  unfold liuPanLogNoncoprimeCorrection
  apply sum_eq_zero
  intro n hn
  simp





/-- The correction to the principal term from prime powers whose prime divides
the modulus. -/
noncomputable def liuPanAggregatePrincipalNoncoprimePsiTerm
    (t A q : ℕ) (f : ℕ → ℝ) : ℂ :=
  liuPanSourceCharacterPrefix A q f (1 : DirichletCharacter ℂ q) *
    (liuPanPsiNoncoprimeCorrection t q : ℂ) / (Nat.totient q : ℂ)

/-- The real source aggregate paired with the noncoprime psi correction. -/
noncomputable def liuPanAggregateNoncoprimePsiCorrection
    (t A q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0) *
    liuPanPsiNoncoprimeCorrection t q


/-- The zero modulus is canonically killed by the totient normalization. -/
@[simp] theorem liuPanAggregatePrincipalNoncoprimePsiTerm_zero
    (t A : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePrincipalNoncoprimePsiTerm t A 0 f = 0 := by
  simp [liuPanAggregatePrincipalNoncoprimePsiTerm]

-- These scalar identities keep the large character and PNT terms opaque.
private theorem liuPan_scalar_coprime_sum (A q : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (∑ a ∈ Icc 1 A, if a.Coprime q then f a * c else 0) =
      (∑ a ∈ Icc 1 A, if a.Coprime q then f a else 0) * c := by
  simp only [sum_mul, ite_mul, zero_mul]

private theorem liuPan_scalar_endpoint_shell
    (y X q : ℕ) (f g c : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then f a * g (y / a) * c (y / a) else 0) =
      ∑ k ∈ Icc 1 y, g k *
        ((∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X k),
            if a.Coprime q then f a else 0) * c k -
          (∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (k + 1)),
            if a.Coprime q then f a else 0) * c k) := by
  have h := sum_source_eq_sum_quotient_shells y X g
    (fun k a => if a.Coprime q then f a * c k else 0) hg0
  simp only [liuPan_scalar_coprime_sum] at h
  convert h using 1
  apply sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    exact mul_right_comm (f a) (g (y / a)) (c (y / a)) |>.trans
      (mul_comm (f a * c (y / a)) (g (y / a)))
  · simp only [if_neg hcop, mul_zero]

private theorem liuPan_scalar_prefix_swap
    (y X q : ℕ) (f w c : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), w n * c n) else 0) =
      ∑ n ∈ range y, w n *
        ((∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (n + 1)),
          if a.Coprime q then f a else 0) * c n) := by
  have h := sum_source_prefix_eq_sum_aggregate_prefix y X w
    (fun n a => if a.Coprime q then f a * c n else 0)
  simp only [liuPan_scalar_coprime_sum] at h
  rw [← h]
  apply sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop, mul_sum]
    apply sum_congr rfl
    intro n hn
    exact mul_left_comm (f a) (w n) (c n)
  · simp only [if_neg hcop, mul_zero, sum_const_zero]

/-- The source-aggregated endpoint shell for a scalar noncoprime correction. -/
theorem liuPanAggregateNoncoprimePsiCorrection_endpoint_shell
    (y X q : ℕ) (f g : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * g (y / a) * liuPanPsiNoncoprimeCorrection (y / a) q
    else 0) =
      ∑ k ∈ Icc 1 y, g k *
        (liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X k) q f -
          liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X (k + 1)) q f) := by
  exact liuPan_scalar_endpoint_shell y X q f g (fun k => liuPanPsiNoncoprimeCorrection k q) hg0

/-- Swapping the source sum with scalar noncoprime correction prefixes retains
the shared Abel source cutoff. -/
theorem liuPanAggregateNoncoprimePsiCorrection_prefix_swap
    (y X q : ℕ) (f w : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), w n *
        liuPanPsiNoncoprimeCorrection n q)
    else 0) =
      ∑ n ∈ range y, w n *
        liuPanAggregateNoncoprimePsiCorrection n
          (liuPanAbelSourceCutoff y X (n + 1)) q f := by
  exact liuPan_scalar_prefix_swap y X q f w (fun k => liuPanPsiNoncoprimeCorrection k q)


/-- At modulus one there are no nonprincipal characters. -/
@[simp] theorem liuPanPrimePowerNonprincipalCharacters_one :
    liuPanPrimePowerNonprincipalCharacters 1 = ∅ := by
  classical
  ext χ
  simp [liuPanPrimePowerNonprincipalCharacters, Subsingleton.elim χ 1]

/-- Modulus one consists only of the principal psi contribution. -/
@[simp] theorem liuPanAggregateNonprincipalPsiTerm_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalPsiTerm t A 1 l f = 0 := by
  simp [liuPanAggregateNonprincipalPsiTerm]

/-- At modulus one the canonical expansion is principal only. -/
@[simp] theorem liuPanAggregatePsiCharacterExpansion_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiCharacterExpansion t A 1 l f =
      liuPanAggregatePrincipalPsiTerm t A 1 f := by
  simp [liuPanAggregatePsiCharacterExpansion]


/-! ## Primitive dilation on the source and von Mangoldt sides -/

/-- The source sequence extended by zero at the excluded index `0`. -/
noncomputable def liuPanSourceZeroExtension (f : ℕ → ℝ) (a : ℕ) : ℂ :=
  if a = 0 then 0 else (f a : ℂ)





/-! ## Exact conductor-first regrouping -/

/-- The nonprincipal character product at one level. -/
noncomputable def liuPanAggregatePsiCharacterProduct
    (t A q l : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  star (χ (l : ZMod q)) * liuPanSourceCharacterPrefix A q f χ *
    liuPanLambdaCharacterPrefix t q χ

/-- The nonprincipal sum regrouped by exact conductor.  Conductor one is absent
from the indexing interval. -/
noncomputable def liuPanAggregatePsiConductorSum
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ d ∈ Icc 2 q,
      ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
          (fun χ => χ.conductor = d),
        liuPanAggregatePsiCharacterProduct t A q l f χ

@[simp] theorem liuPanAggregatePsiConductorSum_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiConductorSum t A 0 l f = 0 := by
  simp [liuPanAggregatePsiConductorSum]

@[simp] theorem liuPanAggregatePsiConductorSum_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiConductorSum t A 1 l f = 0 := by
  simp [liuPanAggregatePsiConductorSum]



/-- The conductor sum reindexed by the unique primitive character inducing each
nonprincipal character. -/
noncomputable def liuPanAggregatePsiPrimitiveLiftSum
    (t A q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ d ∈ Icc 2 q, if hdq : d ∣ q then
      ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
        liuPanAggregatePsiCharacterProduct t A q l f
          (DirichletCharacter.changeLevel hdq ψ)
    else 0

@[simp] theorem liuPanAggregatePsiPrimitiveLiftSum_zero
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiPrimitiveLiftSum t A 0 l f = 0 := by
  simp [liuPanAggregatePsiPrimitiveLiftSum]

@[simp] theorem liuPanAggregatePsiPrimitiveLiftSum_one
    (t A l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregatePsiPrimitiveLiftSum t A 1 l f = 0 := by
  simp [liuPanAggregatePsiPrimitiveLiftSum]


/-! ## Substitution into the aggregate Abel term -/

/-- The exact character expansion substituted into both shared-`y` Abel sums. -/
noncomputable def liuPanAggregateInverseLogPsiCharacterTerm
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePsiCharacterExpansion k
        (liuPanAbelSourceCutoff y X k) q l f -
      liuPanAggregatePsiCharacterExpansion k
        (liuPanAbelSourceCutoff y X (k + 1)) q l f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePsiCharacterExpansion n
      (liuPanAbelSourceCutoff y X (n + 1)) q l f

@[simp] theorem liuPanAggregateInverseLogPsiCharacterTerm_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiCharacterTerm y X 0 l f = 0 := by
  simp [liuPanAggregateInverseLogPsiCharacterTerm]


/-- The principal contribution after substitution into the shared-`y` Abel
shell and prefix sums. -/
noncomputable def liuPanAggregateInverseLogPrincipalPsiTerm
    (y X q : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePrincipalPsiTerm k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePrincipalPsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePrincipalPsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q f








/-- The exact Liu source is an indicator, so replacing it by one is permitted
only through this explicit pointwise upper bound. -/
theorem liuWeight_le_one (N z y a : ℕ) : liuWeight N z y a ≤ 1 := by
  unfold liuWeight
  split <;> simp

/-- The reciprocal mass of the actual Liu source is bounded by the harmonic
sum; this is the source factor used for the long-quotient PNT range. -/
theorem sum_liuWeight_div_le_liuHarmonic (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        liuHarmonic N := by
  rw [liuHarmonic]
  apply sum_le_sum
  intro a ha
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (mem_Icc.mp ha).1
  rw [div_eq_mul_inv]
  simpa using mul_le_mul_of_nonneg_right
    (liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a)
    (inv_nonneg.mpr ha0.le)

/-- The reciprocal Liu-source mass costs at most one logarithm. -/
theorem sum_liuWeight_div_le_one_add_log (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a / a ≤
        1 + Real.log N :=
  (sum_liuWeight_div_le_liuHarmonic N).trans (liuHarmonic_le_one_add_log N)




/-- The modulus-noncoprime correction in the same shared-`y` Abel shell and
prefix aggregation. -/
noncomputable def liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm
    (y X q : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregatePrincipalNoncoprimePsiTerm k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregatePrincipalNoncoprimePsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregatePrincipalNoncoprimePsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The real shared-`y` Abel aggregation of the noncoprime correction. -/
noncomputable def liuPanAggregateInverseLogNoncoprimeCorrection
    (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
    (liuPanAggregateNoncoprimePsiCorrection k
        (liuPanAbelSourceCutoff y X k) q f -
      liuPanAggregateNoncoprimePsiCorrection k
        (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
  ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
    liuPanAggregateNoncoprimePsiCorrection n
      (liuPanAbelSourceCutoff y X (n + 1)) q f

/-- The aggregate correction is exactly the source sum of the logarithmically
normalized noncoprime prime-power correction; the same shared `y` and source
cutoffs are retained. -/
theorem liuPanAggregateInverseLogNoncoprimeCorrection_eq_source
    (y X q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNoncoprimeCorrection y X q f =
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * liuPanLogNoncoprimeCorrection (y / a) q
      else 0 := by
  symm
  simp_rw [liuPanLogNoncoprimeCorrection_eq_discreteAbel]
  calc
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * ((Real.log (y / a : ℕ))⁻¹ *
        liuPanPsiNoncoprimeCorrection (y / a) q +
        ∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q)
    else 0) =
      (∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (Real.log (y / a : ℕ))⁻¹ *
          liuPanPsiNoncoprimeCorrection (y / a) q
      else 0) +
      ∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
          liuPanPsiNoncoprimeCorrection n q)
      else 0 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro a ha
        by_cases hcop : a.Coprime q
        · simp only [if_pos hcop]
          ring
        · simp [hcop]
    _ = (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
        (liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X k) q f -
          liuPanAggregateNoncoprimePsiCorrection k
            (liuPanAbelSourceCutoff y X (k + 1)) q f)) +
        ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
          liuPanAggregateNoncoprimePsiCorrection n
            (liuPanAbelSourceCutoff y X (n + 1)) q f := by
      rw [liuPanAggregateNoncoprimePsiCorrection_endpoint_shell y X q f
        (fun k => (Real.log (k : ℝ))⁻¹) (by simp),
        liuPanAggregateNoncoprimePsiCorrection_prefix_swap y X q f
          liuPanInverseLogAbelWeight]
    _ = _ := rfl


/-- The shared-`y` principal noncoprime term also vanishes canonically at
modulus zero. -/
@[simp] theorem liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm_zero
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm y X 0 f = 0 := by
  simp [liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm]

/-- At modulus one the source form is exactly zero, not merely bounded. -/
@[simp] theorem liuPanAggregateInverseLogNoncoprimeCorrection_one
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNoncoprimeCorrection y X 1 f = 0 := by
  rw [liuPanAggregateInverseLogNoncoprimeCorrection_eq_source]
  apply sum_eq_zero
  intro a ha
  simp












/-- The nonprincipal contribution after substitution into the same Abel shell
and prefix sums. -/
noncomputable def liuPanAggregateInverseLogNonprincipalPsiTerm
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ) : ℂ)⁻¹ *
    (liuPanAggregateNonprincipalPsiTerm k
        (liuPanAbelSourceCutoff y X k) q l f -
      liuPanAggregateNonprincipalPsiTerm k
        (liuPanAbelSourceCutoff y X (k + 1)) q l f)) +
  ∑ n ∈ range y, (liuPanInverseLogAbelWeight n : ℂ) *
    liuPanAggregateNonprincipalPsiTerm n
      (liuPanAbelSourceCutoff y X (n + 1)) q l f

@[simp] theorem liuPanAggregateInverseLogNonprincipalPsiTerm_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X 0 l f = 0 := by
  simp [liuPanAggregateInverseLogNonprincipalPsiTerm,
    liuPanAggregateNonprincipalPsiTerm]

@[simp] theorem liuPanAggregateInverseLogNonprincipalPsiTerm_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogNonprincipalPsiTerm y X 1 l f = 0 := by
  simp [liuPanAggregateInverseLogNonprincipalPsiTerm]

/-- One character's exact inverse-log hyperbola convolution.  The source and
von Mangoldt factors remain paired before any norm is taken. -/
noncomputable def liuPanSourceLogLambdaCharacterHyperbola
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ a ∈ Icc 1 X, ((f a : ℂ) * χ (a : ZMod q)) *
    liuPanLogLambdaCharacterPrefix (y / a) q χ


/-- The nonprincipal inverse-log term in its exact character-by-character
hyperbola form.  Modulus zero is assigned zero canonically. -/
noncomputable def liuPanAggregateNonprincipalLogLambdaHyperbola
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ χ ∈ liuPanPrimePowerNonprincipalCharacters q,
        star (χ (l : ZMod q)) *
          liuPanSourceLogLambdaCharacterHyperbola y X q f χ

@[simp] theorem liuPanAggregateNonprincipalLogLambdaHyperbola_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalLogLambdaHyperbola y X 0 l f = 0 := by
  simp [liuPanAggregateNonprincipalLogLambdaHyperbola]

@[simp] theorem liuPanAggregateNonprincipalLogLambdaHyperbola_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateNonprincipalLogLambdaHyperbola y X 1 l f = 0 := by
  simp [liuPanAggregateNonprincipalLogLambdaHyperbola]



/-- The logarithmic hyperbola sum regrouped by exact conductor. -/
noncomputable def liuPanAggregateLogLambdaConductorSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q,
        ∑ χ ∈ (liuPanPrimePowerNonprincipalCharacters q).filter
            (fun χ => χ.conductor = d),
          star (χ (l : ZMod q)) *
            liuPanSourceLogLambdaCharacterHyperbola y X q f χ

@[simp] theorem liuPanAggregateLogLambdaConductorSum_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaConductorSum y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaConductorSum]

@[simp] theorem liuPanAggregateLogLambdaConductorSum_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaConductorSum y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaConductorSum]


/-- The conductor-grouped logarithmic hyperbola reindexed by primitive
characters and their unique lifts to level `q`. -/
noncomputable def liuPanAggregateLogLambdaPrimitiveLiftSum
    (y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if hdq : d ∣ q then
        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
          star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
            liuPanSourceLogLambdaCharacterHyperbola y X q f
              (DirichletCharacter.changeLevel hdq ψ)
      else 0

@[simp] theorem liuPanAggregateLogLambdaPrimitiveLiftSum_zero
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaPrimitiveLiftSum y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaPrimitiveLiftSum]

@[simp] theorem liuPanAggregateLogLambdaPrimitiveLiftSum_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaPrimitiveLiftSum y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaPrimitiveLiftSum]


/-- Primitive conductors at most `D₀`, retained in their exact lifted hyperbola
form. -/
noncomputable def liuPanAggregateLogLambdaLowConductorSum
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if d ≤ D₀ then
        if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
              liuPanSourceLogLambdaCharacterHyperbola y X q f
                (DirichletCharacter.changeLevel hdq ψ)
        else 0
      else 0

/-- Primitive conductors above `D₀`, the medium/high bilinear family. -/
noncomputable def liuPanAggregateLogLambdaMediumHighConductorSum
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if D₀ < d then
        if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            star ((DirichletCharacter.changeLevel hdq ψ) (l : ZMod q)) *
              liuPanSourceLogLambdaCharacterHyperbola y X q f
                (DirichletCharacter.changeLevel hdq ψ)
        else 0
      else 0

@[simp] theorem liuPanAggregateLogLambdaLowConductorSum_zero
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorSum D₀ y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorSum]

@[simp] theorem liuPanAggregateLogLambdaMediumHighConductorSum_zero
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaMediumHighConductorSum]

@[simp] theorem liuPanAggregateLogLambdaLowConductorSum_one
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorSum D₀ y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorSum]

@[simp] theorem liuPanAggregateLogLambdaMediumHighConductorSum_one
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaMediumHighConductorSum D₀ y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaMediumHighConductorSum]



/-- The substituted Abel term splits exactly into principal and nonprincipal
parts, still before taking an absolute value. -/
theorem liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
    {y X q l : ℕ} (f : ℕ → ℝ) (hq : 0 < q) :
    liuPanAggregateInverseLogPsiCharacterTerm y X q l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X q f +
        liuPanAggregateInverseLogNonprincipalPsiTerm y X q l f := by
  unfold liuPanAggregateInverseLogPsiCharacterTerm
    liuPanAggregateInverseLogPrincipalPsiTerm
    liuPanAggregateInverseLogNonprincipalPsiTerm
    liuPanAggregatePsiCharacterExpansion
  simp only [if_neg hq.ne', mul_add, mul_sub, sum_add_distrib,
    sum_sub_distrib]
  ring

/-- At modulus one the substituted Abel character term is principal only. -/
@[simp] theorem liuPanAggregateInverseLogPsiCharacterTerm_one
    (y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiCharacterTerm y X 1 l f =
      liuPanAggregateInverseLogPrincipalPsiTerm y X 1 f := by
  rw [liuPanAggregateInverseLogPsiCharacterTerm_eq_principal_add_nonprincipal
    f (by omega)]
  simp




/-! ## Source-family decomposition -/




































/-!
## Remaining analytic split

The ordinary principal/PNT family is closed unconditionally by
`liuMainPanAggregateInverseLogPrincipalPNTSourceFamilyBound`, and the
noncoprime family is also closed unconditionally.  Exactly two analytic regimes
remain, neither asserted here:

* low primitive conductors, to be treated by Siegel--Walfisz;
* medium and high conductors, requiring a weighted primitive bilinear
  hyperbola maximal estimate.
-/

end MathlibNt.SieveTheory.LiuWeight
