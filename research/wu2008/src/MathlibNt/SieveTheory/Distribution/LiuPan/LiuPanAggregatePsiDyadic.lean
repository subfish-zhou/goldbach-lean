import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanAggregatePsiCharacters

/-!
# Dyadic blocks for Liu's aggregate psi hyperbola

This module decomposes the exact source/von-Mangoldt hyperbola after both
induced-character factors have been transferred to the primitive character.
The blocks retain the condition `a * m ≤ y`; in particular, no full rectangle
is substituted for the hyperbola.  The resulting cells are staircases.  A
separate Cauchy--Schwarz/large-sieve estimate in each coordinate is therefore
not available: in the ranges `D^2 ≪ V` and `V ≪ D^2` it loses, respectively,
the conductor saving and the source square-root saving.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset ArithmeticFunction
open AnalyticNumberTheory.Sieve
open _root_.AnalyticNumberTheory.LargeSieve





/-- Logarithmically normalized von Mangoldt coefficients, including their
totalized zero values at `0` and `1`. -/
noncomputable def liuPanLogLambdaCoefficient (n : ℕ) : ℂ :=
  ((Λ n / Real.log (n : ℝ) : ℝ) : ℂ)

@[simp] theorem liuPanLogLambdaCoefficient_zero :
    liuPanLogLambdaCoefficient 0 = 0 := by
  norm_num [liuPanLogLambdaCoefficient, ArithmeticFunction.vonMangoldt_apply,
    not_isPrimePow_zero]

@[simp] theorem liuPanLogLambdaCoefficient_one :
    liuPanLogLambdaCoefficient 1 = 0 := by
  norm_num [liuPanLogLambdaCoefficient, ArithmeticFunction.vonMangoldt_apply]



/-- The exact hyperbola after primitive transfer on both the source and Lambda
sides.  The inner cutoff still depends on the same source variable. -/
noncomputable def liuPanPrimitiveDilationLogLambdaHyperbola
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    ((ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)) *
      ∑ u ∈ range (X / e + 1),
        (liuPanSourceZeroExtension f (e * u) *
          χ.primitiveCharacter (u : ZMod χ.conductor)) *
          ∑ r ∈ (q / χ.conductor).divisors,
            ((ArithmeticFunction.moebius r : ℂ) *
              χ.primitiveCharacter (r : ZMod χ.conductor)) *
              ∑ v ∈ range ((y / (e * u)) / r + 1),
                liuPanLogLambdaCoefficient (r * v) *
                  χ.primitiveCharacter (v : ZMod χ.conductor)


/-! ## Low-conductor primitive Siegel--Walfisz interface -/



/-- The low-conductor sum after applying the exact source/Lambda dilation
identity to every lifted primitive character. -/
noncomputable def liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) : ℂ :=
  if q = 0 then 0
  else
    (Nat.totient q : ℂ)⁻¹ *
      ∑ d ∈ Icc 2 q, if d ≤ D₀ then
        if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            let χ := DirichletCharacter.changeLevel hdq ψ
            star (χ (l : ZMod q)) *
              liuPanPrimitiveDilationLogLambdaHyperbola y X q f χ
        else 0
      else 0


@[simp] theorem liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum_zero
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
      D₀ y X 0 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum]

@[simp] theorem liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum_one
    (D₀ y X l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
      D₀ y X 1 l f = 0 := by
  simp [liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum]

























































/-! ## Fixed dilation staircase blocks -/















end MathlibNt.SieveTheory.LiuWeight
