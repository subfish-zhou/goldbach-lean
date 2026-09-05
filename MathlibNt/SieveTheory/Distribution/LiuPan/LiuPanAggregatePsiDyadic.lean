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
open AnalyticNumberTheory.LargeSieve

/-- The half-open positive dyadic shell `[2^j, 2^(j+1))`. -/
def liuPanDyadicShell (j : ℕ) : Finset ℕ :=
  Ico (2 ^ j) (2 ^ (j + 1))

theorem mem_liuPanDyadicShell_iff_log {j n : ℕ} (hn : 0 < n) :
    n ∈ liuPanDyadicShell j ↔ Nat.log 2 n = j := by
  rw [Nat.log_eq_iff (Or.inr ⟨by omega, by omega⟩)]
  simp [liuPanDyadicShell]

/-- A positive prefix is the disjoint sum of its dyadic shells.  The ambient
upper bound permits all later source and Lambda prefixes to use the same pair
of logarithmic index ranges. -/
theorem sum_Icc_eq_sum_dyadicShell_of_le
    {α : Type*} [AddCommMonoid α] (g : ℕ → α)
    {T U : ℕ} (hTU : T ≤ U) :
    (∑ n ∈ Icc 1 T, g n) =
      ∑ j ∈ range (Nat.log 2 U + 1),
        ∑ n ∈ Icc 1 T ∩ liuPanDyadicShell j, g n := by
  classical
  symm
  calc
    (∑ j ∈ range (Nat.log 2 U + 1),
        ∑ n ∈ Icc 1 T ∩ liuPanDyadicShell j, g n) =
        ∑ j ∈ range (Nat.log 2 U + 1), ∑ n ∈ Icc 1 T,
          if n ∈ liuPanDyadicShell j then g n else 0 := by
            apply sum_congr rfl
            intro j hj
            rw [show Icc 1 T ∩ liuPanDyadicShell j =
              (Icc 1 T).filter (fun n => n ∈ liuPanDyadicShell j) by
                ext
                simp]
            rw [sum_filter]
    _ = ∑ n ∈ Icc 1 T, ∑ j ∈ range (Nat.log 2 U + 1),
          if n ∈ liuPanDyadicShell j then g n else 0 := by
            rw [sum_comm]
    _ = ∑ n ∈ Icc 1 T, g n := by
      apply sum_congr rfl
      intro n hn
      have hn0 : 0 < n := (mem_Icc.mp hn).1
      have hnU : n ≤ U := (mem_Icc.mp hn).2.trans hTU
      have hj : Nat.log 2 n ∈ range (Nat.log 2 U + 1) := by
        rw [mem_range]
        exact Nat.lt_succ_of_le (Nat.log_mono_right hnU)
      simp_rw [mem_liuPanDyadicShell_iff_log hn0]
      simp [hj]

theorem sum_range_succ_eq_sum_Icc_of_zero
    {α : Type*} [AddCommMonoid α] (g : ℕ → α) (T : ℕ)
    (hg : g 0 = 0) :
    (∑ n ∈ range (T + 1), g n) = ∑ n ∈ Icc 1 T, g n := by
  have hrange : range (T + 1) = insert 0 (Icc 1 T) := by
    ext n
    simp
    omega
  rw [hrange, sum_insert (by simp), hg, zero_add]

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

theorem norm_liuPanLogLambdaCoefficient_le_one (n : ℕ) :
    ‖liuPanLogLambdaCoefficient n‖ ≤ 1 := by
  rw [liuPanLogLambdaCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg vonMangoldt_nonneg (by
      rcases n with _ | n
      · simp
      exact Real.log_nonneg (by norm_num)))]
  rcases n with _ | _ | n
  · simp
  · simp
  · exact (div_le_one (Real.log_pos (by
      exact_mod_cast (by omega : 1 < n + 2)))).2
      ArithmeticFunction.vonMangoldt_le_log

/-- Primitive/Mobius dilation of a logarithmic von Mangoldt prefix. -/
theorem liuPanLogLambdaCharacterPrefix_eq_primitive_dilations
    {q : ℕ} [NeZero q] (t : ℕ) (χ : DirichletCharacter ℂ q) :
    liuPanLogLambdaCharacterPrefix t q χ =
      ∑ r ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius r : ℂ) *
          χ.primitiveCharacter (r : ZMod χ.conductor)) *
          ∑ v ∈ range (t / r + 1),
            liuPanLogLambdaCoefficient (r * v) *
              χ.primitiveCharacter (v : ZMod χ.conductor) := by
  unfold liuPanLogLambdaCharacterPrefix liuPanLogLambdaCoefficient
  exact characterPrefixSum_eq_sum_primitive_dilations
    (fun n => ((Λ n / Real.log (n : ℝ) : ℝ) : ℂ)) χ t

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

theorem liuPanSourceLogLambdaCharacterHyperbola_eq_primitive_dilations
    {q : ℕ} [NeZero q] (y X : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    liuPanSourceLogLambdaCharacterHyperbola y X q f χ =
      liuPanPrimitiveDilationLogLambdaHyperbola y X q f χ := by
  have houter :
      liuPanSourceLogLambdaCharacterHyperbola y X q f χ =
        ∑ a ∈ range (X + 1),
          (liuPanSourceZeroExtension f a *
            liuPanLogLambdaCharacterPrefix (y / a) q χ) *
            χ (a : ZMod q) := by
    unfold liuPanSourceLogLambdaCharacterHyperbola
    have hrange : range (X + 1) = insert 0 (Icc 1 X) := by
      ext a
      simp
      omega
    rw [hrange, sum_insert (by simp)]
    simp only [liuPanSourceZeroExtension, if_pos, zero_mul, zero_add]
    apply sum_congr rfl
    intro a ha
    rw [if_neg (by
      have := (mem_Icc.mp ha).1
      omega)]
    ring
  rw [houter, characterPrefixSum_eq_sum_primitive_dilations]
  unfold liuPanPrimitiveDilationLogLambdaHyperbola
  apply sum_congr rfl
  intro e he
  congr 1
  apply sum_congr rfl
  intro u hu
  rw [liuPanLogLambdaCharacterPrefix_eq_primitive_dilations]
  ring

/-! ## Low-conductor primitive Siegel--Walfisz interface -/

/-- The exact logarithmic von Mangoldt prefix after dilation by `r`, twisted by
a primitive character of level `d`. -/
noncomputable def liuPanPrimitiveLogLambdaDilationPrefix
    (t r d : ℕ) (ψ : DirichletCharacter ℂ d) : ℂ :=
  ∑ v ∈ range (t / r + 1),
    liuPanLogLambdaCoefficient (r * v) * ψ (v : ZMod d)

/-- The trivial global bound for a primitive dilated prefix.  It is the
short-prefix input in the low-conductor source transfer: importantly, its
length is the actual reduced prefix `t / r`, not the ambient parameter. -/
theorem norm_liuPanPrimitiveLogLambdaDilationPrefix_le
    (t r d : ℕ) (ψ : DirichletCharacter ℂ d) :
    ‖liuPanPrimitiveLogLambdaDilationPrefix t r d ψ‖ ≤
      ((t / r : ℕ) : ℝ) := by
  rw [liuPanPrimitiveLogLambdaDilationPrefix]
  rw [sum_range_succ_eq_sum_Icc_of_zero]
  · calc
      ‖∑ v ∈ Icc 1 (t / r),
          liuPanLogLambdaCoefficient (r * v) * ψ (v : ZMod d)‖ ≤
        ∑ v ∈ Icc 1 (t / r),
          ‖liuPanLogLambdaCoefficient (r * v) * ψ (v : ZMod d)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _v ∈ Icc 1 (t / r), (1 : ℝ) := by
        apply sum_le_sum
        intro v hv
        rw [norm_mul]
        exact (mul_le_mul
          (norm_liuPanLogLambdaCoefficient_le_one (r * v))
          (dirichletCharacter_norm_le_one d ψ (v : ZMod d))
          (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      _ = ((t / r : ℕ) : ℝ) := by simp
  · simp

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

/-- The low-conductor sum is exactly its two-sided primitive-dilation form,
before any norm or sourcewise triangle inequality. -/
theorem liuPanAggregateLogLambdaLowConductorSum_eq_primitive_dilations
    (D₀ y X q l : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorSum D₀ y X q l f =
      liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
        D₀ y X q l f := by
  classical
  by_cases hq : q = 0
  · simp [hq, liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum]
  · let _ : NeZero q := ⟨hq⟩
    unfold liuPanAggregateLogLambdaLowConductorSum
      liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
    rw [if_neg hq, if_neg hq]
    congr 1
    apply sum_congr rfl
    intro d hd
    by_cases hdD : d ≤ D₀
    · rw [if_pos hdD, if_pos hdD]
      by_cases hdq : d ∣ q
      · rw [dif_pos hdq, dif_pos hdq]
        apply sum_congr rfl
        intro ψ hψ
        rw [liuPanSourceLogLambdaCharacterHyperbola_eq_primitive_dilations]
      · simp [hdq]
    · simp [hdD]

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

/-- Reduced-residue and shared-endpoint maximum of the exact low-conductor
primitive-dilation sum. -/
noncomputable def liuPanAggregateLogLambdaLowPrimitiveDilationMaxL
    (D₀ y N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image fun l =>
      ‖liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
        D₀ y N q l f‖).max' (Finset.image_nonempty.mpr h)
  else 0

noncomputable def liuPanAggregateLogLambdaLowPrimitiveDilationMaxY
    (D₀ N q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (N + 1)).image fun y =>
    liuPanAggregateLogLambdaLowPrimitiveDilationMaxL D₀ y N q f).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The original squarefree `3^omega` modulus average, now with both
induced-character dilations visible in every summand. -/
noncomputable def liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage
    (D₀ N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanAggregateLogLambdaLowPrimitiveDilationMaxY D₀ N q f

theorem liuPanAggregateLogLambdaLowConductorMaxL_eq_primitive_dilations
    (D₀ y N q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorMaxL D₀ y N q f =
      liuPanAggregateLogLambdaLowPrimitiveDilationMaxL D₀ y N q f := by
  unfold liuPanAggregateLogLambdaLowConductorMaxL
    liuPanAggregateLogLambdaLowPrimitiveDilationMaxL
  simp_rw [liuPanAggregateLogLambdaLowConductorSum_eq_primitive_dilations]

theorem liuPanAggregateLogLambdaLowConductorMaxY_eq_primitive_dilations
    (D₀ N q : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateLogLambdaLowConductorMaxY D₀ N q f =
      liuPanAggregateLogLambdaLowPrimitiveDilationMaxY D₀ N q f := by
  unfold liuPanAggregateLogLambdaLowConductorMaxY
    liuPanAggregateLogLambdaLowPrimitiveDilationMaxY
  simp_rw [liuPanAggregateLogLambdaLowConductorMaxL_eq_primitive_dilations]

theorem liuMainPanAggregateLogLambdaLowConductorAverage_eq_primitive_dilations
    (D₀ N : ℕ) (f : ℕ → ℝ) (B : ℝ) :
    liuMainPanAggregateLogLambdaLowConductorAverage D₀ N f B =
      liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage D₀ N f B := by
  unfold liuMainPanAggregateLogLambdaLowConductorAverage
    liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage
  simp_rw [liuPanAggregateLogLambdaLowConductorMaxY_eq_primitive_dilations]

/-- Uniform finite Siegel--Walfisz input for every primitive conductor
`2 ≤ d ≤ D₀` and every Lambda-side dilation.  The saving is measured at the
actual reduced prefix `t / r`, so the estimate remains meaningful for short
prefixes; no estimate is asserted here. -/
def LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
    (N D₀ : ℕ) (A C : ℝ) : Prop :=
  0 < C ∧
    ∀ d ∈ Icc 2 D₀,
      ∀ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
        ∀ r t : ℕ, t ≤ N →
          let x := t / r
          ‖liuPanPrimitiveLogLambdaDilationPrefix t r d ψ‖ ≤
            C * x / Real.log (x + 2 : ℕ) ^ A

/-- The pointwise source-transfer input is the minimum of the short-prefix
trivial bound and the primitive Siegel--Walfisz bound, both at the same actual
reduced prefix. -/
theorem norm_liuPanPrimitiveLogLambdaDilationPrefix_le_min_of_siegelWalfisz
    {N D₀ : ℕ} {A Csw : ℝ}
    (hSW : LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
      N D₀ A Csw)
    {d : ℕ} (hd : d ∈ Icc 2 D₀)
    (ψ : DirichletCharacter ℂ d)
    (hψ : ψ ∈ liuPanPrimePowerPrimitiveCharacters d)
    (r t : ℕ) (ht : t ≤ N) :
    ‖liuPanPrimitiveLogLambdaDilationPrefix t r d ψ‖ ≤
      min ((t / r : ℕ) : ℝ)
        (Csw * (t / r : ℕ) /
          Real.log (t / r + 2 : ℕ) ^ A) := by
  apply le_min
  · exact norm_liuPanPrimitiveLogLambdaDilationPrefix_le t r d ψ
  · exact hSW.2 d hd ψ hψ r t ht

/-- In the short range the global prefix bound is available with no
Siegel--Walfisz input. -/
theorem norm_liuPanPrimitiveLogLambdaDilationPrefix_le_of_reduced_le
    {t r d L : ℕ} (htr : t / r ≤ L)
    (ψ : DirichletCharacter ℂ d) :
    ‖liuPanPrimitiveLogLambdaDilationPrefix t r d ψ‖ ≤ (L : ℝ) :=
  (norm_liuPanPrimitiveLogLambdaDilationPrefix_le t r d ψ).trans
    (by exact_mod_cast htr)

/-- The norm of the zero-extended actual Liu source is exactly its indicator
weight, including the totalized value at zero. -/
theorem norm_liuPanSourceZeroExtension_source_eq
    (N a : ℕ) :
    ‖liuPanSourceZeroExtension
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ =
        liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a := by
  by_cases ha : a = 0
  · subst a
    rw [liuPanSourceZeroExtension, if_pos rfl]
    simp only [norm_zero]
    symm
    rw [liuWeight_eq_zero_iff]
    intro h
    rcases h with ⟨p, hp, hprod⟩
    have hpos := liuWeightPairs_product_pos hp
    omega
  · rw [liuPanSourceZeroExtension, if_neg ha, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    exact liuWeight_nonneg _ _ _ _

/-- The actual Liu source has the required short-range mass bound. -/
theorem sum_norm_liuPanSourceZeroExtension_source_le_three_mul_rpow_two_thirds
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ a ∈ Icc 1 N,
      ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖) ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  simp_rw [norm_liuPanSourceZeroExtension_source_eq]
  exact sum_liuWeight_Icc_le_three_mul_rpow_two_thirds N
    (liuSourceZ10 N) (liuSourceY3 N) hN

/-- The actual Liu source has the required reciprocal mass bound for the
long reduced-prefix range. -/
theorem sum_norm_liuPanSourceZeroExtension_source_div_le_one_add_log
    (N : ℕ) :
    ∑ a ∈ Icc 1 N,
      ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ / a ≤
      1 + Real.log N := by
  simp_rw [norm_liuPanSourceZeroExtension_source_eq]
  exact sum_liuWeight_div_le_one_add_log N

/-- The finite triangle-inequality envelope of one primitive two-dilation
hyperbola.  It keeps the source dilation `e`, the Lambda dilation `r`, and the
actual common quotient `y / (e * u)` visible. -/
noncomputable def liuPanPrimitiveDilationLogLambdaHyperbolaNormEnvelope
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    ‖(ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)‖ *
    ∑ u ∈ range (X / e + 1),
      ‖liuPanSourceZeroExtension f (e * u) *
        χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
      ∑ r ∈ (q / χ.conductor).divisors,
        ‖(ArithmeticFunction.moebius r : ℂ) *
          χ.primitiveCharacter (r : ZMod χ.conductor)‖ *
        ‖liuPanPrimitiveLogLambdaDilationPrefix
          (y / (e * u)) r χ.conductor χ.primitiveCharacter‖

/-- The exact primitive hyperbola is bounded by its finite source/Lambda
envelope before any cofactor estimate.  This is the finite transfer which
permits the short/long choice to be made at
`(y / (e * u)) / r` in each summand. -/
theorem norm_liuPanPrimitiveDilationLogLambdaHyperbola_le_envelope
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) :
    ‖liuPanPrimitiveDilationLogLambdaHyperbola y X q f χ‖ ≤
      liuPanPrimitiveDilationLogLambdaHyperbolaNormEnvelope y X q f χ := by
  unfold liuPanPrimitiveDilationLogLambdaHyperbola
    liuPanPrimitiveDilationLogLambdaHyperbolaNormEnvelope
  calc
    ‖∑ e ∈ (q / χ.conductor).divisors,
        ((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
        ∑ u ∈ range (X / e + 1),
          (liuPanSourceZeroExtension f (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)) *
          ∑ r ∈ (q / χ.conductor).divisors,
            ((ArithmeticFunction.moebius r : ℂ) *
              χ.primitiveCharacter (r : ZMod χ.conductor)) *
            liuPanPrimitiveLogLambdaDilationPrefix
              (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ ≤
      ∑ e ∈ (q / χ.conductor).divisors,
        ‖((ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)) *
          ∑ u ∈ range (X / e + 1),
            (liuPanSourceZeroExtension f (e * u) *
              χ.primitiveCharacter (u : ZMod χ.conductor)) *
            ∑ r ∈ (q / χ.conductor).divisors,
              ((ArithmeticFunction.moebius r : ℂ) *
                χ.primitiveCharacter (r : ZMod χ.conductor)) *
              liuPanPrimitiveLogLambdaDilationPrefix
                (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left
      · calc
          ‖∑ u ∈ range (X / e + 1),
              (liuPanSourceZeroExtension f (e * u) *
                χ.primitiveCharacter (u : ZMod χ.conductor)) *
              ∑ r ∈ (q / χ.conductor).divisors,
                ((ArithmeticFunction.moebius r : ℂ) *
                  χ.primitiveCharacter (r : ZMod χ.conductor)) *
                liuPanPrimitiveLogLambdaDilationPrefix
                  (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ ≤
            ∑ u ∈ range (X / e + 1),
              ‖(liuPanSourceZeroExtension f (e * u) *
                χ.primitiveCharacter (u : ZMod χ.conductor)) *
                ∑ r ∈ (q / χ.conductor).divisors,
                  ((ArithmeticFunction.moebius r : ℂ) *
                    χ.primitiveCharacter (r : ZMod χ.conductor)) *
                  liuPanPrimitiveLogLambdaDilationPrefix
                    (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ :=
            norm_sum_le _ _
          _ ≤ _ := by
            apply sum_le_sum
            intro u hu
            rw [norm_mul]
            apply mul_le_mul_of_nonneg_left
            · calc
                ‖∑ r ∈ (q / χ.conductor).divisors,
                    ((ArithmeticFunction.moebius r : ℂ) *
                      χ.primitiveCharacter (r : ZMod χ.conductor)) *
                    liuPanPrimitiveLogLambdaDilationPrefix
                      (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ ≤
                  ∑ r ∈ (q / χ.conductor).divisors,
                    ‖((ArithmeticFunction.moebius r : ℂ) *
                      χ.primitiveCharacter (r : ZMod χ.conductor)) *
                      liuPanPrimitiveLogLambdaDilationPrefix
                        (y / (e * u)) r χ.conductor χ.primitiveCharacter‖ :=
                  norm_sum_le _ _
                _ = _ := by
                  apply sum_congr rfl
                  intro r hr
                  rw [norm_mul]
            · exact norm_nonneg _
      · exact norm_nonneg _

/-- The source/Lambda envelope after the pointwise short/long split at each
actual reduced prefix. -/
noncomputable def liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope
    (y X q : ℕ) (A Csw : ℝ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    ‖(ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)‖ *
    ∑ u ∈ range (X / e + 1),
      ‖liuPanSourceZeroExtension f (e * u) *
        χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
      ∑ r ∈ (q / χ.conductor).divisors,
        ‖(ArithmeticFunction.moebius r : ℂ) *
          χ.primitiveCharacter (r : ZMod χ.conductor)‖ *
        min (((y / (e * u)) / r : ℕ) : ℝ)
          (Csw * ((y / (e * u)) / r : ℕ) /
            Real.log ((y / (e * u)) / r + 2 : ℕ) ^ A)

/-- Uniform primitive Siegel--Walfisz input bounds every two-dilation
hyperbola by the split envelope.  The condition on `χ.primitiveCharacter` is
the exact primitive-character fact supplied by the conductor-fibre
regrouping. -/
theorem norm_liuPanPrimitiveDilationLogLambdaHyperbola_le_splitEnvelope
    {N D₀ : ℕ} {A Csw : ℝ} {y X q : ℕ} {f : ℕ → ℝ}
    {χ : DirichletCharacter ℂ q}
    (hSW : LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
      N D₀ A Csw)
    (hy : y ≤ N)
    (hd : χ.conductor ∈ Icc 2 D₀)
    (hψ : χ.primitiveCharacter ∈
      liuPanPrimePowerPrimitiveCharacters χ.conductor) :
    ‖liuPanPrimitiveDilationLogLambdaHyperbola y X q f χ‖ ≤
      liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope
        y X q A Csw f χ := by
  refine (norm_liuPanPrimitiveDilationLogLambdaHyperbola_le_envelope
    y X q f χ).trans ?_
  unfold liuPanPrimitiveDilationLogLambdaHyperbolaNormEnvelope
    liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope
  apply sum_le_sum
  intro e he
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro u hu
    apply mul_le_mul_of_nonneg_left
    · apply sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left
      exact norm_liuPanPrimitiveLogLambdaDilationPrefix_le_min_of_siegelWalfisz
        hSW hd χ.primitiveCharacter hψ r (y / (e * u))
        ((Nat.div_le_self _ _).trans hy)
      exact norm_nonneg _
    · exact norm_nonneg _
  · exact norm_nonneg _

/-- The logarithmic conductor range required by the low-conductor
Siegel--Walfisz regime. -/
def LiuPanLowConductorLogarithmicCutoffAt
    (D₀ : ℕ → ℕ) (K : ℝ) (N0 : ℕ) : Prop :=
  0 ≤ K ∧ ∀ N : ℕ, N0 ≤ N →
    (D₀ N : ℝ) ≤ Real.log (N + 2 : ℕ) ^ K

/-- The exact cofactor mass for reduced prefixes below the source-transfer
cutoff.  Both primitive dilations are retained as divisor counts. -/
noncomputable def liuPanLowConductorWeightedShortCofactorMass
    (D₀ Q : ℕ) : ℝ :=
  ∑ q ∈ range (Q + 1),
    if q = 0 then 0 else
      (liuPanPrimePowerModulusWeight q / Nat.totient q) *
        ∑ d ∈ Icc 2 q, if d ≤ D₀ then
          if d ∣ q then
            ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
              ((q / d).divisors.card : ℝ) *
                ((q / d).divisors.card : ℝ)
          else 0
        else 0

/-- The exact cofactor mass in the long reduced-prefix range: the outer
dilation contributes its divisor count, while the Lambda-side dilation retains
its reciprocal saving. -/
noncomputable def liuPanLowConductorWeightedLongCofactorMass
    (D₀ Q : ℕ) : ℝ :=
  ∑ q ∈ range (Q + 1),
    if q = 0 then 0 else
      (liuPanPrimePowerModulusWeight q / Nat.totient q) *
        ∑ d ∈ Icc 2 q, if d ≤ D₀ then
          if d ∣ q then
            ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
              ((q / d).divisors.card : ℝ) *
                ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹
          else 0
        else 0

/-- The finite source-transfer comparison after splitting every actual reduced
prefix `(y / (e * u)) / r` at the source cutoff.  Its two displayed masses are
purely finite cofactor bookkeeping; the preceding envelope theorem and the
actual Liu source mass/reciprocal-mass lemmas isolate the remaining comparison.
No saving at the ambient parameter `N` is postulated for short prefixes. -/
def LiuPanAggregateLowConductorSourceTransferBoundAt
    (D₀ : ℕ → ℕ) (R Csw B : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
        N (D₀ N) R Csw →
      liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage
          (D₀ N) N (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
        (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
          Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
            Real.log (N + 2 : ℕ) ^ R) *
          (liuPanLowConductorWeightedShortCofactorMass
            (D₀ N) (panModulusCutoff N B) +
          liuPanLowConductorWeightedLongCofactorMass
            (D₀ N) (panModulusCutoff N B))

/-- The only remaining low-conductor source-transfer input after the exact
primitive character regrouping: for one fixed conductor fibre and one fixed
primitive character, the split envelope is bounded by the displayed short/long
cofactor masses.  This is the smallest remaining finite source-transfer
obligation; the theorems below prove all residue, shared-`y`, and modulus
lifting around it. -/
def LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt
    (D₀ : ℕ → ℕ) (R Csw : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    ∀ q d : ℕ, d ∈ Icc 2 (D₀ N) → ∀ hdq : d ∣ q,
      ∀ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
      ∀ y : ℕ, y ≤ N →
        liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope y N q R Csw
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
          (DirichletCharacter.changeLevel hdq ψ) ≤
        (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
          Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
            Real.log (N + 2 : ℕ) ^ R) *
          ((((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ)) +
            ((q / d).divisors.card : ℝ) *
              ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)

/-- A fixed positive source dilation has no more mass than the full actual Liu
source. -/
private theorem liuPanSourceDilationMass_le
    (N e : ℕ) (he : 0 < e) :
    (∑ u ∈ range (N / e + 1),
      ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u)‖) ≤
      ∑ a ∈ Icc 1 N,
        ‖liuPanSourceZeroExtension
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ := by
  rw [sum_range_succ_eq_sum_Icc_of_zero]
  · have hinj : Set.InjOn (fun u : ℕ => e * u) (Icc 1 (N / e)) := by
      intro u hu v hv huv
      exact Nat.eq_of_mul_eq_mul_left he huv
    have hsum := Finset.sum_image
      (f := fun a => ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖) hinj
    rw [← hsum]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      rcases mem_image.mp ha with ⟨u, hu, rfl⟩
      rw [mem_Icc] at hu ⊢
      constructor
      · exact Nat.mul_pos he (by omega)
      · simpa [mul_comm] using Nat.mul_le_of_le_div e u N hu.2
    · intro a ha hnot
      exact norm_nonneg _
  · simp [liuPanSourceZeroExtension]

/-- The reciprocal mass also decreases after restricting to a fixed positive
source dilation. -/
private theorem liuPanSourceDilationReciprocalMass_le
    (N e : ℕ) (he : 0 < e) :
    (∑ u ∈ range (N / e + 1),
      ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u)‖ / (e * u)) ≤
      ∑ a ∈ Icc 1 N,
        ‖liuPanSourceZeroExtension
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ / a := by
  rw [sum_range_succ_eq_sum_Icc_of_zero]
  · have hinj : Set.InjOn (fun u : ℕ => e * u) (Icc 1 (N / e)) := by
      intro u hu v hv huv
      exact Nat.eq_of_mul_eq_mul_left he huv
    have hsum := Finset.sum_image
      (f := fun a => ‖liuPanSourceZeroExtension
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ / a) hinj
    calc
      _ = ∑ a ∈ (Icc 1 (N / e)).image (fun u => e * u),
          ‖liuPanSourceZeroExtension
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ / a := by
        simpa only [Nat.cast_mul] using hsum.symm
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          rcases mem_image.mp ha with ⟨u, hu, rfl⟩
          rw [mem_Icc] at hu ⊢
          constructor
          · exact Nat.mul_pos he (by omega)
          · simpa [mul_comm] using Nat.mul_le_of_le_div e u N hu.2
        · intro a ha hnot
          exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · simp [liuPanSourceZeroExtension]

/-- On the long range `N^(1/6) < x`, comparison of
`log (N + 2)` with `log (x + 2)` costs the honest factor `6^R`. -/
private theorem liuPanLongReducedPrefixSiegelWalfiszTerm_le
    {N y e u r : ℕ} {R Csw : ℝ}
    (hN : 3 ≤ N) (hy : y ≤ N) (hR : 0 < R) (hCsw : 0 < Csw)
    (hx : (N : ℝ) ^ (1 / 6 : ℝ) <
      (((y / (e * u)) / r : ℕ) : ℝ)) :
    Csw * (((y / (e * u)) / r : ℕ) : ℝ) /
          Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R ≤
      (Csw * (6 : ℝ) ^ R * N / Real.log (N + 2 : ℕ) ^ R) /
        (e * u) / r := by
  let x := (y / (e * u)) / r
  have hxpos : 0 < x := by
    have hroot : 0 < (N : ℝ) ^ (1 / 6 : ℝ) := by positivity
    exact_mod_cast hroot.trans hx
  have heu : 0 < e * u := by
    by_contra h
    have hzero : e * u = 0 := Nat.eq_zero_of_not_pos h
    simp [x, hzero] at hxpos
  have hr : 0 < r := by
    by_contra h
    have hzero : r = 0 := Nat.eq_zero_of_not_pos h
    simp [x, hzero] at hxpos
  have hNpos : (0 : ℝ) < N := by positivity
  have hroot_nonneg : 0 ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg hNpos.le _
  have hpow := Real.rpow_lt_rpow hroot_nonneg hx
    (by norm_num : (0 : ℝ) < 6)
  have hxpow : (N : ℝ) < (x : ℝ) ^ (6 : ℕ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ((N : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℝ) := by
        rw [← Real.rpow_mul hNpos.le]
        norm_num
      _ < (x : ℝ) ^ (6 : ℝ) := by simpa [x] using hpow
      _ = (x : ℝ) ^ (6 : ℕ) := Real.rpow_natCast _ _
  have hxpowNat : N < x ^ 6 := by exact_mod_cast hxpow
  have hNx : N + 2 ≤ (x + 2) ^ 6 := by
    have hstep : x ^ 6 < (x + 2) ^ 6 :=
      Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  have hlog6 : Real.log (N + 2 : ℕ) ≤
      6 * Real.log (x + 2 : ℕ) := by
    calc
      Real.log (N + 2 : ℕ) ≤ Real.log ((x + 2 : ℕ) ^ 6) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hNx)
      _ = 6 * Real.log (x + 2 : ℕ) := by
        rw [Real.log_pow]
        norm_num
  have hlogN : 0 < Real.log (N + 2 : ℕ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N + 2 by omega)
  have hbase : 0 < Real.log (N + 2 : ℕ) / 6 := by positivity
  have hlogCompare : Real.log (N + 2 : ℕ) / 6 ≤
      Real.log (x + 2 : ℕ) := by
    linarith
  have hdenomCompare :
      (Real.log (N + 2 : ℕ) / 6) ^ R ≤
        Real.log (x + 2 : ℕ) ^ R :=
    Real.rpow_le_rpow hbase.le hlogCompare hR.le
  have hxnum : (x : ℝ) ≤ ((N : ℝ) / (e * u)) / r := by
    dsimp [x]
    calc
      ((((y / (e * u)) / r : ℕ) : ℝ)) ≤
          ((y / (e * u) : ℕ) : ℝ) / r := Nat.cast_div_le
      _ ≤ ((y : ℝ) / (e * u)) / r := by
        apply div_le_div_of_nonneg_right
        · simpa only [Nat.cast_mul] using
            (Nat.cast_div_le (α := ℝ) (m := y) (n := e * u))
        · positivity
      _ ≤ ((N : ℝ) / (e * u)) / r := by
        gcongr
  calc
    Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R ≤
        Csw * (((N : ℝ) / (e * u)) / r) /
          (Real.log (N + 2 : ℕ) / 6) ^ R :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hxnum hCsw.le)
        (Real.rpow_pos_of_pos hbase _) hdenomCompare
    _ = (Csw * (6 : ℝ) ^ R * N / Real.log (N + 2 : ℕ) ^ R) /
        (e * u) / r := by
      rw [Real.div_rpow hlogN.le (by norm_num : (0 : ℝ) ≤ 6)]
      field_simp

/-- For fixed positive source and Lambda dilations, the actual Liu mass and
reciprocal mass control respectively the short and long reduced prefixes. -/
private theorem liuPanFixedDilationsSplitSum_le
    {N y e r q : ℕ} {R Csw : ℝ} (χ : DirichletCharacter ℂ q)
    (hN : 3 ≤ N) (hy : y ≤ N) (hR : 0 < R) (hCsw : 0 < Csw)
    (he : 0 < e) (hr : 0 < r) :
    (∑ u ∈ range (N / e + 1),
      ‖liuPanSourceZeroExtension
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
        χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
      min ((((y / (e * u)) / r : ℕ) : ℝ))
        (Csw * (((y / (e * u)) / r : ℕ) : ℝ) /
          Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R)) ≤
      3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        (Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
          Real.log (N + 2 : ℕ) ^ R) / r := by
  let W : ℕ → ℝ := fun u =>
    ‖liuPanSourceZeroExtension
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u)‖
  let K : ℝ :=
    Csw * (6 : ℝ) ^ R * N / Real.log (N + 2 : ℕ) ^ R
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hcut : 0 ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ ∑ u ∈ range (N / e + 1), (
        W u * (N : ℝ) ^ (1 / 6 : ℝ) +
          K * (W u / (e * u)) / r) := by
      apply sum_le_sum
      intro u hu
      let x := (y / (e * u)) / r
      have hsource :
          ‖liuPanSourceZeroExtension
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)‖ ≤ W u := by
        dsimp [W]
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left
          (dirichletCharacter_norm_le_one χ.conductor χ.primitiveCharacter
            (u : ZMod χ.conductor))
          (norm_nonneg _)).trans_eq (mul_one _)
      have hlogx : 0 < Real.log (x + 2 : ℕ) := by
        apply Real.log_pos
        have hx2 : (1 : ℕ) < x + 2 := by
          rw [Nat.add_comm]
          exact Nat.lt_add_right x (by norm_num)
        exact_mod_cast hx2
      have hmin : 0 ≤ min (x : ℝ)
          (Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R) := by
        apply le_min
        · exact Nat.cast_nonneg _
        · positivity
      calc
        ‖liuPanSourceZeroExtension
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
            min (x : ℝ)
              (Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R) ≤
            W u * min (x : ℝ)
              (Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R) :=
          mul_le_mul_of_nonneg_right hsource hmin
        _ ≤ W u * (N : ℝ) ^ (1 / 6 : ℝ) +
              K * (W u / (e * u)) / r := by
          by_cases hx : (x : ℝ) ≤ (N : ℝ) ^ (1 / 6 : ℝ)
          · apply le_add_of_le_of_nonneg
            · exact mul_le_mul_of_nonneg_left
                (min_le_left _ _ |>.trans hx) (norm_nonneg _)
            · positivity
          · have hx' : (N : ℝ) ^ (1 / 6 : ℝ) < (x : ℝ) :=
              lt_of_not_ge hx
            have hlong :=
              liuPanLongReducedPrefixSiegelWalfiszTerm_le
                hN hy hR hCsw hx'
            apply le_add_of_nonneg_of_le
            · positivity
            · calc
                W u * min (x : ℝ)
                    (Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R) ≤
                    W u *
                      (Csw * (x : ℝ) / Real.log (x + 2 : ℕ) ^ R) :=
                  mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
                _ ≤ W u * (K / (e * u) / r) :=
                  mul_le_mul_of_nonneg_left (by simpa [K, x] using hlong)
                    (norm_nonneg _)
                _ = K * (W u / (e * u)) / r := by ring
    _ = (∑ u ∈ range (N / e + 1), W u) *
          (N : ℝ) ^ (1 / 6 : ℝ) +
        K * (∑ u ∈ range (N / e + 1), W u / (e * u)) / r := by
      rw [sum_add_distrib, ← sum_mul, ← sum_div, ← mul_sum]
    _ ≤ (3 * (N : ℝ) ^ (2 / 3 : ℝ)) *
          (N : ℝ) ^ (1 / 6 : ℝ) +
        K * (1 + Real.log (N + 2 : ℕ)) / r := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
          ((liuPanSourceDilationMass_le N e he).trans
            (sum_norm_liuPanSourceZeroExtension_source_le_three_mul_rpow_two_thirds
              N (by omega)))
          hcut
      · apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ hK
          calc
            (∑ u ∈ range (N / e + 1), W u / (e * u)) ≤
                ∑ a ∈ Icc 1 N,
                  ‖liuPanSourceZeroExtension
                    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) a‖ / a := by
              simpa [W] using liuPanSourceDilationReciprocalMass_le N e he
            _ ≤ 1 + Real.log N :=
              sum_norm_liuPanSourceZeroExtension_source_div_le_one_add_log N
            _ ≤ 1 + Real.log (N + 2 : ℕ) := by
              gcongr
              exact_mod_cast (show N ≤ N + 2 by omega)
        · positivity
    _ = 3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        (Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
          Real.log (N + 2 : ℕ) ^ R) / r := by
      have hNpos : (0 : ℝ) < N := by positivity
      have hp :
          (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) =
            (N : ℝ) ^ (5 / 6 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      dsimp [K]
      calc
        3 * (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) +
            Csw * (6 : ℝ) ^ R * N / Real.log (N + 2 : ℕ) ^ R *
              (1 + Real.log (N + 2 : ℕ)) / r =
            3 * ((N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ)) +
              Csw * (6 : ℝ) ^ R * N / Real.log (N + 2 : ℕ) ^ R *
                (1 + Real.log (N + 2 : ℕ)) / r := by ring
        _ = _ := by rw [hp]; ring

/-- The finite local source transfer is unconditional once `R` and the
Siegel--Walfisz constant are positive.  Thus primitive Siegel--Walfisz is the
only analytic input left in the low-conductor lane. -/
theorem LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt.of_primitive_siegelWalfisz
    (D₀ : ℕ → ℕ) {R Csw : ℝ} (hR : 0 < R) (hCsw : 0 < Csw) :
    LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt D₀ R Csw 3 := by
  classical
  intro N hN q d hd hdq ψ hψ y hy
  by_cases hq0 : q = 0
  · subst q
    simp [liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope]
  let _ : NeZero q := ⟨hq0⟩
  let χ := DirichletCharacter.changeLevel hdq ψ
  have hprim : ψ.IsPrimitive := by
    simpa [liuPanPrimePowerPrimitiveCharacters] using hψ
  have hcond : χ.conductor = d := by
    rw [@DirichletCharacter.conductor_changeLevel
      ℂ _ d ψ q ⟨hq0⟩ hdq]
    exact (DirichletCharacter.isPrimitive_def ψ).mp hprim
  let short : ℝ := 3 * (N : ℝ) ^ (5 / 6 : ℝ)
  let long : ℝ :=
    Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
      Real.log (N + 2 : ℕ) ^ R
  have hshort : 0 ≤ short := by
    dsimp [short]
    positivity
  have hlong : 0 ≤ long := by
    dsimp [long]
    positivity
  have hcoefficient (a : ℕ) :
      ‖(ArithmeticFunction.moebius a : ℂ) *
        χ.primitiveCharacter (a : ZMod χ.conductor)‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul
      (moebius_complex_norm_le_one a)
      (dirichletCharacter_norm_le_one χ.conductor χ.primitiveCharacter
        (a : ZMod χ.conductor))
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hsplit_nonneg (t r : ℕ) :
      0 ≤ min ((t / r : ℕ) : ℝ)
        (Csw * (t / r : ℕ) / Real.log (t / r + 2 : ℕ) ^ R) := by
    apply le_min
    · exact Nat.cast_nonneg _
    · have hlog : 0 < Real.log (t / r + 2 : ℕ) := by
        apply Real.log_pos
        have hx2 : (1 : ℕ) < t / r + 2 := by
          rw [Nat.add_comm]
          exact Nat.lt_add_right (t / r) (by norm_num)
        exact_mod_cast hx2
      positivity
  unfold liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope
  calc
    (∑ e ∈ (q / χ.conductor).divisors,
        ‖(ArithmeticFunction.moebius e : ℂ) *
          χ.primitiveCharacter (e : ZMod χ.conductor)‖ *
        ∑ u ∈ range (N / e + 1),
          ‖liuPanSourceZeroExtension
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
          ∑ r ∈ (q / χ.conductor).divisors,
            ‖(ArithmeticFunction.moebius r : ℂ) *
              χ.primitiveCharacter (r : ZMod χ.conductor)‖ *
            min (((y / (e * u)) / r : ℕ) : ℝ)
              (Csw * ((y / (e * u)) / r : ℕ) /
                Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R)) ≤
      ∑ e ∈ (q / χ.conductor).divisors,
        ∑ u ∈ range (N / e + 1),
          ‖liuPanSourceZeroExtension
              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
          ∑ r ∈ (q / χ.conductor).divisors,
            min (((y / (e * u)) / r : ℕ) : ℝ)
              (Csw * ((y / (e * u)) / r : ℕ) /
                Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R) := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ ∑ u ∈ range (N / e + 1),
            ‖liuPanSourceZeroExtension
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
              χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
            ∑ r ∈ (q / χ.conductor).divisors,
              ‖(ArithmeticFunction.moebius r : ℂ) *
                χ.primitiveCharacter (r : ZMod χ.conductor)‖ *
              min (((y / (e * u)) / r : ℕ) : ℝ)
                (Csw * ((y / (e * u)) / r : ℕ) /
                  Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R) := by
          apply (mul_le_mul_of_nonneg_right (hcoefficient e) ?_).trans_eq
            (one_mul _)
          apply sum_nonneg
          intro u hu
          apply mul_nonneg (norm_nonneg _)
          apply sum_nonneg
          intro r hr
          exact mul_nonneg (norm_nonneg _)
            (hsplit_nonneg (y / (e * u)) r)
        _ ≤ _ := by
          apply sum_le_sum
          intro u hu
          apply mul_le_mul_of_nonneg_left
          · apply sum_le_sum
            intro r hr
            exact mul_le_of_le_one_left
              (hsplit_nonneg (y / (e * u)) r)
              (hcoefficient r)
          · exact norm_nonneg _
    _ ≤ ∑ e ∈ (q / χ.conductor).divisors,
        ∑ r ∈ (q / χ.conductor).divisors,
          ∑ u ∈ range (N / e + 1),
            ‖liuPanSourceZeroExtension
                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) (e * u) *
              χ.primitiveCharacter (u : ZMod χ.conductor)‖ *
            min (((y / (e * u)) / r : ℕ) : ℝ)
              (Csw * ((y / (e * u)) / r : ℕ) /
                Real.log ((y / (e * u)) / r + 2 : ℕ) ^ R) := by
      apply sum_le_sum
      intro e he
      simp_rw [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ e ∈ (q / χ.conductor).divisors,
        ∑ r ∈ (q / χ.conductor).divisors, (short + long / r) := by
      apply sum_le_sum
      intro e he
      have hepos : 0 < e := Nat.pos_of_mem_divisors he
      apply sum_le_sum
      intro r hr
      have hrpos : 0 < r := Nat.pos_of_mem_divisors hr
      simpa [short, long] using
        liuPanFixedDilationsSplitSum_le χ hN hy hR hCsw hepos hrpos
    _ = ((q / χ.conductor).divisors.card : ℝ) *
        (((q / χ.conductor).divisors.card : ℝ) * short +
          long * ∑ r ∈ (q / χ.conductor).divisors, (r : ℝ)⁻¹) := by
      rw [sum_const, nsmul_eq_mul]
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      simp_rw [div_eq_mul_inv]
      rw [← mul_sum]
    _ ≤ (short + long) *
        ((((q / χ.conductor).divisors.card : ℝ) *
            ((q / χ.conductor).divisors.card : ℝ)) +
          ((q / χ.conductor).divisors.card : ℝ) *
            ∑ r ∈ (q / χ.conductor).divisors, (r : ℝ)⁻¹) := by
      have hcard : 0 ≤ ((q / χ.conductor).divisors.card : ℝ) :=
        Nat.cast_nonneg _
      have hinv : 0 ≤
          ∑ r ∈ (q / χ.conductor).divisors, (r : ℝ)⁻¹ := by positivity
      nlinarith [mul_nonneg hshort hinv, mul_nonneg hlong hcard]
    _ = _ := by simp [short, long, hcond]

/-- A local split-envelope transfer on each primitive conductor fibre implies
the previous aggregate low-conductor source-transfer bound after restoring the
reduced-residue maximum, the shared `y` maximum, and the original modulus
average. -/
theorem LiuPanAggregateLowConductorSourceTransferBoundAt.of_local
    {D₀ : ℕ → ℕ} {R Csw B : ℝ} {N0 : ℕ}
    (hlocal :
      LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt D₀ R Csw N0) :
    LiuPanAggregateLowConductorSourceTransferBoundAt D₀ R Csw B N0 := by
  classical
  intro N hN hSW
  let S : ℝ :=
    3 * (N : ℝ) ^ (5 / 6 : ℝ) +
      Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
        Real.log (N + 2 : ℕ) ^ R
  have hS : 0 ≤ S := by
    have hlog : 0 < Real.log (N + 2 : ℕ) := by
      apply Real.log_pos
      exact_mod_cast (show 1 < N + 2 by omega)
    have hden : 0 < Real.log (N + 2 : ℕ) ^ R :=
      Real.rpow_pos_of_pos hlog R
    have hCsw : 0 ≤ Csw := hSW.1.le
    dsimp [S]
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hCsw (Real.rpow_nonneg (by norm_num) _))
            (by positivity))
          (by linarith))
        hden.le)
  unfold liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage
    liuPanLowConductorWeightedShortCofactorMass
    liuPanLowConductorWeightedLongCofactorMass
  calc
    ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          liuPanAggregateLogLambdaLowPrimitiveDilationMaxY (D₀ N) N q
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          (S * (if q = 0 then 0 else
            (Nat.totient q : ℝ)⁻¹ *
              ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                if hdq : d ∣ q then
                  ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                    ((((q / d).divisors.card : ℝ) *
                        ((q / d).divisors.card : ℝ)) +
                      ((q / d).divisors.card : ℝ) *
                        ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)
                else 0
              else 0)) := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · unfold liuPanAggregateLogLambdaLowPrimitiveDilationMaxY
        apply max'_le
        intro z hz
        rcases mem_image.mp hz with ⟨y, hy, rfl⟩
        unfold liuPanAggregateLogLambdaLowPrimitiveDilationMaxL
        let T := unitResidues q
        by_cases hT : T.Nonempty
        · dsimp only
          rw [dif_pos hT]
          apply max'_le
          intro w hw
          rcases mem_image.mp hw with ⟨l, hl, rfl⟩
          by_cases hq0 : q = 0
          · subst q
            simp at hl
          · have hphi_nat : 0 < Nat.totient q :=
              Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
            have hphi : 0 < (Nat.totient q : ℝ) := by
              exact_mod_cast hphi_nat
            have hsum :
                ‖liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
                    (D₀ N) y N q l
                    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))‖ ≤
                  S * ((Nat.totient q : ℝ)⁻¹ *
                    ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                      if hdq : d ∣ q then
                        ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                          ((((q / d).divisors.card : ℝ) *
                              ((q / d).divisors.card : ℝ)) +
                            ((q / d).divisors.card : ℝ) *
                              ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)
                      else 0
                    else 0) := by
              unfold liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum
              rw [if_neg hq0]
              calc
                ‖(Nat.totient q : ℂ)⁻¹ *
                    ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                      if hdq : d ∣ q then
                        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                          let χ := DirichletCharacter.changeLevel hdq ψ
                          star (χ (l : ZMod q)) *
                            liuPanPrimitiveDilationLogLambdaHyperbola y N q
                              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ
                      else 0
                    else 0‖ ≤
                  ‖(Nat.totient q : ℂ)⁻¹‖ *
                    ∑ d ∈ Icc 2 q, ‖if d ≤ D₀ N then
                      if hdq : d ∣ q then
                        ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                          let χ := DirichletCharacter.changeLevel hdq ψ
                          star (χ (l : ZMod q)) *
                            liuPanPrimitiveDilationLogLambdaHyperbola y N q
                              (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ
                      else 0
                    else 0‖ := by
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
                    (norm_nonneg _)
                _ ≤ (Nat.totient q : ℝ)⁻¹ *
                    ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                      if hdq : d ∣ q then
                        ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                          (S *
                            ((((q / d).divisors.card : ℝ) *
                                ((q / d).divisors.card : ℝ)) +
                              ((q / d).divisors.card : ℝ) *
                                ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹))
                      else 0
                    else 0 := by
                  rw [norm_inv, Complex.norm_natCast]
                  apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hphi.le)
                  apply sum_le_sum
                  intro d hd
                  by_cases hdD : d ≤ D₀ N
                  · simp only [if_pos hdD]
                    have hdDmem : d ∈ Icc 2 (D₀ N) := by
                      simpa using
                        (show 2 ≤ d ∧ d ≤ D₀ N from
                          ⟨(mem_Icc.mp hd).1, hdD⟩)
                    split_ifs with hdq
                    ·
                      calc
                        ‖∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                            let χ := DirichletCharacter.changeLevel hdq ψ
                            star (χ (l : ZMod q)) *
                              liuPanPrimitiveDilationLogLambdaHyperbola y N q
                                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ‖ ≤
                          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                            ‖star ((DirichletCharacter.changeLevel hdq ψ)
                                (l : ZMod q)) *
                              liuPanPrimitiveDilationLogLambdaHyperbola y N q
                                (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
                                (DirichletCharacter.changeLevel hdq ψ)‖ :=
                          norm_sum_le _ _
                        _ ≤ ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
                            S *
                              ((((q / d).divisors.card : ℝ) *
                                  ((q / d).divisors.card : ℝ)) +
                                ((q / d).divisors.card : ℝ) *
                                  ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹) := by
                          apply sum_le_sum
                          intro ψ hψ
                          let χ := DirichletCharacter.changeLevel hdq ψ
                          have hprim : ψ.IsPrimitive := by
                            simpa [liuPanPrimePowerPrimitiveCharacters] using hψ
                          have hcond : χ.conductor = d := by
                            rw [@DirichletCharacter.conductor_changeLevel
                              ℂ _ d ψ q ⟨hq0⟩ hdq]
                            exact (DirichletCharacter.isPrimitive_def ψ).mp hprim
                          have hdχ : χ.conductor ∈ Icc 2 (D₀ N) := by
                            simpa [χ, hcond] using hdDmem
                          have hψχ :
                              χ.primitiveCharacter ∈
                                liuPanPrimePowerPrimitiveCharacters χ.conductor := by
                            simpa [liuPanPrimePowerPrimitiveCharacters, χ] using
                              χ.primitiveCharacter_isPrimitive
                          calc
                            ‖star ((DirichletCharacter.changeLevel hdq ψ)
                                  (l : ZMod q)) *
                                liuPanPrimitiveDilationLogLambdaHyperbola y N q
                                  (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))
                                  (DirichletCharacter.changeLevel hdq ψ)‖ =
                                ‖star (χ (l : ZMod q)) *
                                  liuPanPrimitiveDilationLogLambdaHyperbola y N q
                                    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ‖ := by
                                  rfl
                            _ ≤ ‖liuPanPrimitiveDilationLogLambdaHyperbola y N q
                                  (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ‖ := by
                              rw [norm_mul]
                              exact (mul_le_mul
                                (by simpa [χ] using
                                  dirichletCharacter_norm_le_one q χ (l : ZMod q))
                                (le_rfl)
                                (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
                            _ ≤ liuPanPrimitiveDilationLogLambdaHyperbolaSplitEnvelope
                                  y N q R Csw
                                  (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ := by
                              exact
                                norm_liuPanPrimitiveDilationLogLambdaHyperbola_le_splitEnvelope
                                  hSW (by exact Nat.le_of_lt_succ (mem_range.mp hy))
                                  hdχ hψχ
                            _ ≤ S *
                                ((((q / d).divisors.card : ℝ) *
                                    ((q / d).divisors.card : ℝ)) +
                                  ((q / d).divisors.card : ℝ) *
                                    ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹) := by
                              simpa [S, χ] using
                                hlocal N hN q d hdDmem hdq ψ hψ y
                                  (Nat.le_of_lt_succ (mem_range.mp hy))
                        _ = ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                            (S *
                              ((((q / d).divisors.card : ℝ) *
                                  ((q / d).divisors.card : ℝ)) +
                                ((q / d).divisors.card : ℝ) *
                                  ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)) := by
                          simp [mul_left_comm]
                    · simp
                  · simp [hdD]
                _ = (Nat.totient q : ℝ)⁻¹ * (S *
                    ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                      if hdq : d ∣ q then
                        ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                          ((((q / d).divisors.card : ℝ) *
                              ((q / d).divisors.card : ℝ)) +
                            ((q / d).divisors.card : ℝ) *
                              ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)
                      else 0
                    else 0) := by
                  congr 1
                  rw [mul_sum]
                  apply sum_congr rfl
                  intro d hd
                  by_cases hdD : d ≤ D₀ N
                  · simp only [if_pos hdD]
                    by_cases hdq : d ∣ q
                    · simp only [dif_pos hdq]
                      ring
                    · simp [hdq]
                  · simp [hdD]
                _ = S * ((Nat.totient q : ℝ)⁻¹ *
                    ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                      if hdq : d ∣ q then
                       ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                         ((((q / d).divisors.card : ℝ) *
                             ((q / d).divisors.card : ℝ)) +
                           ((q / d).divisors.card : ℝ) *
                             ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)
                      else 0
                    else 0) := by
                  ring
            simpa [hq0] using hsum
        · dsimp only
          rw [dif_neg hT]
          by_cases hq0 : q = 0
          · simp [hq0]
          · rw [if_neg hq0]
            apply mul_nonneg hS
            apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            apply sum_nonneg
            intro d hd
            by_cases hdD : d ≤ D₀ N
            · rw [if_pos hdD]
              by_cases hdq : d ∣ q
              · simp only [dif_pos hdq]
                positivity
              · simp [hdq]
            · simp [hdD]
      · exact liuPanPrimePowerModulusWeight_nonneg q
    _ = S *
        (∑ q ∈ range (panModulusCutoff N B + 1),
          if q = 0 then 0 else
            (liuPanPrimePowerModulusWeight q / Nat.totient q) *
              ∑ d ∈ Icc 2 q, if d ≤ D₀ N then
                if d ∣ q then
                  ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                    ((((q / d).divisors.card : ℝ) *
                        ((q / d).divisors.card : ℝ)) +
                      ((q / d).divisors.card : ℝ) *
                        ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹)
                else 0
              else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      by_cases hq0 : q = 0
      · simp [hq0]
      · simp only [if_neg hq0, div_eq_mul_inv]
        ring_nf
        congr 1
    _ = S *
        (liuPanLowConductorWeightedShortCofactorMass
            (D₀ N) (panModulusCutoff N B) +
          liuPanLowConductorWeightedLongCofactorMass
            (D₀ N) (panModulusCutoff N B)) := by
      unfold liuPanLowConductorWeightedShortCofactorMass
        liuPanLowConductorWeightedLongCofactorMass
      apply congrArg (fun x : ℝ => S * x)
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      by_cases hq0 : q = 0
      · simp [hq0]
      · simp only [if_neg hq0]
        rw [← mul_add, ← sum_add_distrib]
        apply congrArg
        apply sum_congr rfl
        intro d hd
        by_cases hdD : d ≤ D₀ N
        · simp only [if_pos hdD]
          by_cases hdq : d ∣ q
          · simp only [if_pos hdq]
            ring
          · simp [hdq]
        · simp [hdD]


/-- The only remaining finite arithmetic bookkeeping in the low-conductor
lane: bound the displayed short and long squarefree `3^omega` cofactor masses
when the conductor cutoff is at most a fixed power of the logarithm. -/
def LiuPanLowConductorWeightedCofactorMassBoundAt
    (D₀ : ℕ → ℕ) (B Ccofactor Kcut Kcof : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    (D₀ N : ℝ) ≤ Real.log (N + 2 : ℕ) ^ Kcut →
      liuPanLowConductorWeightedShortCofactorMass
          (D₀ N) (panModulusCutoff N B) +
        liuPanLowConductorWeightedLongCofactorMass
          (D₀ N) (panModulusCutoff N B) ≤
        Ccofactor * Real.log (N + 2 : ℕ) ^ Kcof

/-- A squarefree Euler-product envelope for the two cofactor divisor factors.
The coefficient `12^ω(q)/φ(q)` is what remains after retaining the outer
`3^ω(q)` and bounding the two complementary squarefree divisor counts by
`2^ω(q)` each. -/
noncomputable def liuPanLowConductorCofactorEnvelopeMass (Q : ℕ) : ℝ :=
  ∑ q ∈ range (Q + 1),
    (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
      Nat.totient q

theorem liuPanLowConductorCofactorEnvelopeMass_nonneg (Q : ℕ) :
    0 ≤ liuPanLowConductorCofactorEnvelopeMass Q := by
  unfold liuPanLowConductorCofactorEnvelopeMass
  exact sum_nonneg fun q _ =>
    div_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _))
      (Nat.cast_nonneg _)

private theorem liuPanLowConductorCofactorEnvelope_term_squarefree
    (q : ℕ) (hq : Squarefree q) :
    (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
        Nat.totient q =
      ∏ p ∈ q.primeFactors, (12 : ℝ) / (p - 1) := by
  have hmu : (((moebius q : ℤ) : ℝ) ^ 2) = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  have hphi := totient_eq_prod_primeFactors_of_squarefree hq
  calc
    (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
        Nat.totient q =
      (∏ p ∈ q.primeFactors, (12 : ℝ)) /
        (∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ)) := by
          rw [hmu, ← prod_const, ← Nat.cast_prod, ← hphi]
          norm_num
    _ = ∏ p ∈ q.primeFactors, (12 : ℝ) / (p - 1) := by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
        (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      norm_num

private theorem liuPanLowConductorCofactorEnvelope_term_non_squarefree
    (q : ℕ) (hq : ¬ Squarefree q) :
    (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
        Nat.totient q = 0 := by
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  norm_num

/-- Subset expansion of the finite squarefree cofactor envelope. -/
theorem liuPanLowConductorCofactorEnvelopeMass_le_prod_one_add (Q : ℕ) :
    liuPanLowConductorCofactorEnvelopeMass Q ≤
      ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
        (1 + (24 : ℝ) / p) := by
  unfold liuPanLowConductorCofactorEnvelopeMass
  calc
    (∑ q ∈ range (Q + 1),
        (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
          Nat.totient q) =
      ∑ q ∈ (range (Q + 1)).filter Squarefree,
        (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
          Nat.totient q := by
        rw [sum_filter]
        apply sum_congr rfl
        intro q hq
        by_cases hsq : Squarefree q
        · simp [hsq]
        · simp [hsq]
    _ = ∑ q ∈ (range (Q + 1)).filter Squarefree,
        ∏ p ∈ q.primeFactors, (12 : ℝ) / (p - 1) := by
      apply sum_congr rfl
      intro q hq
      exact liuPanLowConductorCofactorEnvelope_term_squarefree q
        (mem_filter.mp hq).2
    _ ≤ ∑ q ∈ (range (Q + 1)).filter Squarefree,
        ∏ p ∈ q.primeFactors, (24 : ℝ) / p := by
      apply sum_le_sum
      intro q hq
      apply prod_le_prod
      · intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
        have hpm1 : 0 < (p : ℝ) - 1 := by linarith
        exact div_nonneg (by norm_num) hpm1.le
      · intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
        have hpm1 : 0 < (p : ℝ) - 1 := by linarith
        have hppos : 0 < (p : ℝ) := by positivity
        apply (div_le_div_iff₀ hpm1 hppos).2
        nlinarith
    _ ≤ ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
        (1 + (24 : ℝ) / p) := by
      exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
        (fun p => (24 : ℝ) / p) fun p hp =>
          div_nonneg (by norm_num) (Nat.cast_nonneg p)

/-- The squarefree cofactor envelope has a fixed unconditional logarithmic
growth.  This is only the finite Euler-product/Mertens estimate. -/
theorem liuPanLowConductorCofactorEnvelopeMass_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      liuPanLowConductorCofactorEnvelopeMass Q ≤
        C * (Real.log (Q + 2)) ^ (24 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ :=
    AnalyticNumberTheory.Mertens.mertensSecond_nat
  let K : ℝ :=
    |AnalyticNumberTheory.Mertens.mertensSecondConstant| +
      C₁ / Real.log 2
  let C : ℝ :=
    max (1 / (Real.log 2) ^ (24 : ℝ)) (Real.exp (24 * K))
  have hlog2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left
      (div_pos zero_lt_one (Real.rpow_pos_of_pos hlog2 24))
  refine ⟨C, hC, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 1
  · have hmass : liuPanLowConductorCofactorEnvelopeMass Q ≤ 1 := by
      calc
        liuPanLowConductorCofactorEnvelopeMass Q ≤
            ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
              (1 + (24 : ℝ) / p) :=
          liuPanLowConductorCofactorEnvelopeMass_le_prod_one_add Q
        _ = 1 := by
          rw [AnalyticNumberTheory.Mertens.primesUpTo_eq_empty_of_le_one hQ]
          simp
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlogpow :
        (Real.log 2) ^ (24 : ℝ) ≤
          (Real.log (Q + 2)) ^ (24 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlog2)
        (Real.log_le_log (by norm_num) (by exact_mod_cast hQ2))
        (by norm_num)
    calc
      liuPanLowConductorCofactorEnvelopeMass Q ≤ 1 := hmass
      _ = 1 / (Real.log 2) ^ (24 : ℝ) *
          (Real.log 2) ^ (24 : ℝ) := by
        field_simp [(Real.rpow_pos_of_pos hlog2 24).ne']
      _ ≤ 1 / (Real.log 2) ^ (24 : ℝ) *
          (Real.log (Q + 2)) ^ (24 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogpow
          (div_nonneg zero_le_one
            (Real.rpow_nonneg (le_of_lt hlog2) 24))
      _ ≤ C * (Real.log (Q + 2)) ^ (24 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (le_max_left (1 / (Real.log 2) ^ (24 : ℝ))
            (Real.exp (24 * K)))
          (Real.rpow_nonneg (Real.log_nonneg
            (by exact_mod_cast (show 1 ≤ Q + 2 by omega))) 24)
  · have hQ2 : 2 ≤ Q := by omega
    have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
    have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
    have hM' :
        |AnalyticNumberTheory.Mertens.primeReciprocalSum Q -
          (Real.log (Real.log (Q : ℝ)) +
            AnalyticNumberTheory.Mertens.mertensSecondConstant)| ≤
          C₁ / Real.log (Q : ℝ) :=
      hM Q hQ2
    have hpRS :
        AnalyticNumberTheory.Mertens.primeReciprocalSum Q ≤
          Real.log (Real.log (Q : ℝ)) + K := by
      have hupper :
          AnalyticNumberTheory.Mertens.primeReciprocalSum Q ≤
            Real.log (Real.log (Q : ℝ)) +
              AnalyticNumberTheory.Mertens.mertensSecondConstant +
                C₁ / Real.log (Q : ℝ) := by
          linarith [(abs_le.mp hM').2]
      have hconst :
          AnalyticNumberTheory.Mertens.mertensSecondConstant ≤
            |AnalyticNumberTheory.Mertens.mertensSecondConstant| :=
          le_abs_self _
      have hquot : C₁ / Real.log (Q : ℝ) ≤ C₁ / Real.log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hC₁) hlog2
          (Real.log_le_log (by norm_num) (by exact_mod_cast hQ2))
      dsimp [K]
      linarith
    have hsum :
        (∑ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
          (24 : ℝ) / p) =
          24 * AnalyticNumberTheory.Mertens.primeReciprocalSum Q := by
      unfold AnalyticNumberTheory.Mertens.primeReciprocalSum
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    have hlogle :
        (Real.log (Q : ℝ)) ^ (24 : ℝ) ≤
          (Real.log (Q + 2)) ^ (24 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlogQ)
        (Real.log_le_log (by positivity)
          (by exact_mod_cast (show Q ≤ Q + 2 by omega)))
        (by norm_num)
    have hu :
        ∀ p : ℕ, 0 ≤ (24 : ℝ) / p := fun p =>
          div_nonneg (by norm_num) (Nat.cast_nonneg p)
    calc
      liuPanLowConductorCofactorEnvelopeMass Q ≤
          ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
            (1 + (24 : ℝ) / p) :=
        liuPanLowConductorCofactorEnvelopeMass_le_prod_one_add Q
      _ ≤ Real.exp
          (∑ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
            (24 : ℝ) / p) :=
        Real.prod_one_add_le_exp_sum
          (AnalyticNumberTheory.Mertens.primesUpTo Q) hu
      _ = Real.exp
          (24 * AnalyticNumberTheory.Mertens.primeReciprocalSum Q) := by
        rw [hsum]
      _ ≤ Real.exp (24 * (Real.log (Real.log (Q : ℝ)) + K)) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hpRS (by norm_num))
      _ = Real.exp (24 * K) * (Real.log (Q : ℝ)) ^ (24 : ℝ) := by
        calc
          Real.exp (24 * (Real.log (Real.log (Q : ℝ)) + K)) =
              Real.exp (24 * Real.log (Real.log (Q : ℝ)) + 24 * K) := by
            congr 1
            ring
          _ = Real.exp (24 * Real.log (Real.log (Q : ℝ))) *
                Real.exp (24 * K) := by
            rw [Real.exp_add]
          _ = (Real.log (Q : ℝ)) ^ (24 : ℝ) * Real.exp (24 * K) := by
            rw [show 24 * Real.log (Real.log (Q : ℝ)) =
              Real.log (Real.log (Q : ℝ)) * 24 by ring,
              Real.exp_mul, Real.exp_log hlogQ]
          _ = Real.exp (24 * K) * (Real.log (Q : ℝ)) ^ (24 : ℝ) := by
            ring
      _ ≤ C * (Real.log (Q + 2)) ^ (24 : ℝ) := by
        exact mul_le_mul
          (le_max_right (1 / (Real.log 2) ^ (24 : ℝ))
            (Real.exp (24 * K))) hlogle
          (Real.rpow_nonneg (le_of_lt hlogQ) 24) (by positivity)

/-- A divisor of a squarefree modulus has no more divisors than the modulus
itself, hence at most `2^ω(q)`. -/
private theorem liuPanLowConductor_divisors_card_le_two_pow
    {q d : ℕ} (hq : Squarefree q) (hdq : d ∣ q) :
    ((q / d).divisors.card : ℝ) ≤ (2 : ℝ) ^ q.primeFactors.card := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    exact not_squarefree_zero hq
  have hsub : (q / d).divisors ⊆ q.divisors := by
    intro r hr
    rw [Nat.mem_divisors]
    exact ⟨(Nat.dvd_of_mem_divisors hr).trans (Nat.div_dvd_of_dvd hdq), hq0⟩
  have hcard : (q / d).divisors.card ≤ q.divisors.card := card_le_card hsub
  have hqcard : q.divisors.card = 2 ^ q.primeFactors.card := by
    rw [Nat.card_divisors hq0]
    calc
      (∏ x ∈ q.primeFactors, (q.factorization x + 1)) =
          ∏ x ∈ q.primeFactors, 2 := by
        apply prod_congr rfl
        intro p hp
        rw [Nat.factorization_eq_one_of_squarefree hq
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
      _ = 2 ^ q.primeFactors.card := by simp
  exact_mod_cast hcard.trans_eq hqcard

private theorem liuPanLowConductor_reciprocal_divisor_sum_le_card (n : ℕ) :
    (∑ r ∈ n.divisors, (r : ℝ)⁻¹) ≤ n.divisors.card := by
  calc
    (∑ r ∈ n.divisors, (r : ℝ)⁻¹) ≤ ∑ _r ∈ n.divisors, (1 : ℝ) := by
      apply sum_le_sum
      intro r hr
      exact inv_le_one_of_one_le₀ (by
        exact_mod_cast (Nat.pos_of_mem_divisors hr))
    _ = n.divisors.card := by simp

/-- The exact short cofactor fibre is bounded without maximizing `3^ω`: the
two divisor counts are retained until the squarefree outer modulus is fixed. -/
private theorem liuPanLowConductor_short_inner_le
    (D₀ q : ℕ) (hq : Squarefree q) :
    (∑ d ∈ Icc 2 q, (if d ≤ D₀ then
      if d ∣ q then ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
        ((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ) else 0
      else 0)) ≤
    (D₀ : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    exact not_squarefree_zero hq
  calc
    _ ≤ ∑ d ∈ Icc 2 q, (if d ≤ D₀ then
        (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 else 0) := by
      apply sum_le_sum
      intro d hd
      by_cases hdD : d ≤ D₀
      · simp only [hdD, if_true]
        by_cases hdq : d ∣ q
        · simp only [hdq, if_true]
          have hd2 : 2 ≤ d := (mem_Icc.mp hd).1
          let _ : NeZero d := ⟨by omega⟩
          have hchar : ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) ≤ D₀ := by
            exact_mod_cast
              (liuPanPrimePowerPrimitiveCharacters_card_le_totient d).trans
                ((Nat.totient_le d).trans hdD)
          have htau := liuPanLowConductor_divisors_card_le_two_pow hq hdq
          have hτ : 0 ≤ ((q / d).divisors.card : ℝ) := Nat.cast_nonneg _
          have hW : 0 ≤ (2 : ℝ) ^ q.primeFactors.card := pow_nonneg (by norm_num) _
          have hD : 0 ≤ (D₀ : ℝ) := Nat.cast_nonneg _
          calc
            ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
                ((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ) ≤
              (D₀ : ℝ) * ((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hchar hτ) hτ
            _ ≤ (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) *
                ((q / d).divisors.card : ℝ) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left htau hD) hτ
            _ ≤ (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) *
                ((2 : ℝ) ^ q.primeFactors.card) :=
                mul_le_mul_of_nonneg_left htau (mul_nonneg hD hW)
            _ = (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by ring
        · simp only [hdq, if_false]
          exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      · simp only [hdD, if_false]
        norm_num
    _ = ∑ d ∈ (Icc 2 q).filter (fun d => d ≤ D₀),
        (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
      rw [sum_filter]
    _ ≤ ∑ _d ∈ Icc 1 D₀,
        (D₀ : ℝ) * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        rw [mem_filter, mem_Icc] at hd
        simp only [mem_Icc]
        omega
      · intro d hd hnot
        positivity
    _ = (D₀ : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
      rw [sum_const, Nat.card_Icc]
      norm_num
      ring

/-- The reciprocal-divisor fibre is no larger than the short divisor-square
fibre, because every positive divisor has reciprocal at most one. -/
private theorem liuPanLowConductor_long_inner_le
    (D₀ q : ℕ) (hq : Squarefree q) :
    (∑ d ∈ Icc 2 q, (if d ≤ D₀ then
      if d ∣ q then ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
        ((q / d).divisors.card : ℝ) *
          ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹ else 0
      else 0)) ≤
    (D₀ : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
  calc
    _ ≤ ∑ d ∈ Icc 2 q, (if d ≤ D₀ then
        if d ∣ q then ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
          ((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ) else 0
        else 0) := by
      apply sum_le_sum
      intro d hd
      by_cases hdD : d ≤ D₀
      · simp only [hdD, if_true]
        by_cases hdq : d ∣ q
        · simp only [hdq, if_true]
          exact mul_le_mul_of_nonneg_left
            (liuPanLowConductor_reciprocal_divisor_sum_le_card (q / d))
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        · simp [hdq]
      · simp [hdD]
    _ ≤ _ := liuPanLowConductor_short_inner_le D₀ q hq

/-- Restoring the squarefree outer weight turns the two divisor-count factors
into exactly the coefficient `12^ω(q)` of the envelope. -/
private theorem liuPanLowConductor_weighted_inner_le
    (D₀ q : ℕ) (hq : Squarefree q) {x : ℝ}
    (hx : x ≤ (D₀ : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2) :
    (liuPanPrimePowerModulusWeight q / Nat.totient q) * x ≤
      (D₀ : ℝ) ^ 2 *
        ((((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
          Nat.totient q) := by
  have hmu : (((moebius q : ℤ) : ℝ) ^ 2) = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  have hphi : 0 ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
  have hthree : 0 ≤ (3 : ℝ) ^ q.primeFactors.card :=
    pow_nonneg (by norm_num) _
  calc
    (liuPanPrimePowerModulusWeight q / Nat.totient q) * x ≤
        (liuPanPrimePowerModulusWeight q / Nat.totient q) *
          ((D₀ : ℝ) ^ 2 * ((2 : ℝ) ^ q.primeFactors.card) ^ 2) := by
      apply mul_le_mul_of_nonneg_left hx
      unfold liuPanPrimePowerModulusWeight
      rw [hmu]
      simpa using div_nonneg hthree hphi
    _ = (D₀ : ℝ) ^ 2 *
        ((((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
          Nat.totient q) := by
      unfold liuPanPrimePowerModulusWeight
      rw [hmu]
      have h12 : (12 : ℝ) ^ q.primeFactors.card =
          (3 : ℝ) ^ q.primeFactors.card *
            ((2 : ℝ) ^ q.primeFactors.card) ^ 2 := by
        rw [show (12 : ℝ) = 3 * 2 ^ 2 by norm_num, mul_pow]
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [h12]
      ring

/-- Both exact cofactor masses are bounded by the same finite squarefree
Euler-product envelope, with the conductor range counted only after the
primitive-character bound has been applied. -/
theorem liuPanLowConductorWeightedCofactorMasses_le_envelope
    (D₀ Q : ℕ) :
    liuPanLowConductorWeightedShortCofactorMass D₀ Q +
      liuPanLowConductorWeightedLongCofactorMass D₀ Q ≤
      2 * (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q := by
  have hshort :
      liuPanLowConductorWeightedShortCofactorMass D₀ Q ≤
        (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q := by
    unfold liuPanLowConductorWeightedShortCofactorMass
      liuPanLowConductorCofactorEnvelopeMass
    calc
      (∑ q ∈ range (Q + 1), if q = 0 then 0 else
        (liuPanPrimePowerModulusWeight q / Nat.totient q) *
          ∑ d ∈ Icc 2 q, if d ≤ D₀ then
            if d ∣ q then ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
              ((q / d).divisors.card : ℝ) * ((q / d).divisors.card : ℝ)
            else 0
          else 0) ≤
        ∑ q ∈ range (Q + 1), if q = 0 then 0 else
          if Squarefree q then
            (D₀ : ℝ) ^ 2 *
              ((((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
                Nat.totient q)
          else 0 := by
          apply sum_le_sum
          intro q hq
          by_cases hq0 : q = 0
          · simp [hq0]
          by_cases hsq : Squarefree q
          · simp only [if_neg hq0, if_pos hsq]
            exact liuPanLowConductor_weighted_inner_le D₀ q hsq
              (liuPanLowConductor_short_inner_le D₀ q hsq)
          · simp [hsq, liuPanPrimePowerModulusWeight_eq_zero_of_not_squarefree hsq]
      _ = (D₀ : ℝ) ^ 2 *
          ∑ q ∈ range (Q + 1),
            (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
              Nat.totient q := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q hq
          by_cases hq0 : q = 0
          · simp [hq0]
          by_cases hsq : Squarefree q
          · simp [hq0, hsq]
          · rw [liuPanLowConductorCofactorEnvelope_term_non_squarefree q hsq]
            simp [hq0, hsq]
  have hlong :
      liuPanLowConductorWeightedLongCofactorMass D₀ Q ≤
        (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q := by
    unfold liuPanLowConductorWeightedLongCofactorMass
      liuPanLowConductorCofactorEnvelopeMass
    calc
      (∑ q ∈ range (Q + 1), if q = 0 then 0 else
        (liuPanPrimePowerModulusWeight q / Nat.totient q) *
          ∑ d ∈ Icc 2 q, if d ≤ D₀ then
            if d ∣ q then ((liuPanPrimePowerPrimitiveCharacters d).card : ℝ) *
              ((q / d).divisors.card : ℝ) *
                ∑ r ∈ (q / d).divisors, (r : ℝ)⁻¹
            else 0
          else 0) ≤
        ∑ q ∈ range (Q + 1), if q = 0 then 0 else
          if Squarefree q then
            (D₀ : ℝ) ^ 2 *
              ((((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
                Nat.totient q)
          else 0 := by
          apply sum_le_sum
          intro q hq
          by_cases hq0 : q = 0
          · simp [hq0]
          by_cases hsq : Squarefree q
          · simp only [if_neg hq0, if_pos hsq]
            exact liuPanLowConductor_weighted_inner_le D₀ q hsq
              (liuPanLowConductor_long_inner_le D₀ q hsq)
          · simp [hsq, liuPanPrimePowerModulusWeight_eq_zero_of_not_squarefree hsq]
      _ = (D₀ : ℝ) ^ 2 *
          ∑ q ∈ range (Q + 1),
            (((moebius q : ℤ) : ℝ) ^ 2) * (12 : ℝ) ^ q.primeFactors.card /
              Nat.totient q := by
          rw [mul_sum]
          apply sum_congr rfl
          intro q hq
          by_cases hq0 : q = 0
          · simp [hq0]
          by_cases hsq : Squarefree q
          · simp [hq0, hsq]
          · rw [liuPanLowConductorCofactorEnvelope_term_non_squarefree q hsq]
            simp [hq0, hsq]
  calc
    _ ≤ (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q +
        (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q :=
      add_le_add hshort hlong
    _ = 2 * (D₀ : ℝ) ^ 2 * liuPanLowConductorCofactorEnvelopeMass Q := by
      ring

/-- The finite weighted cofactor bookkeeping is unconditional.  It uses only
the stated logarithmic conductor cutoff; the Euler-product estimate is the
finite Mertens bound above, not a Siegel--Walfisz or BV input. -/
theorem exists_liuPanLowConductorWeightedCofactorMassBoundAt
    (D₀ : ℕ → ℕ) (B Kcut : ℝ) (hB : 0 ≤ B) (_hKcut : 0 ≤ Kcut) :
    ∃ Ccofactor : ℝ, 0 < Ccofactor ∧
      LiuPanLowConductorWeightedCofactorMassBoundAt
        D₀ B Ccofactor Kcut (2 * Kcut + 24) 3 := by
  obtain ⟨Cenv, hCenv, henv⟩ :=
    liuPanLowConductorCofactorEnvelopeMass_le_polylog
  let Ccofactor : ℝ := 2 * Cenv * (2 : ℝ) ^ (24 : ℝ)
  have htwo : 0 < (2 : ℝ) ^ (24 : ℝ) := by positivity
  have hCcofactor : 0 < Ccofactor := by
    dsimp [Ccofactor]
    positivity
  refine ⟨Ccofactor, hCcofactor, ?_⟩
  intro N hN hD
  let Q := panModulusCutoff N B
  let L : ℝ := Real.log (N + 2 : ℕ)
  have hLpos : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    exact_mod_cast (show 1 < N + 2 by omega)
  have hLnonneg : 0 ≤ L := hLpos.le
  have hDsq : (D₀ N : ℝ) ^ 2 ≤ L ^ (2 * Kcut) := by
    calc
      (D₀ N : ℝ) ^ 2 ≤ (L ^ Kcut) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by simpa [L] using hD) 2
      _ = L ^ (2 * Kcut) := by
        calc
          (L ^ Kcut) ^ 2 = (L ^ Kcut) ^ (2 : ℝ) :=
            (Real.rpow_natCast (L ^ Kcut) 2).symm
          _ = L ^ (Kcut * 2) :=
            (Real.rpow_mul hLnonneg Kcut 2).symm
          _ = L ^ (2 * Kcut) := by
            congr 1
            ring
  have hcut :
      Real.log (Q + 2 : ℕ) ≤ 2 * L := by
    have hcut' := liuPanPrimePower_cutoff_log_add_two_le_two_mul_log
      N B hN hB
    have hlog :
        Real.log (N : ℝ) ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by positivity)
        (by exact_mod_cast (show N ≤ N + 2 by omega))
    exact hcut'.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))
  have hQlog_nonneg : 0 ≤ Real.log (Q + 2 : ℕ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q + 2 by omega))
  have henv' :
      liuPanLowConductorCofactorEnvelopeMass Q ≤
        Cenv * ((2 : ℝ) ^ (24 : ℝ) * L ^ (24 : ℝ)) := by
    calc
      liuPanLowConductorCofactorEnvelopeMass Q ≤
          Cenv * (Real.log (Q + 2 : ℕ)) ^ (24 : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using henv Q
      _ ≤ Cenv * (2 * L) ^ (24 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hQlog_nonneg hcut (by norm_num)) hCenv.le
      _ = Cenv * ((2 : ℝ) ^ (24 : ℝ) * L ^ (24 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hLnonneg]
  calc
    liuPanLowConductorWeightedShortCofactorMass
          (D₀ N) (panModulusCutoff N B) +
        liuPanLowConductorWeightedLongCofactorMass
          (D₀ N) (panModulusCutoff N B) ≤
      2 * (D₀ N : ℝ) ^ 2 *
        liuPanLowConductorCofactorEnvelopeMass Q := by
          simpa [Q] using liuPanLowConductorWeightedCofactorMasses_le_envelope
            (D₀ N) Q
    _ ≤ 2 * L ^ (2 * Kcut) *
        (Cenv * ((2 : ℝ) ^ (24 : ℝ) * L ^ (24 : ℝ))) := by
          have hMnonneg : 0 ≤ liuPanLowConductorCofactorEnvelopeMass Q :=
            liuPanLowConductorCofactorEnvelopeMass_nonneg Q
          have hleftnonneg : 0 ≤ 2 * L ^ (2 * Kcut) :=
            mul_nonneg (by norm_num) (Real.rpow_nonneg hLnonneg _)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hDsq (by norm_num)) henv'
            hMnonneg hleftnonneg
    _ = Ccofactor * L ^ (2 * Kcut + 24) := by
      dsimp [Ccofactor]
      rw [Real.rpow_add hLpos]
      ring

/-- A uniform primitive Siegel--Walfisz estimate, the exact weighted cofactor
transfer, and the final scalar comparison imply the existing low-conductor
source-family bound. -/
theorem LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt.of_primitive
    {D₀ : ℕ → ℕ} {A C B R Csw Ccofactor Kcut Kcof : ℝ} {N0 : ℕ}
    (hSW : ∀ N : ℕ, N0 ≤ N →
      LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
        N (D₀ N) R Csw)
    (hlocal :
      LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt
        D₀ R Csw N0)
    (hcofactor :
      LiuPanLowConductorWeightedCofactorMassBoundAt
        D₀ B Ccofactor Kcut Kcof N0)
    (hcutoff : LiuPanLowConductorLogarithmicCutoffAt D₀ Kcut N0)
    (hscale : ∀ N : ℕ, N0 ≤ N →
      (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
          Real.log (N + 2 : ℕ) ^ R) *
          (Ccofactor * Real.log (N + 2 : ℕ) ^ Kcof) ≤
        C * N / Real.log N ^ A) :
    LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt
      D₀ A C B N0 := by
  have hsource :
      LiuPanAggregateLowConductorSourceTransferBoundAt
        D₀ R Csw B N0 :=
    LiuPanAggregateLowConductorSourceTransferBoundAt.of_local hlocal
  intro N hN
  rw [liuMainPanAggregateLogLambdaLowConductorAverage_eq_primitive_dilations]
  calc
    liuMainPanAggregateLogLambdaLowPrimitiveDilationAverage
        (D₀ N) N (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
          Real.log (N + 2 : ℕ) ^ R) *
          (liuPanLowConductorWeightedShortCofactorMass
            (D₀ N) (panModulusCutoff N B) +
          liuPanLowConductorWeightedLongCofactorMass
            (D₀ N) (panModulusCutoff N B)) :=
      hsource N hN (hSW N hN)
    _ ≤ (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
          Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
            Real.log (N + 2 : ℕ) ^ R) *
          (Ccofactor * Real.log (N + 2 : ℕ) ^ Kcof) := by
      apply mul_le_mul_of_nonneg_left
        (hcofactor N hN (hcutoff.2 N hN))
      have hCsw : 0 ≤ Csw := (hSW N hN).1.le
      positivity
    _ ≤ C * N / Real.log N ^ A := hscale N hN

/-- A source-family primitive Siegel--Walfisz producer at one conductor cutoff.
The logarithmic cutoff exponent is chosen *before* the arbitrary saving `R`.
This order is essential: the low-conductor endpoint must choose `R` with enough
slack after seeing the fixed cutoff exponent, rather than allowing the cutoff
exponent to depend circularly on that choice. -/
def LiuPanPrimitiveLogLambdaDilationSiegelWalfiszProducer
    (D₀ : ℕ → ℕ) : Prop :=
  ∃ Kcut : ℝ, 0 ≤ Kcut ∧ ∀ R : ℝ, 0 < R →
    ∃ Csw : ℝ, 0 < Csw ∧ ∃ N0 : ℕ,
      LiuPanLowConductorLogarithmicCutoffAt D₀ Kcut N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          LiuPanPrimitiveLogLambdaDilationSiegelWalfiszBoundAt
            N (D₀ N) R Csw

/-- The eventual low-conductor estimate, uniformly as a source family. -/
def LiuMainPanAggregateLowConductorSiegelWalfiszSourceFamilyBound
    (D₀ : ℕ → ℕ) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ,
      LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt D₀ A C B N0

/-- The short `N^(5/6)` term and the shifted-log Siegel--Walfisz term both
absorb the finite cofactor loss `log(N+2)^(2*Kcut+24)`. -/
theorem exists_liuPanLowConductorSiegelWalfiszScalarBoundAt
    (A Csw Ccofactor Kcut : ℝ)
    (hA : 0 < A) (hCsw : 0 < Csw) (hCcofactor : 0 < Ccofactor)
    (hKcut : 0 ≤ Kcut) :
    let Kcof := 2 * Kcut + 24
    let R := A + Kcof + 2
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        Csw * (6 : ℝ) ^ R * N * (1 + Real.log (N + 2 : ℕ)) /
          Real.log (N + 2 : ℕ) ^ R) *
          (Ccofactor * Real.log (N + 2 : ℕ) ^ Kcof) ≤
        C * N / Real.log N ^ A := by
  dsimp only
  let Kcof : ℝ := 2 * Kcut + 24
  let R : ℝ := A + Kcof + 2
  let Cshort : ℝ := 3 * Ccofactor * (2 : ℝ) ^ Kcof
  let Clong : ℝ := 2 * Csw * (6 : ℝ) ^ R * Ccofactor
  let C : ℝ := Cshort + Clong
  have hKcof : 0 ≤ Kcof := by
    dsimp [Kcof]
    linarith
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hCshort : 0 < Cshort := by
    dsimp [Cshort]
    positivity
  have hClong : 0 < Clong := by
    dsimp [Clong]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hreal : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log x ^ (A + Kcof) ≤ x ^ (1 / 6 : ℝ) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop (A + Kcof)
      (by norm_num : (0 : ℝ) < 1 / 6)).bound (show 0 < (1 : ℝ) by norm_num)
    filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ x) _),
      one_mul] at hx
    exact hx
  have hnat : ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ (A + Kcof) ≤ (N : ℝ) ^ (1 / 6 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hreal
  rcases Filter.eventually_atTop.mp hnat with ⟨N1, hN1⟩
  refine ⟨C, hC, max N1 3, ?_⟩
  intro N hN
  have hN1' : N1 ≤ N := (le_max_left N1 3).trans hN
  have hN3 : 3 ≤ N := (le_max_right N1 3).trans hN
  let L : ℝ := Real.log (N + 2 : ℕ)
  let l : ℝ := Real.log N
  have hNpos : (0 : ℝ) < N := by positivity
  have hlpos : 0 < l := by
    dsimp [l]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlone : 1 ≤ l := by
    dsimp [l]
    apply (Real.le_log_iff_exp_le hNpos).2
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN3)
  have hLpos : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    exact_mod_cast (show 1 < N + 2 by omega)
  have hLle : L ≤ 2 * l := by
    dsimp [L, l]
    have hmul : N + 2 ≤ N * N := by nlinarith
    calc
      Real.log (N + 2 : ℕ) ≤ Real.log (N * N : ℕ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hmul)
      _ = 2 * Real.log N := by
        rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
        ring
  have hlL : l ≤ L := by
    dsimp [l, L]
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast (show N ≤ N + 2 by omega))
  have hLpow : L ^ Kcof ≤ (2 : ℝ) ^ Kcof * l ^ Kcof := by
    calc
      L ^ Kcof ≤ (2 * l) ^ Kcof :=
        Real.rpow_le_rpow hLpos.le hLle hKcof
      _ = (2 : ℝ) ^ Kcof * l ^ Kcof := by
        rw [Real.mul_rpow (by norm_num) hlpos.le]
  have hlpowprod : l ^ Kcof * l ^ A = l ^ (A + Kcof) := by
    rw [← Real.rpow_add hlpos]
    congr 1
    ring
  have hNpow :
      (N : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  have hshort :
      (3 * (N : ℝ) ^ (5 / 6 : ℝ)) * (Ccofactor * L ^ Kcof) ≤
        Cshort * N / l ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlpos A)]
    calc
      (3 * (N : ℝ) ^ (5 / 6 : ℝ) * (Ccofactor * L ^ Kcof)) * l ^ A ≤
          (3 * (N : ℝ) ^ (5 / 6 : ℝ) *
            (Ccofactor * ((2 : ℝ) ^ Kcof * l ^ Kcof))) * l ^ A := by
        gcongr
      _ = Cshort * (N : ℝ) ^ (5 / 6 : ℝ) * (l ^ Kcof * l ^ A) := by
        dsimp only [Cshort]
        ring
      _ = Cshort * (N : ℝ) ^ (5 / 6 : ℝ) * l ^ (A + Kcof) := by
        rw [hlpowprod]
      _ ≤ Cshort * (N : ℝ) ^ (5 / 6 : ℝ) * (N : ℝ) ^ (1 / 6 : ℝ) := by
        gcongr
        exact hN1 N hN1'
      _ = Cshort * ((N : ℝ) ^ (5 / 6 : ℝ) *
          (N : ℝ) ^ (1 / 6 : ℝ)) := by ring
      _ = Cshort * N := by rw [hNpow]
  have hlogA : l ^ A ≤ L ^ A :=
    Real.rpow_le_rpow hlpos.le hlL hA.le
  have hKA : L ^ Kcof * L ^ A = L ^ (Kcof + A) :=
    (Real.rpow_add hLpos Kcof A).symm
  have hratio : (1 + L) / L ^ R * L ^ Kcof * l ^ A ≤ 2 := by
    calc
      (1 + L) / L ^ R * L ^ Kcof * l ^ A ≤
          (1 + L) / L ^ R * L ^ Kcof * L ^ A := by
        gcongr
      _ = (1 + L) / L ^ R * (L ^ Kcof * L ^ A) := by ring
      _ = (1 + L) / L ^ R * L ^ (Kcof + A) := by rw [hKA]
      _ = (1 + L) * (L ^ (Kcof + A) / L ^ R) := by ring
      _ = (1 + L) * L ^ (Kcof + A - R) := by
        rw [Real.rpow_sub hLpos]
      _ = (1 + L) * L ^ (-2 : ℝ) := by
        congr 2
        dsimp [R]
        ring
      _ = (1 + L) / L ^ (2 : ℕ) := by
        rw [Real.rpow_neg hLpos.le]
        norm_num [div_eq_mul_inv]
      _ ≤ 2 := by
        rw [div_le_iff₀ (pow_pos hLpos 2)]
        nlinarith
  have hlong :
      (Csw * (6 : ℝ) ^ R * N * (1 + L) / L ^ R) *
          (Ccofactor * L ^ Kcof) ≤ Clong * N / l ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlpos A)]
    calc
      (Csw * (6 : ℝ) ^ R * N * (1 + L) / L ^ R *
          (Ccofactor * L ^ Kcof)) * l ^ A =
        (Csw * (6 : ℝ) ^ R * Ccofactor * N) *
          ((1 + L) / L ^ R * L ^ Kcof * l ^ A) := by ring
      _ ≤ (Csw * (6 : ℝ) ^ R * Ccofactor * N) * 2 := by gcongr
      _ = Clong * N := by
        dsimp [Clong]
        ring
  refine (show
      (3 * (N : ℝ) ^ (5 / 6 : ℝ) +
        Csw * (6 : ℝ) ^ R * N * (1 + L) / L ^ R) *
          (Ccofactor * L ^ Kcof) ≤ C * N / l ^ A from ?_)
  calc
    _ = (3 * (N : ℝ) ^ (5 / 6 : ℝ)) * (Ccofactor * L ^ Kcof) +
        (Csw * (6 : ℝ) ^ R * N * (1 + L) / L ^ R) *
          (Ccofactor * L ^ Kcof) := by ring
    _ ≤ Cshort * N / l ^ A + Clong * N / l ^ A :=
      add_le_add hshort hlong
    _ = C * N / l ^ A := by
      dsimp [C]
      ring

/-- Uniform primitive Siegel--Walfisz is the sole remaining analytic input for
the low-conductor source family.  The local source transfer and both cofactor
masses are supplied by unconditional theorems in this module. -/
theorem
    LiuPanPrimitiveLogLambdaDilationSiegelWalfiszProducer.to_lowConductorSourceFamily
    {D₀ : ℕ → ℕ}
    (hproducer : LiuPanPrimitiveLogLambdaDilationSiegelWalfiszProducer D₀) :
    LiuMainPanAggregateLowConductorSiegelWalfiszSourceFamilyBound D₀ := by
  rcases hproducer with ⟨Kcut, hKcut, hproducer⟩
  intro A hA
  let Kcof : ℝ := 2 * Kcut + 24
  let R : ℝ := A + Kcof + 2
  have hR : 0 < R := by
    dsimp [R, Kcof]
    linarith
  rcases hproducer R hR with ⟨Csw, hCsw, Nsw, hcutoff, hSW⟩
  obtain ⟨Ccofactor, hCcofactor, hcofactor⟩ :=
    exists_liuPanLowConductorWeightedCofactorMassBoundAt
      D₀ 0 Kcut le_rfl hKcut
  obtain ⟨C, hC, Nscale, hscale⟩ :=
    exists_liuPanLowConductorSiegelWalfiszScalarBoundAt
      A Csw Ccofactor Kcut hA hCsw hCcofactor hKcut
  let N0 := max (max Nsw Nscale) 3
  refine ⟨C, hC, 0, le_rfl, N0, ?_⟩
  apply LiuMainPanAggregateLowConductorSiegelWalfiszBoundAt.of_primitive
    (R := R) (Csw := Csw) (Ccofactor := Ccofactor)
    (Kcut := Kcut) (Kcof := Kcof)
  · intro N hN
    apply hSW N
    dsimp [N0] at hN
    omega
  · intro N hN
    exact
      (LiuPanPrimitiveLowConductorSourceTransferLocalBoundAt.of_primitive_siegelWalfisz
        D₀ hR hCsw) N (by
          dsimp [N0] at hN
          omega)
  · intro N hN
    apply hcofactor N
    dsimp [N0] at hN
    omega
  · exact ⟨hKcut, fun N hN =>
      hcutoff.2 N (by
        dsimp [N0] at hN
        omega)⟩
  · intro N hN
    apply hscale N
    dsimp [N0] at hN
    omega

/-- One disjoint dyadic staircase cell after both primitive dilations.  Its
source and Lambda coordinates lie in half-open dyadic shells, while the exact
hyperbola cutoff remains in the Lambda endpoint. -/
noncomputable def liuPanPrimitiveDilationDyadicStaircase
    (j k y X q : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    ((ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)) *
      ∑ u ∈ Icc 1 (X / e) ∩ liuPanDyadicShell j,
        (liuPanSourceZeroExtension f (e * u) *
          χ.primitiveCharacter (u : ZMod χ.conductor)) *
          ∑ r ∈ (q / χ.conductor).divisors,
            ((ArithmeticFunction.moebius r : ℂ) *
              χ.primitiveCharacter (r : ZMod χ.conductor)) *
              ∑ v ∈ Icc 1 ((y / (e * u)) / r) ∩ liuPanDyadicShell k,
                liuPanLogLambdaCoefficient (r * v) *
                  χ.primitiveCharacter (v : ZMod χ.conductor)

/-- The exact nested dyadic expansion.  For each pair of source/Lambda
dilations, the only block labels are `j ≤ log₂ X` and `k ≤ log₂ y`. -/
noncomputable def liuPanPrimitiveDilationDyadicExpansion
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ e ∈ (q / χ.conductor).divisors,
    ((ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)) *
      ∑ j ∈ range (Nat.log 2 X + 1),
        ∑ u ∈ Icc 1 (X / e) ∩ liuPanDyadicShell j,
          (liuPanSourceZeroExtension f (e * u) *
            χ.primitiveCharacter (u : ZMod χ.conductor)) *
            ∑ r ∈ (q / χ.conductor).divisors,
              ((ArithmeticFunction.moebius r : ℂ) *
                χ.primitiveCharacter (r : ZMod χ.conductor)) *
                ∑ k ∈ range (Nat.log 2 y + 1),
                  ∑ v ∈ Icc 1 ((y / (e * u)) / r) ∩ liuPanDyadicShell k,
                    liuPanLogLambdaCoefficient (r * v) *
                      χ.primitiveCharacter (v : ZMod χ.conductor)

/-- Exact `O((1+log X)(1+log y))` dyadic staircase decomposition of the
primitive-dilation hyperbola. -/
theorem liuPanPrimitiveDilationLogLambdaHyperbola_eq_dyadicExpansion
    {q : ℕ} [NeZero q] (y X : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    liuPanPrimitiveDilationLogLambdaHyperbola y X q f χ =
      liuPanPrimitiveDilationDyadicExpansion y X q f χ := by
  classical
  unfold liuPanPrimitiveDilationLogLambdaHyperbola
    liuPanPrimitiveDilationDyadicExpansion
  simp_rw [sum_range_succ_eq_sum_Icc_of_zero
    (fun u =>
      (liuPanSourceZeroExtension f (_ * u) *
        χ.primitiveCharacter (u : ZMod χ.conductor)) * _)
    _ (by simp [liuPanSourceZeroExtension])]
  simp_rw [sum_range_succ_eq_sum_Icc_of_zero
    (fun v =>
      liuPanLogLambdaCoefficient (_ * v) *
        χ.primitiveCharacter (v : ZMod χ.conductor))
    _ (by simp)]
  simp_rw [sum_Icc_eq_sum_dyadicShell_of_le _ (Nat.div_le_self X _)]
  simp_rw [sum_Icc_eq_sum_dyadicShell_of_le _
    ((Nat.div_le_self (y / _) _).trans (Nat.div_le_self y _))]

theorem liuPanSourceLogLambdaCharacterHyperbola_eq_dyadicExpansion
    {q : ℕ} [NeZero q] (y X : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) :
    liuPanSourceLogLambdaCharacterHyperbola y X q f χ =
      liuPanPrimitiveDilationDyadicExpansion y X q f χ := by
  rw [liuPanSourceLogLambdaCharacterHyperbola_eq_primitive_dilations,
    liuPanPrimitiveDilationLogLambdaHyperbola_eq_dyadicExpansion]

/-- The displayed dyadic staircase family has exactly the advertised number
of possible block labels. -/
theorem liuPanDyadicStaircaseIndex_card (X y : ℕ) :
    ((range (Nat.log 2 X + 1)).product
      (range (Nat.log 2 y + 1))).card =
        (Nat.log 2 X + 1) * (Nat.log 2 y + 1) := by
  simp

/-- When both hyperbola coordinates are at most `N`, the number of available
dyadic source/Lambda labels is at most `(1+log₂ N)^2`. -/
theorem liuPanDyadicStaircaseIndex_card_le_sq
    {X y N : ℕ} (hX : X ≤ N) (hy : y ≤ N) :
    ((range (Nat.log 2 X + 1)).product
      (range (Nat.log 2 y + 1))).card ≤ (Nat.log 2 N + 1) ^ 2 := by
  rw [liuPanDyadicStaircaseIndex_card, pow_two]
  exact Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.log_mono_right hX) 1)
    (Nat.add_le_add_right (Nat.log_mono_right hy) 1)

/-- Lambda-side energy in every primitive dyadic cell is at most its length. -/
theorem liuPanLogLambdaDyadicEnergy_le_card
    (T r k d : ℕ) (ψ : DirichletCharacter ℂ d) :
    (∑ v ∈ Icc 1 T ∩ liuPanDyadicShell k,
      ‖liuPanLogLambdaCoefficient (r * v) *
        ψ (v : ZMod d)‖ ^ 2) ≤
      ((Icc 1 T ∩ liuPanDyadicShell k).card : ℝ) := by
  calc
    _ ≤ ∑ _v ∈ Icc 1 T ∩ liuPanDyadicShell k, (1 : ℝ) := by
      apply sum_le_sum
      intro v hv
      have hnorm :
          ‖liuPanLogLambdaCoefficient (r * v) *
            ψ (v : ZMod d)‖ ≤ 1 := by
        rw [norm_mul]
        exact (mul_le_mul
          (norm_liuPanLogLambdaCoefficient_le_one (r * v))
          (dirichletCharacter_norm_le_one d ψ (v : ZMod d))
          (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hnorm
    _ = _ := by simp

/-- The exact support geometry of Liu's source: every nonzero coefficient lies
strictly above `N^(13/30)` and at most `N^(2/3)`. -/
theorem liuWeight_ne_zero_source_bounds
    {N a : ℕ} (hN : 1 ≤ N)
    (ha : liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0) :
    (N : ℝ) ^ (13 / 30 : ℝ) < a ∧
      (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hs : LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) a := by
    by_contra h
    exact ha (liuWeight_eq_zero_iff.mpr h)
  rcases liuWeightSupport_iff.mp hs with ⟨p₁, p₂, hp, rfl⟩
  have hrange := liuWeightPairs_source_basic_range (mem_liuWeightPairs.mpr hp)
  have hNpos : (0 : ℝ) < N := by positivity
  constructor
  · calc
      (N : ℝ) ^ (13 / 30 : ℝ) =
          (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_add hNpos]
            norm_num
      _ < (p₁ : ℝ) * p₂ := mul_lt_mul hrange.1 hrange.2.2.le
        (Real.rpow_pos_of_pos hNpos _) (by positivity)
      _ = (p₁ * p₂ : ℕ) := by norm_num
  · exact liuWeightSupport_le_rpow_two_thirds hs

/-- On the exact product hyperbola, the source lower bound forces the
von-Mangoldt variable below `N^(17/30)`. -/
theorem liuWeight_hyperbola_lambda_lt_rpow_seventeen_thirtieth
    {N a m : ℕ} (hN : 1 ≤ N)
    (ha : liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a ≠ 0)
    (ham : a * m ≤ N) :
    (m : ℝ) < (N : ℝ) ^ (17 / 30 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by positivity
  by_cases hm : m = 0
  · subst m
    simpa using Real.rpow_pos_of_pos hNpos (17 / 30 : ℝ)
  have haLower := (liuWeight_ne_zero_source_bounds hN ha).1
  have hamR : (a : ℝ) * m ≤ N := by exact_mod_cast ham
  have hden : 0 < (N : ℝ) ^ (13 / 30 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast Nat.pos_of_ne_zero hm
  have hmdiv :
      (m : ℝ) < (N : ℝ) / (N : ℝ) ^ (13 / 30 : ℝ) := by
    rw [lt_div_iff₀ hden]
    have hmul :
        (N : ℝ) ^ (13 / 30 : ℝ) * m < (a : ℝ) * m :=
      mul_lt_mul_of_pos_right haLower hmpos
    simpa [mul_comm] using hmul.trans_le hamR
  calc
    (m : ℝ) < (N : ℝ) / (N : ℝ) ^ (13 / 30 : ℝ) := hmdiv
    _ = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (13 / 30 : ℝ) := by
      rw [Real.rpow_one]
    _ = (N : ℝ) ^ (1 - 13 / 30 : ℝ) :=
      (Real.rpow_sub hNpos 1 (13 / 30)).symm
    _ = (N : ℝ) ^ (17 / 30 : ℝ) := by norm_num

/-! ## Fixed dilation staircase blocks -/

/-- One fixed `(e,r,j,k)` block of the primitive hyperbola.  This is a
staircase, not a tensor-product rectangle: the upper endpoint of the `v`-sum
still depends on `u`. -/
noncomputable def liuPanPrimitiveDilationDyadicBlock
    (e r j k y X q : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) : ℂ :=
  ((ArithmeticFunction.moebius e : ℂ) *
      χ.primitiveCharacter (e : ZMod χ.conductor)) *
    ((ArithmeticFunction.moebius r : ℂ) *
      χ.primitiveCharacter (r : ZMod χ.conductor)) *
    ∑ u ∈ Icc 1 (X / e) ∩ liuPanDyadicShell j,
      (liuPanSourceZeroExtension f (e * u) *
        χ.primitiveCharacter (u : ZMod χ.conductor)) *
        ∑ v ∈ Icc 1 ((y / (e * u)) / r) ∩ liuPanDyadicShell k,
          liuPanLogLambdaCoefficient (r * v) *
            χ.primitiveCharacter (v : ZMod χ.conductor)

/-- A dyadic shell clipped at a positive prefix is a half-open interval with
the same left endpoint.  This is the interval shape used by finite Perron. -/
theorem Icc_inter_liuPanDyadicShell_eq_Ico
    (T j : ℕ) :
    Icc 1 T ∩ liuPanDyadicShell j =
      Ico (2 ^ j)
        (2 ^ j + (min (T + 1) (2 ^ (j + 1)) - 2 ^ j)) := by
  ext n
  simp only [liuPanDyadicShell, mem_inter, mem_Icc, mem_Ico]
  have hj : 1 ≤ 2 ^ j := one_le_pow₀ (by omega)
  omega

/-- At fixed positive dilations, the staircase cutoff is exactly the product
cutoff in the ambient clipped dyadic rectangle. -/
theorem liuPanDilationStaircase_eq_filter
    {e r u y N k : ℕ} (he : 0 < e) (hr : 0 < r)
    (hu : 0 < u) (hyN : y ≤ N) :
    Icc 1 ((y / (e * u)) / r) ∩ liuPanDyadicShell k =
      (Icc 1 (N / r) ∩ liuPanDyadicShell k).filter
        (fun v => u * v ≤ y / (e * r)) := by
  ext v
  simp only [mem_inter, mem_Icc, mem_filter]
  constructor
  · rintro ⟨⟨hv, hvcut⟩, hvk⟩
    have hcut : u * v ≤ y / (e * r) := by
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos he hr)]
      rw [Nat.le_div_iff_mul_le hr] at hvcut
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos he hu)] at hvcut
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hvcut
    have hvN : v ≤ N / r := by
      rw [Nat.le_div_iff_mul_le hr]
      calc
        v * r ≤ (v * r) * (e * u) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos he hu)
        _ ≤ y := by
          rw [Nat.le_div_iff_mul_le hr] at hvcut
          exact (Nat.le_div_iff_mul_le (Nat.mul_pos he hu)).mp hvcut
        _ ≤ N := hyN
    exact ⟨⟨⟨hv, hvN⟩, hvk⟩, hcut⟩
  · rintro ⟨⟨⟨hv, _hvN⟩, hvk⟩, hcut⟩
    refine ⟨⟨hv, ?_⟩, hvk⟩
    rw [Nat.le_div_iff_mul_le hr]
    rw [Nat.le_div_iff_mul_le (Nat.mul_pos he hu)]
    rw [Nat.le_div_iff_mul_le (Nat.mul_pos he hr)] at hcut
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcut

/-- Exposing the four finite block indices is an exact rearrangement.  In
particular this theorem does not replace a staircase by its ambient rectangle. -/
theorem liuPanPrimitiveDilationDyadicExpansion_eq_sum_blocks
    (y X q : ℕ) (f : ℕ → ℝ) (χ : DirichletCharacter ℂ q) :
    liuPanPrimitiveDilationDyadicExpansion y X q f χ =
      ∑ e ∈ (q / χ.conductor).divisors,
        ∑ j ∈ range (Nat.log 2 X + 1),
          ∑ r ∈ (q / χ.conductor).divisors,
            ∑ k ∈ range (Nat.log 2 y + 1),
              liuPanPrimitiveDilationDyadicBlock e r j k y X q f χ := by
  classical
  unfold liuPanPrimitiveDilationDyadicExpansion
    liuPanPrimitiveDilationDyadicBlock
  simp only [mul_sum]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  apply sum_congr rfl
  intro r hr
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  apply sum_congr rfl
  intro v hv
  ring

/-- Source-side square energy for one fixed dilation and dyadic shell. -/
noncomputable def liuPanSourceDilationDyadicEnergy
    (N e j : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ u ∈ Icc 1 (N / e) ∩ liuPanDyadicShell j,
    ‖(liuPanSourceZeroExtension f (e * u) : ℂ)‖ ^ 2

/-- Lambda-side square energy for one fixed dilation and dyadic shell. -/
noncomputable def liuPanLogLambdaDilationDyadicEnergy
    (N r k : ℕ) : ℝ :=
  ∑ v ∈ Icc 1 (N / r) ∩ liuPanDyadicShell k,
    ‖liuPanLogLambdaCoefficient (r * v)‖ ^ 2

/-- Liu's source is an exact indicator, so every fixed dilated source shell has
energy at most its cardinality. -/
theorem liuPanSourceDilationDyadicEnergy_le_card (N e j : ℕ) :
    liuPanSourceDilationDyadicEnergy N e j
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      ((Icc 1 (N / e) ∩ liuPanDyadicShell j).card : ℝ) := by
  unfold liuPanSourceDilationDyadicEnergy
  calc
    _ ≤ ∑ _u ∈ Icc 1 (N / e) ∩ liuPanDyadicShell j, (1 : ℝ) := by
      apply sum_le_sum
      intro u hu
      by_cases heu : e * u = 0
      · simp [liuPanSourceZeroExtension, heu]
      · rw [liuPanSourceZeroExtension, if_neg heu, Complex.norm_real,
          Real.norm_eq_abs]
        have h :
            |liuWeight N (liuSourceZ10 N) (liuSourceY3 N) (e * u)| ≤ 1 := by
          by_cases ha :
              LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) (e * u) <;>
            simp [liuWeight, ha]
        simpa using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 h
    _ = _ := by simp

/-- The Lambda energy of a fixed dilated shell is bounded by its cardinality. -/
theorem liuPanLogLambdaDilationDyadicEnergy_le_card (N r k : ℕ) :
    liuPanLogLambdaDilationDyadicEnergy N r k ≤
      ((Icc 1 (N / r) ∩ liuPanDyadicShell k).card : ℝ) := by
  unfold liuPanLogLambdaDilationDyadicEnergy
  calc
    _ ≤ ∑ _v ∈ Icc 1 (N / r) ∩ liuPanDyadicShell k, (1 : ℝ) := by
      apply sum_le_sum
      intro v hv
      have h := norm_liuPanLogLambdaCoefficient_le_one (r * v)
      simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 h
    _ = _ := by simp

/-- Uniform maximum over the shared hyperbola endpoint and reduced residue
phase for one fixed primitive-dilation staircase block. -/
noncomputable def liuPanPrimitiveDilationDyadicBlockMaxYL
    (N e r j k q : ℕ) (f : ℕ → ℝ)
    (χ : DirichletCharacter ℂ q) : ℝ :=
  let S := unitResidues q
  if hS : S.Nonempty then
    ((range (N + 1)).image fun y =>
      (S.image fun l : ℕ =>
        ‖star (χ (l : ZMod q)) *
          liuPanPrimitiveDilationDyadicBlock e r j k y N q f χ‖).max'
            (Finset.image_nonempty.mpr hS)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)
  else 0

/-- The original squarefree `3^omega` modulus weight, exact conductor fiber,
and both complementary-cofactor divisor tests for a fixed
`(D,e,r,j,k)` block. -/
noncomputable def liuPanWeightedPrimitiveDyadicBlockMean
    (N Q D e r j k : ℕ) : ℝ :=
  ∑ q ∈ range (Q + 1),
    if _hq : q = 0 then 0 else
      liuPanPrimePowerModulusWeight q * (Nat.totient q : ℝ)⁻¹ *
        ∑ d ∈ Icc 2 q ∩ Ico D (2 * D), if hdq : d ∣ q then
          ∑ ψ ∈ liuPanPrimePowerPrimitiveCharacters d,
            let χ := DirichletCharacter.changeLevel hdq ψ
            if e ∈ (q / χ.conductor).divisors ∧
                r ∈ (q / χ.conductor).divisors then
              liuPanPrimitiveDilationDyadicBlockMaxYL
                N e r j k q
                  (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) χ
            else 0
        else 0

/-- The precise local analytic input needed for one conductor/source/Lambda
scale.  Unlike two independent one-dimensional large-sieve estimates, its left
side retains the hyperbola maximum, both induced-character dilations, and the
original modulus/cofactor weights. -/
def LiuPanPrimitiveHyperbolaMaximalBlockBoundAt
    (N Q D e r j k : ℕ) (K : ℝ) : Prop :=
  liuPanWeightedPrimitiveDyadicBlockMean N Q D e r j k ≤
    Real.log N ^ K / D *
      Real.sqrt
        ((((2 ^ j : ℕ) : ℝ) + D ^ 2) *
          liuPanSourceDilationDyadicEnergy N e j
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) *
      Real.sqrt
        ((((2 ^ k : ℕ) : ℝ) + D ^ 2) *
          liuPanLogLambdaDilationDyadicEnergy N r k)

/-- The power-saving profile predicted after summing the local primitive
hyperbola estimates over conductor shells and complementary cofactors. -/
noncomputable def liuPanAggregateMediumHighPowerProfile
    (N D₀ : ℕ) : ℝ :=
  (N : ℝ) / D₀ + (N : ℝ) ^ (5 / 6 : ℝ) +
    D₀ * Real.sqrt N

/-- The still-missing weighted cofactor transfer, isolated from the local
primitive hyperbola estimate.  It must sum the exact local block bounds without
discarding the squarefree `3^omega` weights or taking a pointwise cofactor
maximum.  No instance of this predicate is asserted in this module. -/
def LiuPanAggregateMediumHighWeightedCofactorTransferBoundAt
    (D₀ : ℕ → ℕ) (B C K : ℝ) (N0 : ℕ) : Prop :=
  ∀ N : ℕ, N0 ≤ N →
    0 < D₀ N →
    (∀ D e r j k : ℕ, D₀ N < D →
      LiuPanPrimitiveHyperbolaMaximalBlockBoundAt
        N (panModulusCutoff N B) D e r j k K) →
    liuMainPanAggregateLogLambdaMediumHighConductorAverage
        (D₀ N) N (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B ≤
      C * liuPanAggregateMediumHighPowerProfile N (D₀ N) *
        Real.log N ^ K

/-- Once the local primitive hyperbola inequality, the weighted cofactor
transfer, and the final numerical parameter comparison are available, they
supply the existing medium/high source-family contract. -/
theorem LiuMainPanAggregateMediumHighConductorBilinearBoundAt.of_local_blocks
    {D₀ : ℕ → ℕ} {A B C Chigh K : ℝ} {N0 : ℕ}
    (hlocal : ∀ N : ℕ, N0 ≤ N → ∀ D e r j k : ℕ, D₀ N < D →
      LiuPanPrimitiveHyperbolaMaximalBlockBoundAt
        N (panModulusCutoff N B) D e r j k K)
    (htransfer :
      LiuPanAggregateMediumHighWeightedCofactorTransferBoundAt
        D₀ B C K N0)
    (hD₀ : ∀ N : ℕ, N0 ≤ N → 0 < D₀ N)
    (hpower : ∀ N : ℕ, N0 ≤ N →
      C * liuPanAggregateMediumHighPowerProfile N (D₀ N) *
          Real.log N ^ K ≤
        Chigh * N / Real.log N ^ A) :
    LiuMainPanAggregateMediumHighConductorBilinearBoundAt
      D₀ A Chigh B N0 := by
  intro N hN
  exact (htransfer N hN (hD₀ N hN) (hlocal N hN)).trans (hpower N hN)

end MathlibNt.SieveTheory.LiuWeight
