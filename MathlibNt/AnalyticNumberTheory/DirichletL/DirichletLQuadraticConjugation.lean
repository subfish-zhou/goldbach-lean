import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLConditionalValueSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticFunctionalEquation

open Complex Finset Filter Set
open scoped Topology

namespace DirichletCharacter

open DirichletLAbelWeightVariation DirichletLConditionalValueSeries

local notation "conj" => starRingEnd ℂ

variable {q : ℕ} [NeZero q]

/-- Complex conjugation fixes a quadratic Dirichlet character. -/
lemma star_eq_self_of_sq_eq_one (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) :
    star χ = χ := by
  rw [MulChar.star_eq_inv, (MulChar.isQuadratic_iff_sq_eq_one.mpr hquad).inv]

private lemma conj_character_apply_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (k : ℕ) :
    conj (χ k) = χ k := by
  have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ k)
    (star_eq_self_of_sq_eq_one χ hquad)
  simpa using h

private lemma conj_cpowWeight (s : ℂ) (k : ℕ) :
    conj (cpowWeight s k) = cpowWeight (conj s) k := by
  unfold cpowWeight
  have harg : ((k : ℂ)).arg ≠ Real.pi := by
    change (((k : ℝ) : ℂ)).arg ≠ Real.pi
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact ne_of_lt Real.pi_pos
  simpa using (Complex.cpow_conj (k : ℂ) (-s) harg).symm

/-- Conjugating a finite natural-order partial sum conjugates its parameter. -/
lemma conj_sum_range_cpowWeight_character_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (s : ℂ) (n : ℕ) :
    conj (∑ k ∈ range n, cpowWeight s k * χ k) =
      ∑ k ∈ range n, cpowWeight (conj s) k * χ k := by
  rw [map_sum]
  apply sum_congr rfl
  intro k hk
  rw [map_mul, conj_cpowWeight, conj_character_apply_of_sq_eq_one χ hquad k]

/-- A nonprincipal quadratic Dirichlet L-function commutes with complex
conjugation throughout `re s > 0`.  The proof compares the natural-order
partial sums and then uses continuity and uniqueness of limits. -/
theorem LFunction_conj_eq_conj_LFunction_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction (conj s) = conj (χ.LFunction s) := by
  have hsc : 0 < (conj s).re := by simpa using hs
  have hleft := tendsto_sum_range_orderedValueSeries χ hχ (conj s) hsc
  have hright0 := tendsto_sum_range_orderedValueSeries χ hχ s hs
  have hright :
      Tendsto (fun n : ℕ => conj (∑ k ∈ range n, cpowWeight s k * χ k)) atTop
        (𝓝 (conj (orderedValueSeries χ hχ s hs))) :=
    (Complex.continuous_conj.tendsto (orderedValueSeries χ hχ s hs)).comp hright0
  have hright' :
      Tendsto (fun n : ℕ => ∑ k ∈ range n, cpowWeight (conj s) k * χ k) atTop
        (𝓝 (conj (orderedValueSeries χ hχ s hs))) := by
    refine (tendsto_congr' (Eventually.of_forall fun n => ?_)).mp hright
    exact conj_sum_range_cpowWeight_character_of_sq_eq_one χ hquad s n
  have hordered :
      orderedValueSeries χ hχ (conj s) hsc =
        conj (orderedValueSeries χ hχ s hs) :=
    tendsto_nhds_unique hleft hright'
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ (conj s) hsc,
    orderedValueSeries_eq_LFunction_of_re_pos χ hχ s hs] at hordered
  exact hordered

/-- Every positive real value of a nonprincipal quadratic Dirichlet L-function
is real. -/
theorem LFunction_ofReal_im_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (β : ℝ) (hβ : 0 < β) :
    (χ.LFunction (β : ℂ)).im = 0 := by
  have hs : 0 < ((β : ℂ).re) := by simpa using hβ
  have h := LFunction_conj_eq_conj_LFunction_of_sq_eq_one χ hχ hquad (β : ℂ) hs
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- Zeros of a nonprincipal quadratic Dirichlet L-function in `re s > 0` are
closed under complex conjugation. -/
theorem LFunction_conj_eq_zero_of_sq_eq_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ ^ 2 = 1)
    (s : ℂ) (hs : 0 < s.re) (hz : χ.LFunction s = 0) :
    χ.LFunction (conj s) = 0 := by
  rw [LFunction_conj_eq_conj_LFunction_of_sq_eq_one χ hχ hquad s hs, hz, map_zero]

end DirichletCharacter