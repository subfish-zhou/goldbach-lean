import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosCurve
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Harcos's trace-zero count

The last six counting lines of Corollary 3 on Harcos, page 8
(`pages/harcos-stepanov-08.png`), use the actual field trace and the
change of variables `y = 2at - (x^p - x)`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial Finset

section Trace

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]

/-- The relative Artin--Schreier linear map for finite fields. -/
def harcosArtinSchreier : L →ₗ[K] L :=
  (FiniteField.frobeniusAlgHom K L).toLinearMap - LinearMap.id

omit [Fintype L] in
@[simp] theorem harcosArtinSchreier_apply (x : L) :
    harcosArtinSchreier K L x = x ^ Fintype.card K - x := rfl

/-- Frobenius invariance of the actual algebra trace. -/
theorem harcos_trace_pow_card (x : L) :
    Algebra.trace K L (x ^ Fintype.card K) = Algebra.trace K L x :=
  Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic K L) x

theorem harcos_trace_artinSchreier (x : L) :
    Algebra.trace K L (harcosArtinSchreier K L x) = 0 := by
  rw [harcosArtinSchreier_apply, map_sub, harcos_trace_pow_card, sub_self]

omit [Fintype L] in
/-- The fixed points of the relative Frobenius are exactly the embedded base field. -/
theorem harcos_pow_card_eq_self_iff (x : L) :
    x ^ Fintype.card K = x ↔ ∃ c : K, algebraMap K L c = x := by
  classical
  have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := (X ^ Fintype.card K - X : K[X])) (algebraMap K L).injective
    (by rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]; rfl)
  have hn := FiniteField.X_pow_card_sub_X_ne_zero L (Fintype.one_lt_card (α := K))
  have hm : (X ^ Fintype.card K - X : L[X]).roots =
      (univ.val : Multiset K).map (algebraMap K L) := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      FiniteField.roots_X_pow_card_sub_X] using hr.symm
  rw [← sub_eq_zero, ← show
    (X ^ Fintype.card K - X : L[X]).IsRoot x ↔
      x ^ Fintype.card K - x = 0 by simp [Polynomial.IsRoot],
    ← Polynomial.mem_roots hn, hm]
  simp

omit [Fintype L] in
theorem harcos_artinSchreier_ker :
    (harcosArtinSchreier K L).ker = (Algebra.linearMap K L).range := by
  ext x
  simp only [LinearMap.mem_ker, harcosArtinSchreier_apply, sub_eq_zero,
    LinearMap.mem_range, Algebra.linearMap_apply, harcos_pow_card_eq_self_iff]

omit [Fintype L] in
theorem harcos_artinSchreier_ker_finrank :
    Module.finrank K (harcosArtinSchreier K L).ker = 1 := by
  rw [harcos_artinSchreier_ker,
    LinearMap.finrank_range_of_inj (algebraMap K L).injective]
  exact Module.finrank_self K

/-- Rank-nullity and nondegeneracy of the trace give additive Hilbert 90 here,
without assuming any trace-zero solvability statement. -/
theorem harcos_artinSchreier_range :
    (harcosArtinSchreier K L).range = (Algebra.trace K L).ker := by
  have hle : (harcosArtinSchreier K L).range ≤ (Algebra.trace K L).ker := by
    rintro _ ⟨x, rfl⟩
    exact harcos_trace_artinSchreier K L x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have ha := LinearMap.finrank_range_add_finrank_ker (harcosArtinSchreier K L)
  have ht := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  rw [harcos_artinSchreier_ker_finrank] at ha
  rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)] at ht
  simp only [finrank_top, Module.finrank_self] at ht
  omega

theorem harcos_artinSchreier_exists_iff (c : L) :
    (∃ x : L, x ^ Fintype.card K - x = c) ↔ Algebra.trace K L c = 0 := by
  change c ∈ (harcosArtinSchreier K L).range ↔ c ∈ (Algebra.trace K L).ker
  rw [harcos_artinSchreier_range]

/-- Every nonempty Artin--Schreier fiber has exactly `#K` elements; the empty
fibers are exactly those with nonzero field trace. -/
theorem harcos_artinSchreier_fiber_card [DecidableEq L] [DecidableEq K] (c : L) :
    (univ.filter fun x : L => x ^ Fintype.card K - x = c).card =
      if Algebra.trace K L c = 0 then Fintype.card K else 0 := by
  classical
  change (univ.filter fun x : L => harcosArtinSchreier K L x = c).card = _
  by_cases hc : Algebra.trace K L c = 0
  · rw [if_pos hc]
    obtain ⟨r, hr⟩ := (harcos_artinSchreier_exists_iff K L c).mpr hc
    change harcosArtinSchreier K L r = c at hr
    have hcard : (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card =
        Fintype.card K := by
      simpa only [harcos_artinSchreier_ker_finrank, pow_one,
        Fintype.card_subtype, LinearMap.mem_ker] using
        (Module.card_eq_pow_finrank (K := K) (V := (harcosArtinSchreier K L).ker))
    calc
      _ = (univ.filter fun x : L => harcosArtinSchreier K L x = 0).card := by
        refine card_nbij' (fun x : L => x - r) (fun x : L => x + r) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_sub, hx, hr, sub_self]
        · intro x hx
          simp only [mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
          rw [map_add, hx, hr, zero_add]
        · intro x _
          exact sub_add_cancel x r
        · intro x _
          exact add_sub_cancel_right x r
      _ = Fintype.card K := hcard
  · rw [if_neg hc]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    exact hc ((harcos_artinSchreier_exists_iff K L c).mp ⟨x, hx⟩)

end Trace

section ChangeOfVariables

variable {F : Type*} [Field F]

theorem harcos_artinSchreier_eq_iff_quadratic (s a b t : F) (ht : t ≠ 0) :
    s = a * t + b / t ↔ a * t ^ 2 - s * t + b = 0 := by
  constructor
  · intro h
    have h' := (eq_div_iff ht).mp (show s - a * t = b / t by rw [h]; ring)
    linear_combination -h'
  · intro h
    have h' : (s - a * t) * t = b := by linear_combination -h
    have := (eq_div_iff ht).mpr h'
    linear_combination this

theorem harcos_square_iff_quadratic (htwo : (2 : F) ≠ 0)
    (s a b t : F) (ha : a ≠ 0) :
    (2 * a * t - s) ^ 2 = s ^ 2 - 4 * a * b ↔
      a * t ^ 2 - s * t + b = 0 := by
  have hfour : (4 : F) ≠ 0 := by
    have h := mul_ne_zero htwo htwo
    norm_num at h ⊢
    exact h
  constructor
  · intro h
    have h' : (4 * a) * (a * t ^ 2 - s * t + b) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero hfour ha)
  · intro h
    linear_combination 4 * a * h

theorem harcos_quadratic_parameter_nonzero (s a b t : F) (hb : b ≠ 0)
    (h : a * t ^ 2 - s * t + b = 0) : t ≠ 0 := by
  intro ht
  apply hb
  simpa only [ht, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_add] using h

/-- The explicit inverse substitution `t = (y+s)/(2a)`. -/
theorem harcos_curve_parameter_inverse (htwo : (2 : F) ≠ 0)
    (s a y : F) (ha : a ≠ 0) :
    2 * a * ((y + s) / (2 * a)) - s = y := by
  field_simp [htwo, ha]
  ring

/-- Harcos's change of variables, with nonzero `t` represented by a unit.
Its forward map is exactly `(x,t) ↦ (x,2at-(x^p-x))`; the surjectivity proof
constructs the inverse parameter `(y+(x^p-x))/(2a)`. -/
def harcosCurveArtinSchreierEquiv (p : ℕ) (htwo : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {xt : F × Fˣ // xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)} ≃
      {xy : F × F // xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b} :=
  Equiv.ofBijective
    (fun xt => ⟨(xt.1.1, 2 * a * (xt.1.2 : F) - (xt.1.1 ^ p - xt.1.1)),
      (harcos_square_iff_quadratic htwo _ a b _ ha).mpr
        ((harcos_artinSchreier_eq_iff_quadratic _ a b _ (Units.ne_zero _)).mp xt.2)⟩)
    (by
      constructor
      · intro xt xu h
        apply Subtype.ext
        have hx := congrArg (fun z => z.1.1) h
        have hy := congrArg (fun z => z.1.2) h
        dsimp only at hx hy
        apply Prod.ext hx
        apply Units.val_injective
        rw [hx] at hy
        have hmul : (2 * a) * (xt.1.2 : F) = (2 * a) * (xu.1.2 : F) := by
          linear_combination hy
        exact mul_left_cancel₀ (mul_ne_zero htwo ha) hmul
      · intro xy
        let s := xy.1.1 ^ p - xy.1.1
        let t := (xy.1.2 + s) / (2 * a)
        have hinv : 2 * a * t - s = xy.1.2 :=
          harcos_curve_parameter_inverse htwo s a xy.1.2 ha
        have hquad : a * t ^ 2 - s * t + b = 0 := by
          apply (harcos_square_iff_quadratic htwo s a b t ha).mp
          rw [hinv]
          exact xy.2
        have ht := harcos_quadratic_parameter_nonzero s a b t hb hquad
        refine ⟨⟨(xy.1.1, Units.mk0 t ht), ?_⟩, ?_⟩
        · exact (harcos_artinSchreier_eq_iff_quadratic s a b t ht).mpr hquad
        · apply Subtype.ext
          exact Prod.ext rfl hinv)

@[simp] theorem harcosCurveArtinSchreierEquiv_apply
    (p : ℕ) (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (xt : {xt : F × Fˣ // xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)}) :
    (harcosCurveArtinSchreierEquiv p htwo a b ha hb xt).1 =
      (xt.1.1, 2 * a * (xt.1.2 : F) - (xt.1.1 ^ p - xt.1.1)) := rfl

theorem harcosCurveArtinSchreierEquiv_symm_apply
    (p : ℕ) (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (xy : {xy : F × F // xy.2 ^ 2 = (xy.1 ^ p - xy.1) ^ 2 - 4 * a * b}) :
    ((harcosCurveArtinSchreierEquiv p htwo a b ha hb).symm xy).1.1 = xy.1.1 ∧
      (((harcosCurveArtinSchreierEquiv p htwo a b ha hb).symm xy).1.2 : F) =
        (xy.1.2 + (xy.1.1 ^ p - xy.1.1)) / (2 * a) := by
  have h := congrArg Subtype.val
    ((harcosCurveArtinSchreierEquiv p htwo a b ha hb).apply_symm_apply xy)
  rw [harcosCurveArtinSchreierEquiv_apply] at h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp only at hx hy
  refine ⟨hx, (eq_div_iff (mul_ne_zero htwo ha)).mpr ?_⟩
  rw [hx] at hy
  linear_combination hy

end ChangeOfVariables

section Counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem harcosCurvePointCount_eq_artinSchreier_pairCount
    (p : ℕ) (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      (univ.filter fun xt : F × Fˣ =>
        xt.1 ^ p - xt.1 = a * (xt.2 : F) + b / (xt.2 : F)).card := by
  classical
  simpa only [Fintype.card_subtype, harcosCurvePointCount] using
    (Fintype.card_congr (harcosCurveArtinSchreierEquiv p htwo a b ha hb)).symm

/-- The relative finite-field version of Harcos's trace-zero counting identity. -/
theorem harcosCurvePointCount_eq_card_mul_traceZero
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Algebra K F]
    (htwo : (2 : F) ≠ 0) (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount (Fintype.card K) a b =
      Fintype.card K *
        (univ.filter fun t : Fˣ =>
          Algebra.trace K F (a * (t : F) + b / (t : F)) = 0).card := by
  classical
  rw [harcosCurvePointCount_eq_artinSchreier_pairCount _ htwo a b ha hb]
  calc
    _ = ∑ t : Fˣ, (univ.filter fun x : F =>
        x ^ Fintype.card K - x = a * (t : F) + b / (t : F)).card := by
      simp only [card_filter, Fintype.sum_prod_type]
      exact sum_comm
    _ = ∑ t : Fˣ, if Algebra.trace K F (a * (t : F) + b / (t : F)) = 0
        then Fintype.card K else 0 := by
      apply sum_congr rfl
      intro t _
      exact harcos_artinSchreier_fiber_card K F _
    _ = _ := by
      rw [card_filter, mul_sum]
      apply sum_congr rfl
      intro t _
      split_ifs <;> simp

/-- Artin--Schreier fibers over the prime field have size `p` precisely at
trace-zero elements. This uses `Algebra.trace`, not a fiber-count surrogate. -/
theorem harcos_artinSchreier_prime_fiber_card (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) F] (c : F) :
    (univ.filter fun x : F => x ^ p - x = c).card =
      if Algebra.trace (ZMod p) F c = 0 then p else 0 := by
  simpa only [ZMod.card] using harcos_artinSchreier_fiber_card (ZMod p) F c

/-- The last six counting lines of Harcos, Corollary 3, page 8. -/
theorem harcosCurvePointCount_eq_prime_mul_traceZero (p : ℕ) [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F] (hp2 : p ≠ 2)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCurvePointCount p a b =
      p * (univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F (a * (t : F) + b * (t : F)⁻¹) = 0).card := by
  have htwo : (2 : F) ≠ 0 := by
    exact_mod_cast CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  simpa only [ZMod.card, div_eq_mul_inv] using
    harcosCurvePointCount_eq_card_mul_traceZero (ZMod p) htwo a b ha hb

end Counts

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
