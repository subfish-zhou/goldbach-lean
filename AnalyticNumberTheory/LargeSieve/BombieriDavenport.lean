import AnalyticNumberTheory.LargeSieve.Multiplicative
import AnalyticNumberTheory.Sieve.PanMeanValueBody
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.Tactic

/-! # AnalyticNumberTheory.LargeSieve.BombieriDavenport

## Primitive characters + Gauss sums, and the Bombieri-Davenport large sieve

This module proves the classical Bombieri-Davenport multiplicative large sieve
lemma (Montgomery 1971 Ch.1; Iwaniec-Kowalski 2004 Thm 7.18 type):

  sum_{1 <= q <= Q} (q/phi(q)) * sum_{chi primitive mod q} ||sum_n a_n chi(n)||^2
      <= largeSieveBound(N, 1/Q^2) * sum_n ||a_n||^2

The construction consists of:
1. The standard additive character e_q(x) = e(x.val/q) on ZMod q (from
   AddChar.zmodChar and the repo's charReal), its primitivity, and the Gauss
   sum bridge gaussSum chi (e_q.mulShift n) = sum_x chi(x) * e(n * x.val / q).
2. |tau(chi)|^2 = q for primitive chi mod q (zmodParseval + mathlib's
   gaussSum_mulShift_of_isPrimitive).
3. Gauss-sum Fourier inversion for primitive chi:
   ||S_chi||^2 = (1/q) * ||sum_{r<q} chi(r) * T(r/q)||^2.
4. The Bombieri-Davenport stacking: unit Parseval (charOrthSum) + the Farey
   point additive sieve (largeSieveRationalPoints).

Limitation of panTypeICharSquareMeanBound: the literal target
  sum_{q <= Q} mu^2(q) 3^omega(q) * sum_{chi mod q} ||V_chi(m)||^2
      <= C * (m + Q^2) * sum_{n <= m} vaughanFirst(n,u)^2
is FALSE as stated: take u = 1 (then vaughanFirst(n,1) = log n) and m = Q^2;
the smooth part of the class sums gives
  LHS >= sum_{q <= Q} mu^2(q) 3^omega(q) phi(q)^2 m^2 (log m)^2 / q^2
which already exceeds C (m + Q^2) S(m) for every constant C (primes alone
contribute sum_{p <= Q} 3 (p-1)^2 / p^2 ~ 3 Q / log Q). See check_target.py
for the numerics (LHS/RHS grows without bound as Q -> oo). The correct
analytic input is the primitive-character version with the (q/phi(q)) weight,
proved below as bombieriDavenport_le; see the file trailer for the explicit
corrected sub-steps of the type-I assembly.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## 1. The standard additive character e_q and Gauss sum bridge -/

/-- Standard q-th root of unity: zeta = e(1/q) = exp(2*pi*i/q). -/
def zetaRoot (q : ℕ) : ℂ := charReal (1 / (q : ℝ))

/-- zeta is a primitive q-th root of unity (q != 0). -/
lemma zetaRoot_isPrimitiveRoot (q : ℕ) (hq : q ≠ 0) : IsPrimitiveRoot (zetaRoot q) q := by
  have h := Complex.isPrimitiveRoot_exp_of_isCoprime (1 : ℤ) q hq (by exact isCoprime_one_left)
  convert h using 1
  · dsimp [zetaRoot, charReal]
    congr 1
    norm_num
    ring

/-- zeta^q = 1 (q != 0). -/
lemma zetaRoot_pow (q : ℕ) (hq : q ≠ 0) : (zetaRoot q) ^ q = 1 := by
  exact (IsPrimitiveRoot.iff_def (zetaRoot q) q).mp (zetaRoot_isPrimitiveRoot q hq) |>.1

/-- The standard additive character e_q(a) = e(a.val/q) = zeta^(a.val). -/
def zmodCharStd (q : ℕ) [NeZero q] : AddChar (ZMod q) ℂ :=
  AddChar.zmodChar q (zetaRoot_pow q (NeZero.ne q))

/-- e_q(a) = e(a.val/q). -/
lemma zmodCharStd_apply (q : ℕ) [NeZero q] (a : ZMod q) :
    zmodCharStd q a = charReal ((a.val : ℝ) / (q : ℝ)) := by
  rw [zmodCharStd]
  rw [AddChar.zmodChar_apply]
  rw [zetaRoot]
  rw [← charReal_nat_mul (a.val) (1 / (q : ℝ))]
  congr 1
  · field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne q)]

/-- e_q is a primitive additive character (q != 0). -/
lemma zmodCharStd_isPrimitive (q : ℕ) [NeZero q] : (zmodCharStd q).IsPrimitive := by
  dsimp [zmodCharStd]
  exact AddChar.zmodChar_primitive_of_primitive_root q (zetaRoot_isPrimitiveRoot q (NeZero.ne q))

/-- charReal is periodic modulo integers: e((m + q t)/q) = e(m/q). -/
lemma charReal_periodic_zmod {q : ℕ} (hq : 0 < q) {m n : ℤ}
    (hmn : m ≡ n [ZMOD (q : ℤ)]) :
    charReal ((m : ℝ) / (q : ℝ)) = charReal ((n : ℝ) / (q : ℝ)) := by
  rcases (Int.modEq_iff_add_fac.mp hmn) with ⟨t, ht⟩
  have hm : m = n - (q : ℤ) * t := by omega
  calc
    charReal ((m : ℝ) / (q : ℝ)) = charReal (((n : ℝ) / (q : ℝ)) + (-(t : ℝ))) := by
      congr 1
      rw [hm]
      norm_num
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne']
      ring
    _ = charReal ((n : ℝ) / (q : ℝ)) := by
      simpa using charReal_periodic_int ((n : ℝ) / (q : ℝ)) (-t)

/-- e_q(n * x) = e(n * x.val / q) for n : ℤ: the Gauss-sum bridge. -/
lemma zmodCharStd_mulShift_apply (q : ℕ) [NeZero q] (n : ℤ) (x : ZMod q) :
    (zmodCharStd q).mulShift (n : ZMod q) x = charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  rw [AddChar.mulShift_apply]
  rw [zmodCharStd_apply]
  have heq : ((n : ZMod q) * x : ZMod q) = (((n * (x.val : ℤ) : ℤ) : ZMod q)) := by
    calc
      (n : ZMod q) * x = (n : ZMod q) * (((x.val : ℤ) : ZMod q)) := by
        have hx : x = (((x.val : ℤ) : ZMod q)) := by
          exact ((ZMod.natCast_zmod_val x).symm.trans (Int.cast_natCast (R := ZMod q) (x.val)).symm)
        conv_lhs => rw [hx]
      _ = (((n * (x.val : ℤ) : ℤ) : ZMod q)) := by
        exact (Int.cast_mul (α := ZMod q) (m := n) (n := (x.val : ℤ))).symm
  have hmod : ((n : ZMod q) * x).val ≡ (n * (x.val : ℤ) : ℤ) [ZMOD (q : ℤ)] := by
    have hv : ((((n : ZMod q) * x).val : ℤ) : ZMod q) = ((n * (x.val : ℤ) : ℤ) : ZMod q) := by
      rw [Int.cast_natCast (R := ZMod q) (((n : ZMod q) * x).val)]
      rw [ZMod.natCast_zmod_val ((n : ZMod q) * x)]
      exact heq
    exact (ZMod.intCast_eq_intCast_iff _ _ q).1 hv
  calc
    charReal (((n : ZMod q) * x).val / (q : ℝ)) = charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
      have hmain := charReal_periodic_zmod (hq := NeZero.pos q)
        (m := (((n : ZMod q) * x).val : ℤ)) (n := (n * (x.val : ℤ) : ℤ)) hmod
      convert hmain using 1
      · norm_num
      · norm_num [Int.cast_mul]

/-! ## 2. The Gauss-sum magnitude: |tau(chi)|^2 = q for primitive chi -/

/-- (c : ℂ) * sum of casts = cast of (c * sum). -/
lemma cast_mul_sum {α : Type*} (s : Finset α) (c : ℝ) (f : α → ℝ) :
    (c : ℂ) * (∑ x ∈ s, (f x : ℂ)) = (algebraMap ℝ ℂ) (c * ∑ x ∈ s, f x) := by
  calc
    (c : ℂ) * (∑ x ∈ s, (f x : ℂ)) = ∑ x ∈ s, (c : ℂ) * (f x : ℂ) := by
      rw [Finset.mul_sum]
    _ = ∑ x ∈ s, ((c * f x : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      norm_num
    _ = ((∑ x ∈ s, (c * f x : ℝ)) : ℂ) := by
      simp
    _ = (algebraMap ℝ ℂ) (c * ∑ x ∈ s, f x) := by
      rw [show (∑ x ∈ s, ((c * f x : ℝ) : ℂ)) =
          (algebraMap ℝ ℂ) (∑ x ∈ s, (c * f x : ℝ)) by
            exact (map_sum (algebraMap ℝ ℂ) (fun x => c * f x) s).symm]
      congr 1
      rw [Finset.mul_sum]

/-- Gauss sum of chi against a shifted additive character, in charReal form:
  gaussSum chi (e_q.mulShift n) = sum_{x mod q} chi(x) * e(n * x.val / q). -/
lemma gaussSum_mulShift_apply {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℤ) :
    gaussSum χ ((zmodCharStd q).mulShift (n : ZMod q)) =
      ∑ x : ZMod q, χ x * charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  unfold gaussSum
  apply Finset.sum_congr rfl
  intro x hx
  rw [zmodCharStd_mulShift_apply]

/-- The sum over ZMod q equals the sum over representatives r < q. -/
lemma zmodSum_eq_rangeSum {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    (∑ a : ZMod q, f a) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  refine Finset.sum_bij (s := Finset.univ) (t := Finset.range q) (fun a _ => a.val) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a₁ ha₁ a₂ ha₂ h
    rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂]
    exact congrArg (fun v : ℕ => (v : ZMod q)) h
  · intro r hr
    refine ⟨(r : ZMod q), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  · intro a ha
    congr 1
    exact (ZMod.natCast_zmod_val a).symm

/-- **Parseval (ZMod version)**: sum_{a mod q} |sum_{x mod q} e(a*x.val/q) z x|^2 = q * sum_x |z x|^2. -/
lemma zmodParseval_zmod {q : ℕ} [NeZero q] (z : ZMod q → ℂ) :
    (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2) =
      (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := by
  let z' : ℕ → ℂ := fun r => z (r : ZMod q)
  have hL : (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2)
      = ∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 := by
    rw [zmodSum_eq_rangeSum]
    apply Finset.sum_congr rfl
    intro a ha
    have haq : (a : ZMod q).val = a := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha)]
    rw [haq]
    congr 1
    rw [zmodSum_eq_rangeSum]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : (r : ZMod q).val = r := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
    rw [hrq]
  have hR : (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := by
    congr 1
    rw [zmodSum_eq_rangeSum]
  have hP := zmodParseval (NeZero.pos q) z'
  have hP1 : (∑ a ∈ Finset.range q, ((‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 : ℝ) : ℂ))
      = (q : ℂ) * (∑ r ∈ Finset.range q, ((‖z' r‖ ^ 2 : ℝ) : ℂ)) := by
    simpa [map_sum] using hP
  have hP2 : (∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2)
      = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := by
    have hc : ((∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 : ℝ) : ℂ)
        = (algebraMap ℝ ℂ) ((q : ℝ) * (∑ r ∈ Finset.range q, ‖z' r‖ ^ 2)) := by
      calc
        ((∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 : ℝ) : ℂ)
            = (q : ℂ) * (∑ r ∈ Finset.range q, ((‖z' r‖ ^ 2 : ℝ) : ℂ)) := by
              simpa [map_sum] using hP
        _ = (algebraMap ℝ ℂ) ((q : ℝ) * (∑ r ∈ Finset.range q, ‖z' r‖ ^ 2)) := by
              exact cast_mul_sum (Finset.range q) (q : ℝ) (fun r => ‖z' r‖ ^ 2)
    exact Complex.ofReal_inj.mp hc
  calc
    (∑ a : ZMod q, ‖∑ x : ZMod q, charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) * z x‖ ^ 2)
        = ∑ a ∈ Finset.range q, ‖∑ r ∈ Finset.range q, charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z' r‖ ^ 2 := hL
    _ = (q : ℝ) * ∑ r ∈ Finset.range q, ‖z' r‖ ^ 2 := hP2
    _ = (q : ℝ) * ∑ x : ZMod q, ‖z x‖ ^ 2 := hR.symm

/-! ## 3. |tau(chi)|^2 = q for primitive chi -/

/-- |chi(a)| = 1 for unit a. -/
lemma dirichletChar_norm_unit {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    ‖χ a‖ = 1 := by
  haveI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let n : ℕ := Fintype.card (ZMod q)ˣ
  have hn : n ≠ 0 := ne_of_gt (Fintype.card_pos (α := (ZMod q)ˣ))
  have hpow_u : ha.unit ^ n = 1 := pow_card_eq_one (G := (ZMod q)ˣ) (x := ha.unit)
  have hspec : (a : ZMod q) = (ha.unit : ZMod q) := ha.unit_spec.symm
  have hpow_l : a ^ n = 1 := by
    rw [hspec]
    simpa using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpow_u
  have hpow_χ : (χ a) ^ n = 1 := by
    rw [← map_pow, hpow_l, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow_χ hn

/-- The L2 mass of |chi| over all residues is phi(q). -/
lemma charNormSq_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = (q.totient : ℝ) := by
  calc
    (∑ a : ZMod q, ‖χ a‖ ^ 2) = ∑ a : ZMod q, (if IsUnit a then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : IsUnit a
      · have hnorm : ‖χ a‖ = 1 := dirichletChar_norm_unit χ h
        simp [h, hnorm]
      · have h0 : χ a = 0 := χ.map_nonunit h
        simp [h, h0]
    _ = (q.totient : ℝ) := by
      -- sum of the unit indicator = number of units = phi(q)
      rw [Finset.sum_boole]
      have hcard : (Finset.univ.filter (fun a : ZMod q => IsUnit a)).card = q.totient := by
        -- {a | IsUnit a} in bijection with (ZMod q)ˣ
        rw [← Fintype.card_subtype]
        refine (Fintype.card_congr ?_).trans (ZMod.card_units_eq_totient q)
        refine ⟨fun x => x.2.unit, fun u => ⟨(u : ZMod q), ⟨u, rfl⟩⟩, ?_, ?_⟩
        · intro x
          apply Subtype.ext
          exact x.2.unit_spec.symm
        · intro u
          ext
          rfl
      simpa [hcard]

/-- chi^{-1} a = star (chi a) for all a (complex characters). -/
lemma char_inv_eq_star {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ⁻¹ a = star (χ a) := by
  rw [MulChar.star_apply']

/-- **Gauss-sum magnitude**: |tau(chi)|^2 = q for primitive chi mod q.
  Via Parseval (zmodParseval_zmod with z = chi) and mathlib's
  gaussSum_mulShift_of_isPrimitive. -/
lemma gaussSumSq_eq_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (zmodCharStd q)‖ ^ 2 = (q : ℝ) := by
  -- Parseval with z = chi: Σ_a |Σ_x e(a x) chi x|^2 = q * Σ |chi|^2
  have hP := zmodParseval_zmod (z := χ)
  -- inner sum = gaussSum chi (e_q.mulShift a)
  have hL : (∑ a : ZMod q, ‖gaussSum χ ((zmodCharStd q).mulShift a)‖ ^ 2) =
      (q : ℝ) * ∑ x : ZMod q, ‖χ x‖ ^ 2 := by
    rw [← hP]
    apply Finset.sum_congr rfl
    intro a ha
    congr 1
    congr 1
    have hb := gaussSum_mulShift_apply χ (n := (a.val : ℤ))
    have hz : ((a.val : ℤ) : ZMod q) = a := by
      rw [Int.cast_natCast (R := ZMod q) (a.val)]
      exact ZMod.natCast_zmod_val a
    have hb' : gaussSum χ ((zmodCharStd q).mulShift a) =
        ∑ x : ZMod q, χ x * charReal ((a.val : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
      simpa [hz] using hb
    rw [hb']
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm]
  -- |gaussSum chi (e.mulShift a)|^2 = |chi^{-1} a|^2 * |tau|^2 via the mulShift identity
  have hR : (∑ a : ZMod q, ‖gaussSum χ ((zmodCharStd q).mulShift a)‖ ^ 2) =
      ‖gaussSum χ (zmodCharStd q)‖ ^ 2 * (q.totient : ℝ) := by
    calc
      (∑ a : ZMod q, ‖gaussSum χ ((zmodCharStd q).mulShift a)‖ ^ 2)
          = ∑ a : ZMod q, ‖χ⁻¹ a * gaussSum χ (zmodCharStd q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [gaussSum_mulShift_of_isPrimitive (e := zmodCharStd q) hχ a]
      _ = ∑ a : ZMod q, ‖χ⁻¹ a‖ ^ 2 * ‖gaussSum χ (zmodCharStd q)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [norm_mul]
            ring
      _ = ‖gaussSum χ (zmodCharStd q)‖ ^ 2 * (∑ a : ZMod q, ‖χ⁻¹ a‖ ^ 2) := by
            rw [← Finset.sum_mul]
            ring
      _ = ‖gaussSum χ (zmodCharStd q)‖ ^ 2 * (q.totient : ℝ) := by
            rw [charNormSq_sum (χ⁻¹)]
  -- combine: |tau|^2 * phi(q) = q * phi(q)
  have hEq : ‖gaussSum χ (zmodCharStd q)‖ ^ 2 * (q.totient : ℝ) = (q : ℝ) * (q.totient : ℝ) := by
    rw [← hR, hL]
    congr 1
    exact charNormSq_sum χ
  have hφ : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  exact mul_right_cancel₀ hφ hEq

/-! ## 4. Gauss-sum Fourier inversion for primitive characters -/

/-- star preserves FactorsThrough: (star chi).FactorsThrough d iff chi.FactorsThrough d. -/
lemma star_factorsThrough {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ) :
    (star χ).FactorsThrough d ↔ χ.FactorsThrough d := by
  by_cases hd : d ∣ q
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    have hto : (star χ).toUnitHom = (Units.map (starRingEnd ℂ).toMonoidHom).comp χ.toUnitHom := by
      ext u
      change star ((χ.toUnitHom u : ℂ)) = star ((χ.toUnitHom u : ℂ))
      rfl
    have hker : ((star χ).toUnitHom).ker = χ.toUnitHom.ker := by
      rw [hto]
      apply le_antisymm
      · intro u hu
        rw [MonoidHom.mem_ker] at hu ⊢
        apply Units.ext
        -- hu : (Units.map (starRingEnd ℂ).toMonoidHom (χ.toUnitHom u)) = 1
        -- star (↑(χ.toUnitHom u)) = 1
        have hstar : star ((χ.toUnitHom u : ℂ)) = (1 : ℂ) := by
          have hc := congrArg (fun w : ℂˣ => (w : ℂ)) hu
          simpa [Units.coe_map] using hc
        have hval : ((χ.toUnitHom u : ℂ) : ℂ) = (1 : ℂ) := by
          have hs : star (star ((χ.toUnitHom u : ℂ))) = star (1 : ℂ) := by rw [hstar]
          simpa using hs
        exact hval
      · intro u hu
        rw [MonoidHom.mem_ker] at hu ⊢
        apply Units.ext
        have hval : ((χ.toUnitHom u : ℂ) : ℂ) = (1 : ℂ) := by
          simpa [Units.ext_iff] using hu
        simp [Units.coe_map]
        rw [← MulChar.coe_toUnitHom χ u, hval]
        simp
    rw [hker]
  · constructor <;> intro h <;> exact False.elim (hd h.dvd)

/-- The conductor is preserved by star. -/
lemma star_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (star χ).conductor = χ.conductor := by
  apply le_antisymm
  · have hf : (star χ).FactorsThrough χ.conductor :=
      (star_factorsThrough χ χ.conductor).2 (DirichletCharacter.factorsThrough_conductor χ)
    exact Nat.sInf_le (by simpa [DirichletCharacter.mem_conductorSet_iff] using hf)
  · have hf : χ.FactorsThrough (star χ).conductor :=
      (star_factorsThrough χ (star χ).conductor).1 (DirichletCharacter.factorsThrough_conductor (star χ))
    exact Nat.sInf_le (by simpa [DirichletCharacter.mem_conductorSet_iff] using hf)

/-- star preserves primitivity. -/
lemma star_isPrimitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    (star χ).IsPrimitive := by
  unfold DirichletCharacter.IsPrimitive
  rw [star_conductor, hχ]

/-- The additive sum T(x) = sum_n a_n * e(n * x.val / q) for x : ZMod q. -/
def charAddSum (a : ℤ → ℂ) (M : ℤ) (N q : ℕ) (x : ZMod q) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))

/-- e(n·x/q) written with the single quotient x/q: argument-form bridge. -/
lemma charReal_mul_div {q : ℕ} [NeZero q] (n : ℤ) (x : ZMod q) :
    charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ))) =
      charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
  congr 1
  field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne q)]

/-- The Fourier transform of a primitive character: for all n,
  sum_{x mod q} star(chi x) * e(n x / q) = chi n * tau(star chi). -/
lemma primitiveFourier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (n : ℤ) :
    (∑ x : ZMod q, star (χ x) * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))) =
      χ (n : ZMod q) * gaussSum (star χ) (zmodCharStd q) := by
  calc
    (∑ x : ZMod q, star (χ x) * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ))))
        = ∑ x : ZMod q, star (χ x) * charReal ((n : ℝ) * (x.val : ℝ) / (q : ℝ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [charReal_mul_div]
    _ = gaussSum (star χ) ((zmodCharStd q).mulShift (n : ZMod q)) := by
          exact (gaussSum_mulShift_apply (star χ) n).symm
    _ = χ (n : ZMod q) * gaussSum (star χ) (zmodCharStd q) := by
          have hprim := star_isPrimitive χ hχ
          have hms := gaussSum_mulShift_of_isPrimitive (e := zmodCharStd q) hprim (n : ZMod q)
          -- hms : gaussSum (star χ) (e.mulShift n) = (star χ)⁻¹ n * gaussSum (star χ) e
          rw [hms]
          -- (star χ)⁻¹ n = chi n
          have hinv : (star χ)⁻¹ (n : ZMod q) = χ (n : ZMod q) := by
            rw [← MulChar.star_apply' (χ := (star χ)) (a := (n : ZMod q))]
            simp
          rw [hinv]

/-- **Primitive inversion**: for primitive chi mod q,
  |S_chi|^2 = (1/q) * |sum_{x mod q} star(chi x) * T(x)|^2
  where S_chi = sum_n a_n chi(n) and T(x) = sum_n a_n e(n x.val / q). -/
lemma primitiveInversion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2 =
      (1 / (q : ℝ)) * ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2 := by
  -- sum_x star(chi x) * T(x) = tau(star chi) * S_chi
  have hsum : (∑ x : ZMod q, star (χ x) * charAddSum a M N q x) =
      gaussSum (star χ) (zmodCharStd q) * (∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)) := by
    unfold charAddSum
    calc
      (∑ x : ZMod q, star (χ x) * (∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))))
          = ∑ x : ZMod q, ∑ n ∈ Finset.Icc (M + 1) (M + N),
              star (χ x) * (a n * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [mul_comm, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro n hn
            ring
      _ = ∑ n ∈ Finset.Icc (M + 1) (M + N), ∑ x : ZMod q,
            star (χ x) * (a n * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))) := by
            rw [Finset.sum_comm]
      _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * (∑ x : ZMod q, star (χ x) * charReal ((n : ℝ) * ((x.val : ℝ) / (q : ℝ)))) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = ∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * (χ (n : ZMod q) * gaussSum (star χ) (zmodCharStd q)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [primitiveFourier χ hχ n]
      _ = gaussSum (star χ) (zmodCharStd q) * (∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
  -- |sum_x star(chi x) * T(x)|^2 = q * |S_chi|^2
  have hnorm : ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2 =
      (q : ℝ) * ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2 := by
    rw [hsum]
    have hτ : ‖gaussSum (star χ) (zmodCharStd q)‖ ^ 2 = (q : ℝ) :=
      gaussSumSq_eq_conductor (star χ) (star_isPrimitive χ hχ)
    rw [norm_mul]
    rw [mul_pow]
    rw [hτ]
  -- |S_chi|^2 = (1/q) * |sum_x star(chi x) * T(x)|^2
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'
  calc
    ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2
        = ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2 / (q : ℝ) := by
          rw [hnorm]
          field_simp [hq]
    _ = (1 / (q : ℝ)) * ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2 := by
          field_simp [hq]

/-! ## 5. Unit Parseval and the Bombieri-Davenport stacking -/

/-- Orthogonality with star: sum_chi star(chi a) * chi b = phi(q) * [a = b and a unit]. -/
lemma charOrthSum_star {q : ℕ} [NeZero q] (a b : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
      if IsUnit a ∧ IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
  have h := charOrthSum (Nat.pos_of_ne_zero (NeZero.ne q)) a b
  by_cases hcond : IsUnit a ∧ IsUnit b ∧ a = b
  · rw [if_pos hcond]
    -- h : Σ_χ χ a·star(χ b) = φ (cond true)
    rw [if_pos hcond] at h
    -- goal: Σ_χ star(χ a)·χ b = φ — star of h
    have hstar := congrArg star h
    -- hstar : star (Σ_χ χ a·star(χ b)) = star (φ : ℂ)
    -- LHS: Σ_χ star(χ a)·star(star(χ b)) = Σ_χ star(χ a)·χ b
    calc
      (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b)
          = star (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) := by
            change (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
              (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b))
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro χ hχ
            change star (χ a) * χ b = star (χ a * star (χ b))
            rw [star_mul, star_star]
            ring
      _ = star ((q.totient : ℂ)) := hstar
      _ = (q.totient : ℂ) := by simp
  · rw [if_neg hcond]
    rw [if_neg hcond] at h
    -- goal: Σ_χ star(χ a)·χ b = 0 — from h : Σ χ a·star(χ b) = 0
    have hstar := congrArg star h
    calc
      (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b)
          = star (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) := by
            change (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
              (starRingEnd ℂ) (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b))
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro χ hχ
            change star (χ a) * χ b = star (χ a * star (χ b))
            rw [star_mul, star_star]
            ring
      _ = star (0 : ℂ) := hstar
      _ = 0 := by simp

/-- **Unit Parseval**: sum_chi ||sum_x star(chi x) T x||^2 = phi(q) * sum over units |T x|^2. -/
lemma charParseval_units {q : ℕ} [NeZero q] (T : ZMod q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2) =
      (q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0) := by
  have hC : (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ)) =
      (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0)) := by
    calc
      (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ))
          = ∑ x : ZMod q, ∑ y : ZMod q,
              T x * star (T y) * (∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y) := by
            -- expand the squares and swap the sums
            calc
              (∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ))
                  = ∑ χ : DirichletCharacter ℂ q, ∑ x : ZMod q, ∑ y : ZMod q,
                      (star (χ x) * T x) * star (star (χ y) * T y) := by
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    exact normSq_sum_eq_sum_mul_star (Finset.univ)
                      (fun x : ZMod q => star (χ x) * T x)
              _ = ∑ x : ZMod q, ∑ y : ZMod q,
                    T x * star (T y) * (∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro χ hχ
                    rw [star_mul, star_star]
                    ring
      _ = ∑ x : ZMod q, ∑ y : ZMod q,
            T x * star (T y) * (if IsUnit x ∧ IsUnit y ∧ x = y then (q.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            exact congrArg (fun t : ℂ => T x * star (T y) * t) (charOrthSum_star x y)
      _ = ∑ x : ZMod q, T x * star (T x) * (if IsUnit x then (q.totient : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hx' : IsUnit x
            · rw [Finset.sum_eq_single x]
              · simp [hx']
              · intro y hy hxy
                have hfalse : ¬ (IsUnit x ∧ IsUnit y ∧ x = y) := by
                  intro h
                  exact hxy (h.2.2.symm)
                simp [hfalse]
              · intro hnx
                exact False.elim (hnx (Finset.mem_univ x))
            · simp [hx']
      _ = (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0) := by
            have h1 : (∑ x : ZMod q, T x * star (T x) * (if IsUnit x then (q.totient : ℂ) else 0)) =
                ∑ x : ZMod q, (if IsUnit x then T x * star (T x) * (q.totient : ℂ) else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : IsUnit x <;> simp [h]
            have h2 : (∑ x : ZMod q, (if IsUnit x then T x * star (T x) * (q.totient : ℂ) else 0)) =
                (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases h : IsUnit x
              · have hmul : T x * star (T x) = (‖T x‖ ^ 2 : ℂ) := by
                  have hc := Complex.mul_conj (T x)
                  rw [Complex.normSq_eq_norm_sq] at hc
                  simpa using hc
                simp [h]
                change T x * star (T x) * (q.totient : ℂ) = (q.totient : ℂ) * (‖T x‖ ^ 2 : ℂ)
                rw [hmul]
                ring
              · simp [h]
            exact h1.trans h2
  -- convert hC to ℝ
  exact Complex.ofReal_inj.mp (by
    calc
      ((∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℝ) : ℂ)
          = ∑ χ : DirichletCharacter ℂ q, (‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2 : ℂ) := by
            simpa using (map_sum (algebraMap ℝ ℂ)
              (fun χ : DirichletCharacter ℂ q => ‖∑ x : ZMod q, star (χ x) * T x‖ ^ 2)
              (Finset.univ))
      _ = (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0)) := hC
      _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
            have hmid : (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) =
                (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
              simpa [cast_mul_sum]
            calc
              (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0))
                  = (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases h : IsUnit x <;> simp [h]
              _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := hmid)

/-- The set of reduced fractions {r/q : 1 <= q <= Q, 0 < r < q, (r, q) = 1}. -/
def reducedFracs (Q : ℕ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion (fun q =>
    ((Finset.range q).filter (fun r => r.Coprime q)).image (fun r : ℕ => (r : ℝ) / (q : ℝ)))

/-- reducedFracs is contained in rationalPoints (each reduced fraction is a rational point). -/
lemma reducedFracs_subset_rationalPoints (Q : ℕ) : reducedFracs Q ⊆ rationalPoints Q := by
  intro x hx
  rw [reducedFracs] at hx
  rw [Finset.mem_biUnion] at hx
  rcases hx with ⟨q, hq, hx2⟩
  rcases Finset.mem_image.mp hx2 with ⟨r, hr, rfl⟩
  rw [rationalPoints, Finset.mem_biUnion]
  refine ⟨q, hq, ?_⟩
  exact Finset.mem_image.mpr ⟨r, (Finset.mem_filter.mp hr).1, rfl⟩

/-- The double sum over reduced pairs equals the sum over reducedFracs (the map is injective). -/
lemma reducedFracs_sum {Q : ℕ} {β : Type*} [AddCommMonoid β] (T : ℝ → β) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
      T ((r : ℝ) / (q : ℝ))) =
      ∑ x ∈ reducedFracs Q, T x := by
  rw [← Finset.sum_sigma (s := Finset.Icc 1 Q)
    (t := fun q => (Finset.range q).filter (fun r => r.Coprime q))
    (f := fun p : Σ q : ℕ, ℕ => T ((p.2 : ℝ) / (p.1 : ℝ)))]
  refine Finset.sum_bij (s := (Finset.Icc 1 Q).sigma (fun q =>
      (Finset.range q).filter (fun r => r.Coprime q)))
    (t := reducedFracs Q)
    (fun p _ => ((p.2 : ℝ) / (p.1 : ℝ))) ?_ ?_ ?_ ?_
  · -- hi: i p = p.2/p.1 ∈ reducedFracs
    intro p hp
    rw [Finset.mem_sigma] at hp
    rw [reducedFracs, Finset.mem_biUnion]
    refine ⟨p.1, hp.1, ?_⟩
    exact Finset.mem_image.mpr ⟨p.2, hp.2, rfl⟩
  · -- i_inj: reduced fractions r₁/q₁ = r₂/q₂ force (q₁, r₁) = (q₂, r₂)
    intro p₁ hp₁ p₂ hp₂ h
    rw [Finset.mem_sigma] at hp₁ hp₂
    -- h : (p₁.2 : ℝ) / (p₁.1 : ℝ) = (p₂.2 : ℝ) / (p₂.1 : ℝ)
    have hpos1 : 0 < p₁.1 := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp hp₁.1).1
    have hpos2 : 0 < p₂.1 := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp hp₂.1).1
    have hq1ne : (p₁.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos1)
    have hq2ne : (p₂.1 : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos2)
    have hn : p₁.2 * p₂.1 = p₁.1 * p₂.2 := by
      have hh : (p₁.2 : ℝ) / (p₁.1 : ℝ) = (p₂.2 : ℝ) / (p₂.1 : ℝ) := h
      field_simp [hq1ne, hq2ne] at hh
      exact_mod_cast hh
    have hcross : (p₁.2 : ℤ) * (p₂.1 : ℤ) = (p₁.1 : ℤ) * (p₂.2 : ℤ) := by
      exact_mod_cast hn
    have hcop1 : p₁.2.Coprime p₁.1 := (Finset.mem_filter.mp hp₁.2).2
    have hcop2 : p₂.2.Coprime p₂.1 := (Finset.mem_filter.mp hp₂.2).2
    have hdvd1 : p₁.1 ∣ p₂.1 := by
      have hd : p₁.1 ∣ p₁.2 * p₂.1 := by
        have hdz : (p₁.1 : ℤ) ∣ (p₁.2 : ℤ) * (p₂.1 : ℤ) := by
          rw [hcross]
          exact dvd_mul_right (p₁.1 : ℤ) (p₂.2 : ℤ)
        exact Int.natCast_dvd_natCast.mp (by simpa using hdz)
      exact hcop1.symm.dvd_of_dvd_mul_left hd
    have hdvd2 : p₂.1 ∣ p₁.1 := by
      have hd : p₂.1 ∣ p₂.2 * p₁.1 := by
        have hcross' : (p₂.2 : ℤ) * (p₁.1 : ℤ) = (p₂.1 : ℤ) * (p₁.2 : ℤ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcross.symm
        have hdz : (p₂.1 : ℤ) ∣ (p₂.2 : ℤ) * (p₁.1 : ℤ) := by
          rw [hcross']
          exact dvd_mul_right (p₂.1 : ℤ) (p₁.2 : ℤ)
        exact Int.natCast_dvd_natCast.mp (by simpa using hdz)
      exact hcop2.symm.dvd_of_dvd_mul_left hd
    have hqeq : p₁.1 = p₂.1 := Nat.dvd_antisymm hdvd1 hdvd2
    have hreq : p₁.2 = p₂.2 := by
      have hz : (p₁.2 : ℤ) * (p₁.1 : ℤ) = (p₂.2 : ℤ) * (p₁.1 : ℤ) := by
        have h1 : (p₁.2 : ℤ) * (p₁.1 : ℤ) = (p₁.1 : ℤ) * (p₂.2 : ℤ) := by
          simpa [hqeq] using hcross
        simpa [mul_comm] using h1
      have hc : (p₁.2 : ℤ) = (p₂.2 : ℤ) := mul_right_cancel₀ (by exact_mod_cast (ne_of_gt hpos1)) hz
      exact_mod_cast hc
    apply Sigma.ext hqeq
    simpa [hqeq] using hreq
  · -- i_surj: every x ∈ reducedFracs comes from a reduced pair
    intro x hx
    rw [reducedFracs, Finset.mem_biUnion] at hx
    rcases hx with ⟨q, hq, hx2⟩
    rcases Finset.mem_image.mp hx2 with ⟨r, hr, rfl⟩
    refine ⟨⟨q, r⟩, ?_, rfl⟩
    rw [Finset.mem_sigma]
    exact ⟨hq, hr⟩
  · -- h: f p = g (i p)
    intro p hp
    rfl

/-! ## 6. The Bombieri-Davenport lemma -/

/-- charAddSum at the representative (r : ZMod q) equals the range-sum for r < q. -/
lemma charAddSum_natCast {q : ℕ} [NeZero q] (a : ℤ → ℂ) (M : ℤ) (N : ℕ) {r : ℕ}
    (hr : r < q) :
    charAddSum a M N q (r : ZMod q) =
      ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) := by
  unfold charAddSum
  have hrq : (r : ZMod q).val = r := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  rw [hrq]

/-- The unit-class sum of |T|^2 equals the sum over reduced residues r < q. -/
lemma unitsSum_eq_reducedFracs {q : ℕ} [NeZero q] (T : ZMod q → ℂ) :
    (∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) =
      ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), ‖T (r : ZMod q)‖ ^ 2 := by
  calc
    (∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0))
        = ∑ r ∈ Finset.range q,
            (if IsUnit (r : ZMod q) then ‖T (r : ZMod q)‖ ^ 2 else 0) := by
          rw [zmodSum_eq_rangeSum (f := fun x : ZMod q =>
            if IsUnit x then ‖T x‖ ^ 2 else 0)]
    _ = ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q), ‖T (r : ZMod q)‖ ^ 2 := by
          rw [← Finset.sum_filter]
          have hext : (Finset.range q).filter (fun r : ℕ => IsUnit (r : ZMod q)) =
              (Finset.range q).filter (fun r : ℕ => r.Coprime q) := by
            ext r
            constructor
            · intro h
              rw [Finset.mem_filter] at h ⊢
              exact ⟨h.1, (ZMod.isUnit_iff_coprime r q).1 h.2⟩
            · intro h
              rw [Finset.mem_filter] at h ⊢
              exact ⟨h.1, (ZMod.isUnit_iff_coprime r q).2 h.2⟩
          rw [hext]

/-- **Bombieri-Davenport lemma**: sum_{1 <= q <= Q} (q/phi(q)) * sum over primitive chi
  of |sum_n a_n chi(n)|^2 is bounded by the additive large sieve on the Farey set
  X_Q = {r/q : 1 <= q <= Q, 0 <= r < q, gcd(r,q)=1}. -/
theorem bombieriDavenport_le (Q : ℕ) (hQ : 0 < Q) (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2))
      ≤ largeSieveBound N (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := by
  -- per-modulus inequality: (q/phi(q)) * sum_{chi prim} |S_chi|^2 <= sum over reduced r < q |T(r/q)|^2
  have hmain : ∀ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2)
        ≤ ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2 := by
    intro q hq
    haveI : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    let primChars : Finset (DirichletCharacter ℂ q) :=
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
    have h1 : (∑ χ ∈ primChars, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2) ≤
        (1 / (q : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
          ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) := by
      calc
        (∑ χ ∈ primChars, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2)
            ≤ ∑ χ ∈ primChars, (1 / (q : ℝ)) * ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro χ hχ
              rw [primitiveInversion χ (Finset.mem_filter.mp hχ).2 a M N]
        _ = (1 / (q : ℝ)) * (∑ χ ∈ primChars, ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) := by
              rw [Finset.mul_sum]
        _ ≤ (1 / (q : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
              ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) := by
              have hsub : (∑ χ ∈ primChars, ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) ≤
                  (∑ χ : DirichletCharacter ℂ q, ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) :=
                Finset.sum_le_sum_of_subset_of_nonneg (by intro χ hχ; exact Finset.mem_univ χ)
                  (fun χ hχ hnot => sq_nonneg (‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖))
              exact mul_le_mul_of_nonneg_left hsub (by positivity)
    calc
      ((q : ℝ) / (q.totient : ℝ)) * (∑ χ ∈ primChars,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2)
          ≤ ((q : ℝ) / (q.totient : ℝ)) * ((1 / (q : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
              ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖∑ x : ZMod q, star (χ x) * charAddSum a M N q x‖ ^ 2) := by
            have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp hq).1
            field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne',
              show (q.totient : ℝ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hqpos).ne']
      _ = (1 / (q.totient : ℝ)) * ((q.totient : ℝ) *
            (∑ x : ZMod q, (if IsUnit x then ‖charAddSum a M N q x‖ ^ 2 else 0))) := by
            rw [charParseval_units (T := charAddSum a M N q)]
      _ = (1 / (q.totient : ℝ)) * ((q.totient : ℝ) *
            (∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
              ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2)) := by
            have hpu : (∑ x : ZMod q, (if IsUnit x then ‖charAddSum a M N q x‖ ^ 2 else 0)) =
                ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
                  ‖charAddSum a M N q (r : ZMod q)‖ ^ 2 :=
              unitsSum_eq_reducedFracs (T := charAddSum a M N q)
            have hcr : ∀ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
                ‖charAddSum a M N q (r : ZMod q)‖ ^ 2 =
                  ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2 := by
              intro r hr
              exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
                (charAddSum_natCast a M N (Finset.mem_range.mp (Finset.mem_filter.mp hr).1))
            calc
              (1 / (q.totient : ℝ)) * ((q.totient : ℝ) *
                  (∑ x : ZMod q, (if IsUnit x then ‖charAddSum a M N q x‖ ^ 2 else 0)))
                  = (1 / (q.totient : ℝ)) * ((q.totient : ℝ) *
                      (∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
                        ‖charAddSum a M N q (r : ZMod q)‖ ^ 2)) := by
                    rw [hpu]
              _ = (1 / (q.totient : ℝ)) * ((q.totient : ℝ) *
                      (∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
                        ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2)) := by
                    congr 1
                    congr 1
                    apply Finset.sum_congr rfl
                    intro r hr
                    exact hcr r hr
      _ = ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2 := by
            have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp hq).1
            field_simp [show (q.totient : ℝ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hqpos).ne']
  -- assemble over q and use the additive large sieve on the Farey set
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2))
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ (Finset.range q).filter (fun r => r.Coprime q),
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ)))‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          exact hmain q hq
    _ = ∑ x ∈ reducedFracs Q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * x)‖ ^ 2 := by
          exact reducedFracs_sum (fun x : ℝ =>
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * x)‖ ^ 2)
    _ ≤ ∑ x ∈ rationalPoints Q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * charReal ((n : ℝ) * x)‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (reducedFracs_subset_rationalPoints Q) (fun _ _ _ => sq_nonneg _)
    _ ≤ largeSieveBound N (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := by
          simpa [mul_comm] using largeSieveRationalPoints M N Q hQ a

/-! ## 7. Application to Type I coefficients and limitations -/

/-- The Icc (0 : ℤ) (m : ℤ) sum of the vaughanFirst coefficients equals the
  character sum over range (m + 1) (bridge between the BD lemma and
  panTypeIV1CharSum). -/
lemma vaughanFirst_Icc_charSum {q m u : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      (if 0 ≤ n then (vaughanFirst n.toNat u : ℂ) else 0) * χ (n : ZMod q)) =
      ∑ n ∈ Finset.range (m + 1), (vaughanFirst n u : ℂ) * χ (n : ZMod q) := by
  refine Finset.sum_bij (s := Finset.Icc (0 : ℤ) (m : ℤ)) (t := Finset.range (m + 1))
    (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    -- 0 ≤ n and n ≤ m → n.toNat ≤ m
    have hto : n.toNat ≤ m := by
      have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1
      exact_mod_cast (by simpa [hz] using hn.2)
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    -- n₁.toNat = n₂.toNat → n₁ = n₂ (both in Icc, so nonneg)
    have h₁ : 0 ≤ n₁ := (Finset.mem_Icc.mp hn₁).1
    have h₂ : 0 ≤ n₂ := (Finset.mem_Icc.mp hn₂).1
    calc
      n₁ = (n₁.toNat : ℤ) := (Int.toNat_of_nonneg h₁).symm
      _ = (n₂.toNat : ℤ) := by rw [h]
      _ = n₂ := Int.toNat_of_nonneg h₂
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by exact_mod_cast (Nat.zero_le n), by exact_mod_cast (Nat.le_of_lt_succ hn)⟩
    · -- (n : ℤ).toNat = n
      exact Int.toNat_natCast n
  · intro n hn
    -- the summands match: (if 0 ≤ (n : ℤ) then vaughanFirst (n : ℤ).toNat u else 0) = vaughanFirst n u
    have hnon : 0 ≤ (n : ℤ) := (Finset.mem_Icc.mp hn).1
    have hto : (n.toNat : ZMod q) = (n : ZMod q) := by
      rw [← Int.cast_natCast (R := ZMod q) n.toNat]
      exact congrArg (fun z : ℤ => (z : ZMod q)) (Int.toNat_of_nonneg hnon)
    simp [hnon, hto]

/-- The norm-square of the interval coefficients equals the range sum of
  vaughanFirst(n,u)^2. -/
lemma vaughanFirst_Icc_normSq (m u : ℕ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      ‖(if 0 ≤ n then (vaughanFirst n.toNat u : ℂ) else 0)‖ ^ 2) =
      ∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2 := by
  refine Finset.sum_bij (s := Finset.Icc (0 : ℤ) (m : ℤ)) (t := Finset.range (m + 1))
    (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1
    have hto : n.toNat ≤ m := by
      exact_mod_cast (by simpa [hz] using hn.2)
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    have h₁ : 0 ≤ n₁ := (Finset.mem_Icc.mp hn₁).1
    have h₂ : 0 ≤ n₂ := (Finset.mem_Icc.mp hn₂).1
    calc
      n₁ = (n₁.toNat : ℤ) := (Int.toNat_of_nonneg h₁).symm
      _ = (n₂.toNat : ℤ) := by rw [h]
      _ = n₂ := Int.toNat_of_nonneg h₂
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by exact_mod_cast (Nat.zero_le n), by exact_mod_cast (Nat.le_of_lt_succ hn)⟩
    · exact Int.toNat_natCast n
  · intro n hn
    have hnon : 0 ≤ (n : ℤ) := (Finset.mem_Icc.mp hn).1
    -- ‖(vaughanFirst n u : ℂ)‖² = (vaughanFirst n u)²
    have hnorm : ‖(vaughanFirst n.toNat u : ℂ)‖ ^ 2 = (vaughanFirst n.toNat u) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa [pow_two] using Complex.normSq_ofReal (vaughanFirst n.toNat u)
    simp [hnon, hnorm]

/-- **Bombieri-Davenport for the type-I coefficients**: the primitive-character
  (q/phi(q))-weighted mean bound for vaughanFirst(n,u), i.e. the corrected
  analytic input for the type-I mean value. The literal
  panTypeICharSquareMeanBound (all characters, weight mu^2 3^omega, constant C)
  is FALSE as stated; see the module header. -/
theorem bombieriDavenport_vaughanFirst (Q m u : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖panTypeIV1CharSum q m u χ‖ ^ 2))
      ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
  let a : ℤ → ℂ := fun n => if 0 ≤ n then (vaughanFirst n.toNat u : ℂ) else 0
  have hbd := bombieriDavenport_le Q hQ a (-1) (m + 1)
  -- rewrite the character sums: Σ_{Icc 0 (m:ℤ)} a n·chi(n) = panTypeIV1CharSum q m u chi
  have hL : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)‖ ^ 2 = ‖panTypeIV1CharSum q m u χ‖ ^ 2 := by
    intro q hq χ hχ
    congr 1
    unfold panTypeIV1CharSum
    rw [← vaughanFirst_Icc_charSum χ]
  -- rewrite the norm-square: Σ_{Icc}‖a n‖² = Σ_{range}(vaughanFirst n u)²
  have hR : (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2 := by
    simpa [a] using vaughanFirst_Icc_normSq m u
  -- now convert hbd
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖panTypeIV1CharSum q m u χ‖ ^ 2))
        ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) *
            (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) := by
          -- rewrite the character sums in hbd's LHS
          rw [show (∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (q.totient : ℝ)) *
              (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                ‖panTypeIV1CharSum q m u χ‖ ^ 2)) =
              (∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (q.totient : ℝ)) *
                (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)‖ ^ 2)) by
            apply Finset.sum_congr rfl
            intro q hq
            congr 1
            apply Finset.sum_congr rfl
            intro χ hχ
            exact (hL q hq χ hχ).symm]
          have hn1 : (-1 + 1 : ℤ) = 0 := by norm_num
          have hn2 : (-1 + ((m : ℤ) + 1) : ℤ) = (m : ℤ) := by omega
          simpa [hn1, hn2] using hbd
    _ ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) := by
          rw [hR]

/-! ## 7b. Application to the type-II assembly (panTypeIIV3CharSum)

The mirror of section 7 for the type-II coefficients: Bombieri-Davenport for
`vaughanThird(n,u,v)` with the (q/phi(q)) primitive-character weight,
`bombieriDavenport_vaughanThird`, the corrected analytic input for the type-II
mean value. -/

/-- The Icc (0 : ℤ) (m : ℤ) sum of the vaughanThird coefficients equals the
  character sum over range (m + 1) (bridge between the BD lemma and
  panTypeIIV3CharSum). -/
lemma vaughanThird_Icc_charSum {q m u v : ℕ} (χ : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      (if 0 ≤ n then (vaughanThird n.toNat u v : ℂ) else 0) * χ (n : ZMod q)) =
      ∑ n ∈ Finset.range (m + 1), (vaughanThird n u v : ℂ) * χ (n : ZMod q) := by
  refine Finset.sum_bij (s := Finset.Icc (0 : ℤ) (m : ℤ)) (t := Finset.range (m + 1))
    (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    -- 0 ≤ n and n ≤ m → n.toNat ≤ m
    have hto : n.toNat ≤ m := by
      have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1
      exact_mod_cast (by simpa [hz] using hn.2)
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    -- n₁.toNat = n₂.toNat → n₁ = n₂ (both in Icc, so nonneg)
    have h₁ : 0 ≤ n₁ := (Finset.mem_Icc.mp hn₁).1
    have h₂ : 0 ≤ n₂ := (Finset.mem_Icc.mp hn₂).1
    calc
      n₁ = (n₁.toNat : ℤ) := (Int.toNat_of_nonneg h₁).symm
      _ = (n₂.toNat : ℤ) := by rw [h]
      _ = n₂ := Int.toNat_of_nonneg h₂
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by exact_mod_cast (Nat.zero_le n), by exact_mod_cast (Nat.le_of_lt_succ hn)⟩
    · -- (n : ℤ).toNat = n
      exact Int.toNat_natCast n
  · intro n hn
    -- the summands match: (if 0 ≤ (n : ℤ) then vaughanThird (n : ℤ).toNat u v else 0) = vaughanThird n u v
    have hnon : 0 ≤ (n : ℤ) := (Finset.mem_Icc.mp hn).1
    have hto : (n.toNat : ZMod q) = (n : ZMod q) := by
      rw [← Int.cast_natCast (R := ZMod q) n.toNat]
      exact congrArg (fun z : ℤ => (z : ZMod q)) (Int.toNat_of_nonneg hnon)
    simp [hnon, hto]

/-- The norm-square of the interval coefficients equals the range sum of
  vaughanThird(n,u,v)^2. -/
lemma vaughanThird_Icc_normSq (m u v : ℕ) :
    (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
      ‖(if 0 ≤ n then (vaughanThird n.toNat u v : ℂ) else 0)‖ ^ 2) =
      ∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2 := by
  refine Finset.sum_bij (s := Finset.Icc (0 : ℤ) (m : ℤ)) (t := Finset.range (m + 1))
    (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    have hz : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.1
    have hto : n.toNat ≤ m := by
      exact_mod_cast (by simpa [hz] using hn.2)
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    have h₁ : 0 ≤ n₁ := (Finset.mem_Icc.mp hn₁).1
    have h₂ : 0 ≤ n₂ := (Finset.mem_Icc.mp hn₂).1
    calc
      n₁ = (n₁.toNat : ℤ) := (Int.toNat_of_nonneg h₁).symm
      _ = (n₂.toNat : ℤ) := by rw [h]
      _ = n₂ := Int.toNat_of_nonneg h₂
  · intro n hn
    rw [Finset.mem_range] at hn
    refine ⟨(n : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨by exact_mod_cast (Nat.zero_le n), by exact_mod_cast (Nat.le_of_lt_succ hn)⟩
    · exact Int.toNat_natCast n
  · intro n hn
    have hnon : 0 ≤ (n : ℤ) := (Finset.mem_Icc.mp hn).1
    -- ‖(vaughanThird n u v : ℂ)‖² = (vaughanThird n u v)²
    have hnorm : ‖(vaughanThird n.toNat u v : ℂ)‖ ^ 2 = (vaughanThird n.toNat u v) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa [pow_two] using Complex.normSq_ofReal (vaughanThird n.toNat u v)
    simp [hnon, hnorm]

/-- **Bombieri-Davenport for the type-II coefficients**: the primitive-character
  (q/phi(q))-weighted mean bound for vaughanThird(n,u,v), i.e. the corrected
  analytic input for the type-II mean value (mirror of
  bombieriDavenport_vaughanFirst). -/
theorem bombieriDavenport_vaughanThird (Q m u v : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖panTypeIIV3CharSum q m u v χ‖ ^ 2))
      ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
  let a : ℤ → ℂ := fun n => if 0 ≤ n then (vaughanThird n.toNat u v : ℂ) else 0
  have hbd := bombieriDavenport_le Q hQ a (-1) (m + 1)
  -- rewrite the character sums: Σ_{Icc 0 (m:ℤ)} a n·chi(n) = panTypeIIV3CharSum q m u chi
  have hL : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)‖ ^ 2 = ‖panTypeIIV3CharSum q m u v χ‖ ^ 2 := by
    intro q hq χ hχ
    congr 1
    unfold panTypeIIV3CharSum
    rw [← vaughanThird_Icc_charSum χ]
  -- rewrite the norm-square: Σ_{Icc}‖a n‖² = Σ_{range}(vaughanThird n u v)²
  have hR : (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2 := by
    simpa [a] using vaughanThird_Icc_normSq m u v
  -- now convert hbd
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖panTypeIIV3CharSum q m u v χ‖ ^ 2))
        ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) *
            (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) := by
          -- rewrite the character sums in hbd's LHS
          rw [show (∑ q ∈ Finset.Icc 1 Q,
              ((q : ℝ) / (q.totient : ℝ)) *
              (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                ‖panTypeIIV3CharSum q m u v χ‖ ^ 2)) =
              (∑ q ∈ Finset.Icc 1 Q,
                ((q : ℝ) / (q.totient : ℝ)) *
                (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
                  ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)‖ ^ 2)) by
            apply Finset.sum_congr rfl
            intro q hq
            congr 1
            apply Finset.sum_congr rfl
            intro χ hχ
            exact (hL q hq χ hχ).symm]
          have hn1 : (-1 + 1 : ℤ) = 0 := by norm_num
          have hn2 : (-1 + ((m : ℤ) + 1) : ℤ) = (m : ℤ) := by omega
          simpa [hn1, hn2] using hbd
    _ ≤ largeSieveBound (m + 1) (1 / (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
          rw [hR]

/-
## Scope of the all-character square-mean target

The literal target (PanMeanValueBody.lean, def panTypeICharSquareMeanBound)
  sum_{q <= Q} mu^2(q) 3^omega(q) * sum_{chi mod q} ||V_chi(m)||^2
      <= C * (m + Q^2) * sum_{n <= m} vaughanFirst(n,u)^2
is FALSE as stated: for u = 1 (vaughanFirst(n,1) = log n) and m = Q^2 the smooth
part of the character sums (each A_a(m) ~ (m/q) log m) gives
  LHS ~ m^2 (log m)^2 * sum_{q <= Q} mu^2(q) 3^omega(q) phi(q)^2 / q^2
with the inner sum already >= sum_{p <= Q} 3 (p-1)^2 / p^2 ~ 3 Q / log Q
(growing without bound), while RHS = C (m + Q^2) S(m) with S(m) ~ m (log m)^2.
See check_target.py for the numerics (LHS/RHS grows ~ Q/log Q as Q -> oo).

The primitive-character analytic input proved in this module is the
Bombieri-Davenport lemma over PRIMITIVE characters with the (q/phi(q)) weight:
  bombieriDavenport_le / bombieriDavenport_vaughanFirst.
The remaining assembly to a usable panTypeI input (all characters, conductor
decomposition with the (n, q) > 1 splitting, and the mu^2 3^omega weight
estimates) requires the distinctions below. These do not turn the false
literal square-mean target into a theorem.

Sub-steps to the corrected type-I mean value:
  (S1) Primitive-character BD lemma: bombieriDavenport_vaughanFirst.
  (S2) conductor decomposition: sum_{chi mod q} ||V_chi||^2 expressed via
       primitive characters of conductors q' | q, with the non-coprime part
       controlled by density estimates (classical, needs the charSqSum
       orthogonality identity). The conductor-cast and non-coprime
       estimates are separate from the primitive-character theorem.
  (S3) Weight estimates must accompany the conductor decomposition.
       The coefficient bound S(m) <= C m log^5 m and an elementary
       sum_{q <= Q} mu^2(q) 3^omega(q) << Q log^2 Q are relevant.
       In contrast, the proposed bound
       sum_{q <= Q} mu^2(q) 3^omega(q) phi(q)^2 / q^2 << (log Q)^3
       is false: primes alone contribute order Q/log Q, as above.
       A corrected mean-value route must retain the appropriate
       conductor weights and cannot use that proposed estimate.
  (S4) the (m + Q^2) shape with a constant requires the sharp additive
       large-sieve constant N + delta^{-1} (the repo's largeSieveBound has
       N + O(Q^2 log Q); the sharp estimate is not supplied here).
-/

/-! ## 8. The per-q assembly analysis: regrouping by reduced fractions -/

/-- gcd multiplication: gcd(a*c, b*c) = c * gcd(a, b). -/
lemma gcd_mul_right' (a b c : ℕ) : (a * c).gcd (b * c) = c * (a.gcd b) := by
  rw [Nat.gcd_mul_right a c b, mul_comm]

/-- Dividing by the gcd gives a coprime pair. -/
lemma coprime_div_gcd {q r : ℕ} (hq : 0 < q) : (q / q.gcd r).Coprime (r / q.gcd r) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hdiv : q.gcd r ∣ q := Nat.gcd_dvd_left q r
  have hdiv2 : q.gcd r ∣ r := Nat.gcd_dvd_right q r
  -- gcd(q, r) = gcd((q/g)·g, (r/g)·g) = g·gcd(q/g, r/g) = g
  have hcalc : (q.gcd r) * (q / q.gcd r).gcd (r / q.gcd r) = q.gcd r := by
    rw [← gcd_mul_right' (q / q.gcd r) (r / q.gcd r) (q.gcd r)]
    rw [Nat.div_mul_cancel hdiv, Nat.div_mul_cancel hdiv2]
  -- g·gcd(q/g, r/g) = g ⟹ gcd(q/g, r/g) = 1
  have hmain : ((q / q.gcd r).gcd (r / q.gcd r)) * (q.gcd r) = (q.gcd r) := by
    simpa [mul_comm] using hcalc
  exact (mul_right_cancel₀ (Nat.ne_of_gt hg) (by simpa [one_mul] using hmain))

/-- **Per-modulus regrouping (the exact content of assembly for each q)**: for weights w(q),
    sum_{q <= Q} w(q) * sum_{r < q} f(r/q) = sum_{q' <= Q} W(q') * sum_{red r'} f(r'/q')
  with W(q') = sum_{d <= Q/q'} w(q'*d); the reduced fractions r'/q' (coprime) carry
  the regrouped weight. For w(q) = mu^2 3^omega phi(q)/q, W(1) ~ (log Q)^3 is
  unbounded — the per-q stacking cannot produce the (m + Q^2) shape. -/
lemma perModulus_regroup {Q : ℕ} (w : ℕ → ℝ) (f : ℝ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q,
        (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
        ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ)) := by
  -- both sides are the triple sum over (q', r', d) of w(q'*d) * f(r'/q'), grouped differently
  have hLeft : (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
        ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
    -- bijection between (q, r) and (q', r', d)
    have hbij : (∑ p ∈ (Finset.Icc 1 Q).sigma (fun q => Finset.range q),
          w p.1 * f ((p.2 : ℝ) / (p.1 : ℝ))) =
        (∑ p ∈ (Finset.Icc 1 Q).sigma (fun q' =>
            ((Finset.range q').filter (fun r' => r'.Coprime q')).product (Finset.Icc 1 (Q / q'))),
          w (p.1 * p.2.2) * f ((p.2.1 : ℝ) / (p.1 : ℝ))) := by
      refine Finset.sum_bij (s := (Finset.Icc 1 Q).sigma (fun q => Finset.range q))
        (t := (Finset.Icc 1 Q).sigma (fun q' =>
          ((Finset.range q').filter (fun r' => r'.Coprime q')).product (Finset.Icc 1 (Q / q'))))
        (fun p _ => (⟨p.1 / p.1.gcd p.2, (p.2 / p.1.gcd p.2, p.1.gcd p.2)⟩ : Σ q' : ℕ, ℕ × ℕ)) ?_ ?_ ?_ ?_
      · -- i p ∈ t
        intro p hp
        rw [Finset.mem_sigma] at hp
        rcases hp with ⟨hq, hr⟩
        rw [Finset.mem_sigma]
        -- q' = p.1 / g >= 1, <= Q; r' = p.2 / g < q'; d = g in Icc 1 (Q / q'); coprime
        let g := p.1.gcd p.2
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_left p.2 (Finset.mem_Icc.mp hq).1
        have hgdiv1 : g ∣ p.1 := Nat.gcd_dvd_left p.1 p.2
        have hgdiv2 : g ∣ p.2 := Nat.gcd_dvd_right p.1 p.2
        have hqpos : 0 < p.1 := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (Finset.mem_Icc.mp hq).1
        have hq' : p.1 / g ∈ Finset.Icc 1 Q := by
          rw [Finset.mem_Icc]
          constructor
          · exact Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hqpos hgdiv1) hgpos)
          · exact le_trans (Nat.div_le_self p.1 g) (Finset.mem_Icc.mp hq).2
        have hd : g ∈ Finset.Icc 1 (Q / (p.1 / g)) := by
          rw [Finset.mem_Icc]
          constructor
          · exact hgpos
          · -- g <= Q / (p.1/g) ⟺ g·(p.1/g) <= Q ⟺ p.1 <= Q ✓
            have hgm : g * (p.1 / g) = p.1 := Nat.mul_div_cancel' hgdiv1
            rw [Nat.le_div_iff_mul_le (Nat.div_pos (Nat.le_of_dvd hqpos hgdiv1) hgpos)]
            rw [hgm]
            exact (Finset.mem_Icc.mp hq).2
        have hr' : p.2 / g ∈ (Finset.range (p.1 / g)).filter (fun r' => r'.Coprime (p.1 / g)) := by
          rw [Finset.mem_filter, Finset.mem_range]
          constructor
          · -- p.2 / g < p.1 / g ⟸ p.2 < p.1
            exact Nat.div_lt_div_of_lt_of_dvd hgdiv1 (Finset.mem_range.mp hr)
          · exact (coprime_div_gcd (Finset.mem_Icc.mp hq).1).symm
        exact ⟨hq', Finset.mem_product.mpr ⟨hr', hd⟩⟩
      · -- i_inj: reduced fractions unique
        intro p₁ hp₁ p₂ hp₂ h
        rw [Finset.mem_sigma] at hp₁ hp₂
        have hfst : p₁.1 / p₁.1.gcd p₁.2 = p₂.1 / p₂.1.gcd p₂.2 := congrArg Sigma.fst h
        have hsnd : (p₁.2 / p₁.1.gcd p₁.2, p₁.1.gcd p₁.2) = (p₂.2 / p₂.1.gcd p₂.2, p₂.1.gcd p₂.2) := congrArg Sigma.snd h
        have hg : p₁.1.gcd p₁.2 = p₂.1.gcd p₂.2 := congrArg Prod.snd hsnd
        have hr : p₁.2 / p₁.1.gcd p₁.2 = p₂.2 / p₂.1.gcd p₂.2 := congrArg Prod.fst hsnd
        have h1 : p₁.1 = p₂.1 := by
          calc
            p₁.1 = (p₁.1 / p₁.1.gcd p₁.2) * p₁.1.gcd p₁.2 := (Nat.div_mul_cancel (Nat.gcd_dvd_left p₁.1 p₁.2)).symm
            _ = (p₂.1 / p₂.1.gcd p₂.2) * p₂.1.gcd p₂.2 := by rw [hfst, hg]
            _ = p₂.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left p₂.1 p₂.2)
        have h2 : p₁.2 = p₂.2 := by
          calc
            p₁.2 = (p₁.2 / p₁.1.gcd p₁.2) * p₁.1.gcd p₁.2 := (Nat.div_mul_cancel (Nat.gcd_dvd_right p₁.1 p₁.2)).symm
            _ = (p₂.2 / p₂.1.gcd p₂.2) * p₂.1.gcd p₂.2 := by rw [hr, hg]
            _ = p₂.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right p₂.1 p₂.2)
        apply Sigma.ext h1
        simpa [h1] using h2
      · -- i_surj
        intro p hp
        rw [Finset.mem_sigma] at hp
        rcases hp with ⟨hq', hp2⟩
        rcases (Finset.mem_product.mp hp2) with ⟨hr', hd⟩
        rw [Finset.mem_filter] at hr'
        -- preimage: (p.1 * p.2.2, p.2.1 * p.2.2)
        refine ⟨⟨p.1 * p.2.2, p.2.1 * p.2.2⟩, ?_, ?_⟩
        · rw [Finset.mem_sigma]
          constructor
          · rw [Finset.mem_Icc]
            constructor
            · exact Nat.succ_le_of_lt (Nat.mul_pos (Finset.mem_Icc.mp hq').1 (Finset.mem_Icc.mp hd).1)
            · -- p.1·p.2.2 <= Q: from d <= Q / q'
              have hle := (Finset.mem_Icc.mp hd).2
              rw [Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hq').1] at hle
              simpa [mul_comm, mul_left_comm, mul_assoc] using hle
          · rw [Finset.mem_range]
            -- p.2.1·p.2.2 < p.1·p.2.2 ⟸ p.2.1 < p.1
            exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hr'.1) (Finset.mem_Icc.mp hd).1
        · -- i (q'·d, r'·d) = ⟨q', (r', d)⟩ — since gcd(q'd, r'd) = d (coprime)
          have hcop : p.2.1.Coprime p.1 := hr'.2
          have hgcd : (p.1 * p.2.2).gcd (p.2.1 * p.2.2) = p.2.2 := by
            rw [gcd_mul_right' p.1 p.2.1 p.2.2]
            have hg : p.1.gcd p.2.1 = 1 := hcop.symm.gcd_eq_one
            simp [hg]
          have hfst : (p.1 * p.2.2) / (p.1 * p.2.2).gcd (p.2.1 * p.2.2) = p.1 := by
            rw [hgcd]
            simpa [mul_comm] using Nat.mul_div_cancel_left p.1 (Finset.mem_Icc.mp hd).1
          have hsnd1 : (p.2.1 * p.2.2) / (p.1 * p.2.2).gcd (p.2.1 * p.2.2) = p.2.1 := by
            rw [hgcd]
            simpa [mul_comm] using Nat.mul_div_cancel_left p.2.1 (Finset.mem_Icc.mp hd).1
          apply Sigma.ext hfst
          apply heq_of_eq
          apply Prod.ext
          · exact hsnd1
          · exact hgcd
      · -- h: f p = g (i p)
        intro p hp
        -- w p.1 * f (p.2/p.1) = w ((p.1/g)*g) * f ((p.2/g)/(p.1/g))
        have hg : p.1 = (p.1 / p.1.gcd p.2) * p.1.gcd p.2 := by
          exact (Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)).symm
        have hg2 : p.2 = (p.2 / p.1.gcd p.2) * p.1.gcd p.2 := by
          exact (Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)).symm
        have hw : w p.1 = w ((p.1 / p.1.gcd p.2) * p.1.gcd p.2) := by rw [← hg]
        have hfrac : (p.2 : ℝ) / (p.1 : ℝ) =
            ((p.2 / p.1.gcd p.2 : ℕ) : ℝ) / ((p.1 / p.1.gcd p.2 : ℕ) : ℝ) := by
          have hqpos : 0 < p.1 := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
            (Finset.mem_Icc.mp (Finset.mem_sigma.mp hp).1).1
          have hg0 : (p.1.gcd p.2 : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.gcd_pos_of_pos_left p.2 hqpos))
          have hb0 : ((p.1 / p.1.gcd p.2 : ℕ) : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hqpos (Nat.gcd_dvd_left p.1 p.2))
              (Nat.gcd_pos_of_pos_left p.2 hqpos)))
          have hgR : (p.1 : ℝ) = ((p.1 / p.1.gcd p.2 : ℕ) : ℝ) * (p.1.gcd p.2 : ℝ) := by
            exact_mod_cast hg
          have hg2R : (p.2 : ℝ) = ((p.2 / p.1.gcd p.2 : ℕ) : ℝ) * (p.1.gcd p.2 : ℝ) := by
            exact_mod_cast hg2
          calc
            (p.2 : ℝ) / (p.1 : ℝ)
                = (((p.2 / p.1.gcd p.2 : ℕ) : ℝ) * (p.1.gcd p.2 : ℝ)) /
                    (((p.1 / p.1.gcd p.2 : ℕ) : ℝ) * (p.1.gcd p.2 : ℝ)) := by
                  rw [← hg2R, ← hgR]
            _ = ((p.2 / p.1.gcd p.2 : ℕ) : ℝ) / ((p.1 / p.1.gcd p.2 : ℕ) : ℝ) := by
                  field_simp [hg0, hb0]
        rw [hw]
        congr 1
        exact congrArg f hfrac
    -- the LHS double sum = the sigma sum over s
    calc
      (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ)))
          = ∑ q ∈ Finset.Icc 1 Q, ∑ r ∈ Finset.range q, w q * f ((r : ℝ) / (q : ℝ)) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [Finset.mul_sum]
      _ = ∑ p ∈ (Finset.Icc 1 Q).sigma (fun q => Finset.range q),
            w p.1 * f ((p.2 : ℝ) / (p.1 : ℝ)) := by
            rw [Finset.sum_sigma' (s := Finset.Icc 1 Q) (t := fun q => Finset.range q)
              (f := fun q r => w q * f ((r : ℝ) / (q : ℝ)))]
      _ = (∑ p ∈ (Finset.Icc 1 Q).sigma (fun q' =>
            ((Finset.range q').filter (fun r' => r'.Coprime q')).product (Finset.Icc 1 (Q / q'))),
            w (p.1 * p.2.2) * f ((p.2.1 : ℝ) / (p.1 : ℝ))) := hbij
      _ = ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
            ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
            rw [Finset.sum_sigma (s := Finset.Icc 1 Q)
              (t := fun q' => ((Finset.range q').filter (fun r' => r'.Coprime q')).product (Finset.Icc 1 (Q / q')))
              (f := fun p : Σ q' : ℕ, ℕ × ℕ => w (p.1 * p.2.2) * f ((p.2.1 : ℝ) / (p.1 : ℝ)))]
            apply Finset.sum_congr rfl
            intro q' hq'
            rw [← Finset.sum_product
              (s := (Finset.range q').filter (fun r' => r'.Coprime q'))
              (t := Finset.Icc 1 (Q / q'))
              (f := fun z : ℕ × ℕ => w (q' * z.2) * f ((z.1 : ℝ) / (q' : ℝ)))]
            rw [Finset.product_eq_sprod]
  -- RHS factorization
  have hRight : (∑ q' ∈ Finset.Icc 1 Q,
        (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
        ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ))) =
      ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
        ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q' hq'
    -- (Σ_d w)·(Σ_r' f) = Σ_{r',d} w·f — expand (with the ℝ sum cast to ℂ)
    have hcast : (algebraMap ℝ ℂ) (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) =
        ∑ d ∈ Finset.Icc 1 (Q / q'), (w (q' * d) : ℂ) := by
      exact map_sum (algebraMap ℝ ℂ) (fun d => w (q' * d)) (Finset.Icc 1 (Q / q'))
    calc
      (algebraMap ℝ ℂ) (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
          ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ))
          = (∑ d ∈ Finset.Icc 1 (Q / q'), (w (q' * d) : ℂ)) *
              ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ)) := by
            rw [hcast]
      _ = ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
            ∑ d ∈ Finset.Icc 1 (Q / q'), (w (q' * d) : ℂ) * f ((r' : ℝ) / (q' : ℝ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r' hr'
            rw [Finset.sum_mul]
      _ = ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
            ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := by
            rfl
  calc
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ r ∈ Finset.range q, f ((r : ℝ) / (q : ℝ)))
        = ∑ q' ∈ Finset.Icc 1 Q, ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'),
            ∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d) * f ((r' : ℝ) / (q' : ℝ)) := hLeft
    _ = ∑ q' ∈ Finset.Icc 1 Q,
          (∑ d ∈ Finset.Icc 1 (Q / q'), w (q' * d)) *
          ∑ r' ∈ (Finset.range q').filter (fun r' => r'.Coprime q'), f ((r' : ℝ) / (q' : ℝ)) := hRight.symm

/-! ## 9. Per-modulus bounds versus the Type I mean-value target

**Setup.** The actual consumer of the mean-value input is
`panTypeICharMeanSieveBound` in `PanMeanValueBody`, via
`PanTypeICharacterMeanValue.of_sieveBound`. Its L^2 intermediate
`panTypeICharSquareMeanBound` asks for
  sum_{q<=Q} mu^2 3^omega * sum_{chi mod q} ||V_chi(m)||^2 <= C (m + Q^2) S(m).
The per-modulus material already proved is `characterSieveModulus_le`
  sum_chi ||S_chi||^2 <= (phi(q)/q) * sum_{r<q} |T(r/q)|^2   (one q at a time)
together with the additive sieve `largeSieveBound(m+1, 1/q^2) = m + O(q^2 log q)`.

**(a) Can the q-summation be done from the per-q material + polylog? NO.**
The per-q bound gives the q-sum with weight mu^2 3^omega (phi(q)/q) times (m + q^2 log q).
The regrouping lemma `perModulus_regroup` shows this is exactly
  sum_{q'<=Q} W(q') * sum_{red r'} |T(r'/q')|^2,  W(q') = sum_{d<=Q/q'} mu^2 3^omega phi(q'd)/(q'd),
and the effective weight W(1) = sum_{d<=Q} mu^2 3^omega phi(d)/d is unbounded;
primes alone contribute order Q/log Q, so this is not merely log-cubed growth
(numerics in check_perq.py: W(1) = 94, 211, 473, 1098 at Q = 40, 80, 160, 320). Equivalently,
  sum_{q<=Q} mu^2 3^omega (phi/q) (m + q^2 log q) ~ m Q (log Q)^2 + Q^3 (log Q)^3,
which is ~ Q (log Q)^3 times bigger than (m + Q^2) at m = Q^2 (ratio 704, 1664, 3844, 9777).
So the per-q stacking cannot produce the (m + Q^2) shape; moreover
`panTypeICharSquareMeanBound` itself is false (u = 1, m = Q^2; see section 7).

**(b) The real Bombieri-Davenport (all q simultaneously) is needed — and proved.**
`characterSieveModulus_le` is per-modulus (fixed q). The all-q version must
apply the additive sieve to the WHOLE Farey set X_Q = {r/q : 1 <= q <= Q, 0 <= r < q, gcd(r,q)=1}
(which is 1/Q^2-well-spaced) with `largeSieveRationalPoints` — that is exactly
`bombieriDavenport_le` / `bombieriDavenport_vaughanFirst`
(sum over primitive chi with the (q/phi(q)) weight; the Gauss-sum inversion converts the
weighted primitive sum to the UNWEIGHTED reduced-fraction sum, and the additive sieve is
applied once, on X_Q). This gives the m + Q^2 shape (up to the weak sieve constant).

**(c) The direct-Parseval-stacking counterexample is avoided.**
The per-modulus counterexample discussed in `PanMeanValueBody` shows that stacking the per-q Parseval
over ALL characters (or with multiplicities on the rational points) fails. The BD proof
never does that: it (i) restricts to primitive characters, (ii) uses the Gauss-sum
inversion |S_chi|^2 = (1/q) |sum_a star(chi a) T(a/q)|^2, (iii) applies the unit-group
Parseval to get the sum over REDUCED fractions with weight 1, and (iv) applies the
additive sieve once on the Farey set. No per-q Parseval stacking occurs.

**Additional requirements for a mean-value assembly.** The proved BD lemma carries the (q/phi(q)) weight over
primitive characters; the target carries mu^2 3^omega over all characters. Bridging the
two needs the conductor decomposition (each chi mod q lifts a unique primitive chi' mod
q' | q) with the non-coprime part controlled by density estimates, and then the
mu^2 3^omega weight assembly (sub-steps S2-S3 of section 7). The sharp (m + Q^2)
constant additionally needs the N + delta^{-1} additive-sieve constant (sub-step S4).
-/
