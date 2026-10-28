import AnalyticNumberTheory.Sieve.PanMeanValueBody
import Mathlib.NumberTheory.DirichletCharacter.GaussSum

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

set_option maxHeartbeats 4000000

/-! ## 1. The standard additive character e_q and Gauss sum bridge -/


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


/-- The sum over ZMod q equals the sum over representatives r < q. -/
lemma zmodSum_eq_rangeSum {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    (∑ a : ZMod q, f a) = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  exact zmod_sum_range f

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
  have : Fintype (ZMod q)ˣ := Fintype.ofFinite _
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

/-- The norm of a Dirichlet character is at most one, for every modulus. -/
lemma dirichletChar_norm_le_one (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ZMod q) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · rw [dirichletChar_norm_unit χ ha]
  · have hz : χ a = 0 := MulChar.map_nonunit χ ha
    rw [hz]
    norm_num

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
      simp [hcard]


/-! ## 4. Gauss-sum Fourier inversion for primitive characters -/


/-! ## 5. Unit Parseval and the Bombieri-Davenport stacking -/

/-- Orthogonality with star: sum_chi star(chi a) * chi b = phi(q) * [a = b and a unit]. -/
lemma charOrthSum_star {q : ℕ} [NeZero q] (a b : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, star (χ a) * χ b) =
      if IsUnit a ∧ IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
  -- Conjugate orthogonality once: star distributes over the sum and
  -- star (chi a * star (chi b)) = star (chi a) * chi b over ℂ.
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
    _ = if IsUnit a ∧ IsUnit b ∧ a = b then (q.totient : ℂ) else 0 := by
          rw [charOrthSum (Nat.pos_of_ne_zero (NeZero.ne q)) a b]
          -- Both possible values, phi(q) and zero, are fixed by star.
          split_ifs <;> simp

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
            simp
      _ = (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0)) := hC
      _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
            have hmid : (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) =
                (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := by
              simp
            calc
              (q.totient : ℂ) * (∑ x : ZMod q, (if IsUnit x then (‖T x‖ ^ 2 : ℂ) else 0))
                  = (q.totient : ℂ) * (∑ x : ZMod q, (((if IsUnit x then ‖T x‖ ^ 2 else 0 : ℝ) : ℂ))) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro x hx
                    by_cases h : IsUnit x <;> simp [h]
              _ = (algebraMap ℝ ℂ) ((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then ‖T x‖ ^ 2 else 0)) := hmid)


/-! ## 6. The Bombieri-Davenport lemma -/


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


/-! ## 7. Application to Type I coefficients and limitations -/


/-! ## 7b. Application to the type-II assembly (panTypeIIV3CharSum)

The mirror of section 7 for the type-II coefficients: Bombieri-Davenport for
`vaughanThird(n,u,v)` with the (q/phi(q)) primitive-character weight,
`bombieriDavenport_vaughanThird`, the corrected analytic input for the type-II
mean value. -/


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
