import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonvanishing of the Stepanov auxiliary polynomial

The argument is the first half of printed page 11 of Gergely Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`).

The nonsquare hypothesis is geometric: it concerns the polynomial after
base change to the algebraic closure, not just squares over the finite field.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F]

/-- A square times a polynomial cannot be a square unless that polynomial
is a square. Unique factorization supplies the required polynomial quotient. -/
private theorem stepanov_isSquare_of_sq_mul_eq_sq
    {K : Type*} [Field K] (f r t : K[X]) (hr : r ≠ 0)
    (h : r ^ 2 * f = t ^ 2) : IsSquare f := by
  have hdiv : r ^ 2 ∣ t ^ 2 := ⟨f, h.symm⟩
  obtain ⟨u, hu⟩ :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
  refine ⟨u, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hr)
  rw [h, hu]
  ring

/-- The geometric nonsquare obstruction used after reducing modulo `X^q`. -/
theorem stepanov_sq_mul_eq_const_mul_sq
    (f r s : F[X]) (c : F) (hc : c ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (h : r ^ 2 * f = s ^ 2 * C c) : r = 0 ∧ s = 0 := by
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨a, ha⟩ :=
      IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) c)
        (by decide : 0 < 2)
    apply hf
    apply stepanov_isSquare_of_sq_mul_eq_sq
      (f.map (algebraMap F (AlgebraicClosure F)))
      (r.map (algebraMap F (AlgebraicClosure F)))
      (s.map (algebraMap F (AlgebraicClosure F)) * C a)
      (by simpa using hr)
    have hm := congrArg (Polynomial.map (algebraMap F (AlgebraicClosure F))) h
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      mul_pow, ← C_pow, ha] using hm
  refine ⟨hr, ?_⟩
  rw [hr, zero_pow (by decide : 2 ≠ 0), zero_mul] at h
  have hs : s ^ 2 = 0 := (mul_eq_zero.mp h.symm).resolve_right (by simpa using hc)
  by_contra hs0
  exact pow_ne_zero 2 hs0 hs

variable [Fintype F]

/-- Frobenius makes the constant term the entire residue of `f^q` modulo `X^q`. -/
theorem stepanov_X_card_dvd_pow_sub_const (f : F[X]) :
    X ^ Fintype.card F ∣ f ^ Fintype.card F - C (f.eval 0) := by
  obtain ⟨p, hp, n, hprime, hcard⟩ := FiniteField.card' F
  let : CharP F p := hp
  let : Fact p.Prime := ⟨hprime⟩
  have hd : (X : F[X]) ∣ f - C (f.eval 0) := by
    rw [X_dvd_iff]
    simp [coeff_zero_eq_eval_zero]
  have hpow := pow_dvd_pow_of_dvd hd (Fintype.card F)
  have he : (f - C (f.eval 0)) ^ Fintype.card F =
      f ^ Fintype.card F - C (f.eval 0) := by
    rw [hcard, sub_pow_char_pow, ← C_pow, ← hcard, FiniteField.pow_card]
  rwa [he] at hpow

omit [Fintype F] in
private theorem stepanov_natDegree_le_pred {r : F[X]} {B : ℕ}
    (hr : r.degree < (B : WithBot ℕ)) : r.natDegree ≤ B - 1 := by
  by_cases hzero : r = 0
  · simp [hzero]
  rw [degree_eq_natDegree hzero] at hr
  have hr' : r.natDegree < B := by exact_mod_cast hr
  omega

/-- Harcos's residue kernel lemma: a degree-bounded block cannot be divisible
by `X^q`. The degree convention includes zero polynomials even when `B = 0`. -/
theorem stepanov_block_eq_zero_of_X_card_dvd
    (f r s : F[X]) (B : ℕ)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : r.degree < (B : WithBot ℕ)) (hs : s.degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hdiv : X ^ Fintype.card F ∣ r + s * f ^ ((Fintype.card F - 1) / 2)) :
    r = 0 ∧ s = 0 := by
  have he : 2 * ((Fintype.card F - 1) / 2) + 1 = Fintype.card F := by
    obtain ⟨k, hk⟩ := hq
    omega
  have hp : (f ^ ((Fintype.card F - 1) / 2)) ^ 2 * f =
      f ^ Fintype.card F := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  have hd₁ : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * f ^ Fintype.card F := by
    have hd := dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left hdiv (r - s * f ^ ((Fintype.card F - 1) / 2))) f
    convert hd using 1
    rw [← hp]
    ring
  have hd₂ := dvd_mul_of_dvd_right (stepanov_X_card_dvd_pow_sub_const f) (s ^ 2)
  have hd : X ^ Fintype.card F ∣ r ^ 2 * f - s ^ 2 * C (f.eval 0) := by
    convert dvd_add hd₁ hd₂ using 1
    ring
  have hrB := stepanov_natDegree_le_pred hr
  have hsB := stepanov_natDegree_le_pred hs
  have hdr : (r ^ 2 * f).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (r ^ 2).natDegree + f.natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow]; omega
  have hds : (s ^ 2 * C (f.eval 0)).natDegree ≤ 2 * (B - 1) + f.natDegree := by
    calc
      _ ≤ (s ^ 2).natDegree + (C (f.eval 0)).natDegree := natDegree_mul_le
      _ ≤ _ := by rw [natDegree_pow, natDegree_C]; omega
  have hz : r ^ 2 * f - s ^ 2 * C (f.eval 0) = 0 := by
    apply eq_zero_of_dvd_of_natDegree_lt hd
    rw [natDegree_X_pow]
    exact lt_of_le_of_lt
      ((natDegree_sub_le _ _).trans (max_le hdr hds)) hB
  exact stepanov_sq_mul_eq_const_mul_sq f r s (f.eval 0) hf0 hf (sub_eq_zero.mp hz)

/-- The actual Stepanov block ansatz, before multiplication by `f^ell`. -/
def stepanovAnsatz (f : F[X]) {J : ℕ} (r s : Fin J → F[X]) : F[X] :=
  ∑ j : Fin J,
    (r j + s j * f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F)

private theorem stepanovAnsatz_succ (f : F[X]) {J : ℕ}
    (r s : Fin (J + 1) → F[X]) :
    stepanovAnsatz f r s =
      r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) +
        stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
          X ^ Fintype.card F := by
  simp [stepanovAnsatz, Fin.sum_univ_succ, Nat.add_mul, pow_add, Finset.sum_mul,
    mul_assoc]

/-- All coefficients vanish if the actual Stepanov ansatz vanishes.
Successively removing the first block is equivalent to Harcos's choice
of the least nonzero block. -/
theorem stepanovAnsatz_coefficients_eq_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hz : stepanovAnsatz f r s = 0) : ∀ j, r j = 0 ∧ s j = 0 := by
  induction J with
  | zero => intro j; exact Fin.elim0 j
  | succ J ih =>
      rw [stepanovAnsatz_succ] at hz
      have hdiv : X ^ Fintype.card F ∣
          r 0 + s 0 * f ^ ((Fintype.card F - 1) / 2) := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact dvd_neg.mpr (dvd_mul_left _ _)
      have hzero := stepanov_block_eq_zero_of_X_card_dvd
        f (r 0) (s 0) B hq hf0 hf (hr 0) (hs 0) hB hdiv
      have htail :
          stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) = 0 := by
        have ht :
            stepanovAnsatz f (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ) *
              X ^ Fintype.card F = 0 := by
          simpa only [hzero.1, hzero.2, zero_mul, zero_add] using hz
        exact (mul_eq_zero.mp ht).resolve_right (pow_ne_zero _ X_ne_zero)
      have ht := ih (fun j : Fin J => r j.succ) (fun j : Fin J => s j.succ)
        (fun j => hr j.succ) (fun j => hs j.succ) htail
      intro j
      exact Fin.cases hzero (fun i => ht i) j

/-- Injectivity of the actual ansatz on degree-bounded coefficient families. -/
theorem stepanovAnsatz_eq_iff
    (f : F[X]) {J B : ℕ} (r s r' s' : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hr' : ∀ j, (r' j).degree < (B : WithBot ℕ))
    (hs' : ∀ j, (s' j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F) :
    stepanovAnsatz f r s = stepanovAnsatz f r' s' ↔ r = r' ∧ s = s' := by
  constructor
  · intro heq
    have hsub :
        stepanovAnsatz f (fun j => r j - r' j) (fun j => s j - s' j) = 0 := by
      rw [← sub_eq_zero] at heq
      convert heq using 1
      simp only [stepanovAnsatz, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hz := stepanovAnsatz_coefficients_eq_zero f
      (fun j => r j - r' j) (fun j => s j - s' j) hq hf0 hf
      (fun j => lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hr j) (hr' j)))
      (fun j => lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hs j) (hs' j))) hB hsub
    exact ⟨funext (fun j => sub_eq_zero.mp (hz j).1),
      funext (fun j => sub_eq_zero.mp (hz j).2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Harcos page 11: a nontrivial bounded coefficient family gives a nonzero
auxiliary polynomial, under the geometric nonsquare hypothesis. -/
theorem stepanovAnsatz_ne_zero
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) : stepanovAnsatz f r s ≠ 0 := by
  intro hz
  have hall := stepanovAnsatz_coefficients_eq_zero f r s hq hf0 hf hr hs hB hz
  obtain ⟨j, hj⟩ := hne
  exact hj.elim (fun h => h (hall j).1) (fun h => h (hall j).2)

/-- The same nonvanishing conclusion after the multiplier in Harcos's ansatz. -/
theorem stepanov_pow_mul_ansatz_ne_zero
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ))
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hne : ∃ j, r j ≠ 0 ∨ s j ≠ 0) :
    f ^ ell * stepanovAnsatz f r s ≠ 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  exact mul_ne_zero (pow_ne_zero ell hfne)
    (stepanovAnsatz_ne_zero f r s hq hf0 hf hr hs hB hne)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
