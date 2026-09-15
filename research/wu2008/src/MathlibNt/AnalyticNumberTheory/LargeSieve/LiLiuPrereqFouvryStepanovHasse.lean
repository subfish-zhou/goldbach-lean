import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hasse differentiation in Stepanov's construction

The divisibility, linear operator, and degree estimates below formalize
Lemma 10 of Gergely Harcos, *Weil's bound for
Kloosterman sums*, printed page 10 (`harcos-weil.pdf`).

The operator is polynomial division of `hasseDeriv k (g * f ^ n)` by
`f ^ (n - k)`. Its factorization is proved, not assumed. No monicity or
characteristic restriction is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

/-- The power forced by Leibniz's rule divides the Hasse derivative.
The truncated exponent also makes the statement valid when `n < k`. -/
theorem stepanov_pow_dvd_hasseDeriv_mul_pow
    {R : Type*} [CommRing R] (f g : R[X]) (n k : ℕ) :
    f ^ (n - k) ∣ hasseDeriv k (g * f ^ n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      by_cases hkn : n + 1 ≤ k
      · simp [Nat.sub_eq_zero_of_le hkn]
      have hkn' : k ≤ n := by omega
      rw [pow_succ, ← mul_assoc, hasseDeriv_mul]
      apply Finset.dvd_sum
      intro ij hij
      have hij' : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
      by_cases hj : ij.2 = 0
      · have hi : ij.1 = k := by omega
        simp only [hj, hi, hasseDeriv_zero, LinearMap.id_apply]
        have he : n + 1 - k = (n - k) + 1 := by omega
        rw [he, pow_succ]
        exact mul_dvd_mul_right (ih k) f
      · have he : n + 1 - k ≤ n - ij.1 := by omega
        exact dvd_mul_of_dvd_left ((pow_dvd_pow f he).trans (ih ij.1)) _

variable {F : Type*} [Field F]

private theorem stepanov_hasse_div_mul (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    (hasseDeriv k (g * f ^ n) / f ^ (n - k)) * f ^ (n - k) =
      hasseDeriv k (g * f ^ n) := by
  rw [mul_comm]
  exact EuclideanDomain.mul_div_cancel' (pow_ne_zero _ hf)
    (stepanov_pow_dvd_hasseDeriv_mul_pow f g n k)

/-- Harcos's `g ↦ g⁽ᵏ⁾` as an actual linear map, for every nonzero `f`.
It is defined for all `k`; the degree estimate below uses `k ≤ n`. -/
def stepanovHasseOperator (f : F[X]) (hf : f ≠ 0) (n k : ℕ) :
    F[X] →ₗ[F] F[X] where
  toFun g := hasseDeriv k (g * f ^ n) / f ^ (n - k)
  map_add' g h := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [add_mul, stepanov_hasse_div_mul f hf, map_add]
  map_smul' c g := by
    apply mul_right_cancel₀ (pow_ne_zero (n - k) hf)
    rw [stepanov_hasse_div_mul f hf]
    simp only [RingHom.id_apply, smul_mul_assoc, stepanov_hasse_div_mul f hf, map_smul]

@[simp]
theorem stepanovHasseOperator_apply (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    stepanovHasseOperator f hf n k g =
      hasseDeriv k (g * f ^ n) / f ^ (n - k) := rfl

/-- The factorization in Harcos Lemma 10, including the endpoint `k = n`. -/
theorem stepanovHasseOperator_spec (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (g : F[X]) :
    hasseDeriv k (g * f ^ n) =
      stepanovHasseOperator f hf n k g * f ^ (n - k) :=
  (stepanov_hasse_div_mul f hf n k g).symm

@[simp]
theorem stepanovHasseOperator_zero (f : F[X]) (hf : f ≠ 0)
    (n : ℕ) (g : F[X]) :
    stepanovHasseOperator f hf n 0 g = g := by
  simp only [stepanovHasseOperator_apply, hasseDeriv_zero, LinearMap.id_apply, Nat.sub_zero]
  exact mul_div_cancel_right₀ g (pow_ne_zero n hf)

@[simp]
theorem stepanovHasseOperator_self (f : F[X]) (hf : f ≠ 0)
    (n : ℕ) (g : F[X]) :
    stepanovHasseOperator f hf n n g = hasseDeriv n (g * f ^ n) := by
  simpa only [Nat.sub_self, pow_zero, mul_one] using
    (stepanovHasseOperator_spec f hf n n g).symm

/-- The natural-degree form of Harcos's estimate; valid also for `g = 0`. -/
theorem stepanovHasseOperator_natDegree_le (f : F[X]) (hf : f ≠ 0)
    (n k : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree) (g : F[X]) :
    (stepanovHasseOperator f hf n k g).natDegree ≤
      g.natDegree + k * (f.natDegree - 1) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · simp only [hq, natDegree_zero, zero_le]
  have hg : g ≠ 0 := by
    intro hg
    apply hq
    rw [hg, map_zero]
  have hd := natDegree_hasseDeriv_le (g * f ^ n) k
  rw [stepanovHasseOperator_spec f hf n k g,
    natDegree_mul hq (pow_ne_zero _ hf),
    natDegree_mul hg (pow_ne_zero _ hf), natDegree_pow, natDegree_pow] at hd
  have hkm : k ≤ g.natDegree + n * f.natDegree := by nlinarith
  have hnm : (n - k) * f.natDegree + k * f.natDegree = n * f.natDegree := by
    rw [← add_mul, Nat.sub_add_cancel hkn]
  have hkm' : k * (f.natDegree - 1) + k = k * f.natDegree := by
    calc
      k * (f.natDegree - 1) + k = k * ((f.natDegree - 1) + 1) := by ring
      _ = k * f.natDegree := by rw [Nat.sub_add_cancel hm]
  have hsub := Nat.sub_add_cancel hkm
  omega

/-- The strict degree bound used to size Stepanov's coefficient system.
Unlike a `natDegree < B` hypothesis, `degree < B` handles `g = 0`, even
when `B = 0`. -/
theorem stepanovHasseOperator_degree_lt (f : F[X]) (hf : f ≠ 0)
    (n k B : ℕ) (hkn : k ≤ n) (hm : 1 ≤ f.natDegree)
    (g : F[X]) (hg : g.degree < (B : WithBot ℕ)) :
    (stepanovHasseOperator f hf n k g).degree <
      ((B + k * (f.natDegree - 1) : ℕ) : WithBot ℕ) := by
  by_cases hq : stepanovHasseOperator f hf n k g = 0
  · rw [hq, degree_zero]
    exact WithBot.bot_lt_coe _
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hq
    rw [hg0, map_zero]
  rw [degree_eq_natDegree hg0] at hg
  rw [degree_eq_natDegree hq]
  exact_mod_cast lt_of_le_of_lt
    (stepanovHasseOperator_natDegree_le f hf n k hkn hm g)
    (Nat.add_lt_add_right (WithBot.coe_lt_coe.mp hg) _)

/-- Harcos Lemma 8: vanishing of the first Hasse derivatives is exactly
divisibility by the corresponding power of the linear factor. -/
theorem stepanov_hasse_vanishing_iff_pow_dvd
    {R : Type*} [CommRing R] (h : R[X]) (x : R) (ell : ℕ) :
    (∀ k < ell, (hasseDeriv k h).eval x = 0) ↔
      (X - C x) ^ ell ∣ h := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  simp only [← taylor_apply, taylor_coeff]

/-- The sum of root multiplicities over any finite set is at most the degree. -/
theorem stepanov_sum_rootMultiplicity_le (h : F[X]) (s : Finset F) :
    ∑ x ∈ s, h.rootMultiplicity x ≤ h.natDegree := by
  classical
  calc
    ∑ x ∈ s, h.rootMultiplicity x = ∑ x ∈ s, h.roots.count x := by
      simp only [count_roots]
    _ ≤ ∑ x ∈ s ∪ h.roots.toFinset, h.roots.count x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (by intros; exact Nat.zero_le _)
    _ = ∑ x ∈ h.roots.toFinset, h.roots.count x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro x _ hx
      exact Multiset.count_eq_zero.mpr (by simpa only [Multiset.mem_toFinset] using hx)
    _ = h.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := card_roots' h

/-- Finite-root degree bound with a possibly different vanishing order at
each point. The nonzero hypothesis is essential here. -/
theorem stepanov_sum_hasse_orders_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (orders : F → ℕ)
    (hv : ∀ x ∈ s, ∀ k < orders x, (hasseDeriv k h).eval x = 0) :
    ∑ x ∈ s, orders x ≤ h.natDegree := by
  calc
    ∑ x ∈ s, orders x ≤ ∑ x ∈ s, h.rootMultiplicity x := by
      apply Finset.sum_le_sum
      intro x hx
      exact (le_rootMultiplicity_iff hh).mpr
        ((stepanov_hasse_vanishing_iff_pow_dvd h x (orders x)).mp (hv x hx))
    _ ≤ h.natDegree := stepanov_sum_rootMultiplicity_le h s

/-- If a nonzero polynomial vanishes to Hasse order at least `ell` at every
point of a finite set, then `ell` times the number of points is at most its degree. -/
theorem stepanov_card_mul_hasse_order_le (h : F[X]) (hh : h ≠ 0)
    (s : Finset F) (ell : ℕ)
    (hv : ∀ x ∈ s, ∀ k < ell, (hasseDeriv k h).eval x = 0) :
    s.card * ell ≤ h.natDegree := by
  simpa using
    stepanov_sum_hasse_orders_le h hh s (fun _ ↦ ell) hv

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
