import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEta
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Actual coefficient sums for Harcos's L-polynomial

The monic polynomials are parametrized by all their lower coefficients, not
by an assumed list of L-function coefficients. Source: Harcos, §3, Theorem 5,
`pages/harcos-lpolynomial-06.png`.
-/

noncomputable section

open Finset Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- A monic polynomial with the given vector of lower coefficients. -/
def harcosMonic (n : ℕ) (v : Fin n → ZMod p) : (ZMod p)[X] :=
  X ^ n + Polynomial.ofFn n v

theorem harcosMonic_monic (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).Monic := by
  apply (monic_X_pow n).add_of_left
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_natDegree (n : ℕ) (v : Fin n → ZMod p) :
    (harcosMonic n v).natDegree = n := by
  unfold harcosMonic
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa using Polynomial.ofFn_degree_lt v

theorem harcosMonic_coeff_lt (n : ℕ) (v : Fin n → ZMod p) (i : ℕ)
    (hi : i < n) : (harcosMonic n v).coeff i = v ⟨i, hi⟩ := by
  simp [harcosMonic, Polynomial.ofFn_coeff_eq_val_of_lt v hi, ne_of_lt hi]

theorem harcosMonic_unique (n : ℕ) (f : (ZMod p)[X])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ∃! v : Fin n → ZMod p, harcosMonic n v = f := by
  refine ⟨fun i ↦ f.coeff i, ?_, ?_⟩
  · ext i
    rcases lt_trichotomy i n with hi | hi | hi
    · exact harcosMonic_coeff_lt n _ i hi
    · subst i
      have he : (harcosMonic n (fun i ↦ f.coeff i)).coeff n = 1 := by
        simpa only [Polynomial.leadingCoeff, harcosMonic_natDegree] using
          (harcosMonic_monic n (fun i ↦ f.coeff i)).leadingCoeff
      rw [he, ← hd, coeff_natDegree, hm.leadingCoeff]
    · rw [coeff_eq_zero_of_natDegree_lt (by rwa [harcosMonic_natDegree]),
        coeff_eq_zero_of_natDegree_lt (by rwa [hd])]
  · intro v hv
    funext i
    have h := congrArg (fun g : (ZMod p)[X] ↦ g.coeff i) hv
    simpa only [harcosMonic_coeff_lt n v i i.isLt] using h

theorem harcosMonic_injective (n : ℕ) :
    Function.Injective (harcosMonic (p := p) n) := by
  intro v w h
  funext i
  have hc := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) h
  simpa only [harcosMonic_coeff_lt n v i i.isLt,
    harcosMonic_coeff_lt n w i i.isLt] using hc

/-- Exactly the finite set of monic polynomials of degree `n`. -/
def harcosMonicPolynomials (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  Finset.univ.image (harcosMonic n)

theorem mem_harcosMonicPolynomials (n : ℕ) (f : (ZMod p)[X]) :
    f ∈ harcosMonicPolynomials p n ↔ f.Monic ∧ f.natDegree = n := by
  classical
  constructor
  · intro hf
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨harcosMonic_monic n v, harcosMonic_natDegree n v⟩
  · rintro ⟨hm, hd⟩
    obtain ⟨v, hv, _⟩ := harcosMonic_unique n f hm hd
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩

theorem harcosMonicPolynomials_card (n : ℕ) :
    (harcosMonicPolynomials p n).card = p ^ n := by
  classical
  rw [harcosMonicPolynomials, Finset.card_image_of_injective _ (harcosMonic_injective n)]
  simp

theorem harcosMonic_zero (v : Fin 0 → ZMod p) : harcosMonic 0 v = 1 := by
  simp [harcosMonic]

theorem harcosMonic_one (v : Fin 1 → ZMod p) :
    harcosMonic 1 v = X + C (v 0) := by
  unfold harcosMonic
  rw [pow_one]
  congr 1
  ext i
  cases i with
  | zero => simp [Polynomial.ofFn_coeff_eq_val_of_lt]
  | succ i =>
    simp [Polynomial.ofFn_coeff_eq_zero_of_ge v (by omega : 1 ≤ i + 1)]

/-- The genuine finite monic-degree coefficient sum of the polynomial character. -/
def harcosCoefficient (a b : ZMod p) (n : ℕ) : ℂ :=
  ∑ v : Fin n → ZMod p, harcosEta a b (harcosMonic n v)

theorem harcosCoefficient_eq_sum_monic (a b : ZMod p) (n : ℕ) :
    harcosCoefficient a b n =
      ∑ f ∈ harcosMonicPolynomials p n, harcosEta a b f := by
  classical
  rw [harcosMonicPolynomials, Finset.sum_image]
  · rfl
  · intro v _ w _ h
    exact harcosMonic_injective n h

/-- Interface to finite-UFD sums indexed by Mathlib's degree-exact monic subtype. -/
theorem harcosCoefficient_eq_sum_monicDegreeEq (a b : ZMod p) (n : ℕ)
    [Fintype (Polynomial.MonicDegreeEq (ZMod p) n)] :
    harcosCoefficient a b n =
      ∑ f : Polynomial.MonicDegreeEq (ZMod p) n, harcosEta a b f.val := by
  rw [harcosCoefficient]
  apply Fintype.sum_bijective (fun v : Fin n → ZMod p ↦
    Polynomial.MonicDegreeEq.mk (harcosMonic n v)
      (harcosMonic_monic n v) (harcosMonic_natDegree n v))
  · constructor
    · intro v w h
      exact harcosMonic_injective n (congrArg Subtype.val h)
    · intro f
      obtain ⟨v, hv, _⟩ := harcosMonic_unique n f.val f.monic f.natDegree
      exact ⟨v, Subtype.ext hv⟩
  · intro v
    rfl

theorem harcosCoefficient_norm_le (a b : ZMod p) (n : ℕ) :
    ‖harcosCoefficient a b n‖ ≤ (p : ℝ) ^ n := by
  rw [harcosCoefficient_eq_sum_monic]
  calc
    ‖∑ f ∈ harcosMonicPolynomials p n, harcosEta a b f‖ ≤
        ∑ f ∈ harcosMonicPolynomials p n, ‖harcosEta a b f‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ harcosMonicPolynomials p n, (1 : ℝ) :=
      Finset.sum_le_sum (fun f _ ↦ harcosEta_norm_le_one a b f)
    _ = (p : ℝ) ^ n := by simp [harcosMonicPolynomials_card]

theorem harcosCoefficient_zero (a b : ZMod p) : harcosCoefficient a b 0 = 1 := by
  simp [harcosCoefficient, harcosMonic_zero, harcosEta_one]

theorem harcosCoefficient_one (a : ZMod p) (b : ℤ) :
    harcosCoefficient a (b : ZMod p) 1 = completeKloosterman p a b := by
  classical
  rw [harcosCoefficient, completeKloosterman_eq]
  calc
    ∑ v : Fin 1 → ZMod p, harcosEta a (b : ZMod p) (harcosMonic 1 v) =
        ∑ t : ZMod p, harcosEta a (b : ZMod p) (X - C t) := by
      apply Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ -v 0)
      · constructor
        · intro v w h
          funext i
          have hi : i = 0 := Subsingleton.elim _ _
          simpa only [hi] using neg_injective h
        · intro t
          exact ⟨fun _ ↦ -t, neg_neg t⟩
      · intro v
        simp [harcosMonic_one, sub_eq_add_neg]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [harcosEta_X_sub_C]
      by_cases ht : t = 0 <;> simp [ht, isUnit_iff_ne_zero]

theorem harcosEta_monic_coefficients (a b : ZMod p) (n : ℕ)
    (hn : 2 ≤ n) (v : Fin n → ZMod p) :
    harcosEta a b (harcosMonic n v) =
      if v ⟨0, by omega⟩ = 0 then 0 else
        ZMod.stdAddChar (-a * v ⟨n - 1, by omega⟩ -
          b * (v ⟨1, by omega⟩ / v ⟨0, by omega⟩)) := by
  have hn' : 0 < (harcosMonic n v).natDegree := by
    rw [harcosMonic_natDegree]; omega
  simp only [harcosEta, nextCoeff_of_natDegree_pos hn', harcosMonic_natDegree,
    (harcosMonic_monic n v).leadingCoeff, div_one,
    harcosMonic_coeff_lt n v 0 (by omega),
    harcosMonic_coeff_lt n v 1 (by omega),
    harcosMonic_coeff_lt n v (n - 1) (by omega)]

private theorem sum_snoc (n : ℕ) (f : (Fin (n + 1) → ZMod p) → ℂ) :
    ∑ v, f v = ∑ t : ZMod p, ∑ w : Fin n → ZMod p, f (Fin.snoc w t) := by
  calc
    _ = ∑ z : ZMod p × (Fin n → ZMod p), f (Fin.snoc z.2 z.1) :=
      Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ZMod p)).symm
        _ _ (fun _ ↦ by simp [Fin.snocEquiv])
    _ = _ := Fintype.sum_prod_type _

private theorem sum_char_mul (c : ZMod p) :
    ∑ t : ZMod p, ZMod.stdAddChar (c * t) = if c = 0 then (p : ℂ) else 0 := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [if_neg hc]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hc)

theorem harcosCoefficient_ge_three (a b : ZMod p) (ha : a ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) : harcosCoefficient a b n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 3 + m = (m + 2) + 1 by omega, harcosCoefficient, sum_snoc, sum_comm]
  apply Finset.sum_eq_zero
  intro w _
  have he (t : ZMod p) :
      harcosEta a b (harcosMonic (m + 2 + 1) (Fin.snoc w t)) =
        if w ⟨0, by omega⟩ = 0 then 0 else
          ZMod.stdAddChar (-a * t) *
            ZMod.stdAddChar (-b * (w ⟨1, by omega⟩ / w ⟨0, by omega⟩)) := by
    rw [harcosEta_monic_coefficients a b _ (by omega)]
    simp [Fin.snoc, Fin.castLT, sub_eq_add_neg, AddChar.map_add_eq_mul]
  simp_rw [he]
  by_cases hw : w ⟨0, by omega⟩ = 0
  · simp only [hw, if_true, sum_const_zero]
  · simp only [hw, if_false, ← Finset.sum_mul, sum_char_mul, neg_ne_zero.mpr ha,
      if_false, zero_mul]

private theorem sum_fin_one (f : ZMod p → ℂ) :
    ∑ v : Fin 1 → ZMod p, f (v 0) = ∑ c : ZMod p, f c := by
  refine Fintype.sum_bijective (fun v : Fin 1 → ZMod p ↦ v 0) ?_ _ _ (fun _ ↦ rfl)
  constructor
  · intro v w h
    funext i
    simpa only [show i = 0 from Subsingleton.elim _ _] using h
  · intro c
    exact ⟨fun _ ↦ c, rfl⟩

theorem harcosCoefficient_two_sum (a b : ZMod p) :
    harcosCoefficient a b 2 =
      ∑ c : ZMod p, if c = 0 then 0 else
        ∑ t : ZMod p, ZMod.stdAddChar ((-a - b / c) * t) := by
  rw [harcosCoefficient, show 2 = 1 + 1 from rfl, sum_snoc]
  have he (t : ZMod p) (w : Fin 1 → ZMod p) :
      harcosEta a b (harcosMonic 2 (Fin.snoc w t)) =
        if w 0 = 0 then 0 else ZMod.stdAddChar ((-a - b / w 0) * t) := by
    rw [harcosEta_monic_coefficients a b 2 (by omega)]
    simp only [Fin.snoc, Fin.castLT, Fin.val_mk]
    simp
    congr 2
    ring
  simp_rw [he]
  conv_lhs =>
    arg 2
    ext t
    rw [sum_fin_one (fun c ↦ if c = 0 then 0 else
      ZMod.stdAddChar ((-a - b / c) * t))]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hc : c = 0 <;> simp [hc]

theorem harcosCoefficient_two (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosCoefficient a b 2 = (p : ℂ) := by
  classical
  rw [harcosCoefficient_two_sum]
  simp_rw [sum_char_mul]
  have hroot : -b / a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have hz (c : ZMod p) (hc : c ≠ 0) : -a - b / c = 0 ↔ c = -b / a := by
    field_simp
    constructor <;> intro h <;> linear_combination -h
  rw [Finset.sum_eq_single (-b / a)]
  · rw [if_neg hroot, if_pos ((hz _ hroot).2 rfl)]
  · intro c _ hc
    by_cases hc0 : c = 0
    · simp [hc0]
    · rw [if_neg hc0, if_neg (fun h ↦ hc ((hz c hc0).1 h))]
  · simp

/-- The formal generating series, before any coefficient evaluation. -/
def harcosLSeries (a b : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (harcosCoefficient a b)

/-- The polynomial assembled from the actual degree-zero, one, and two sums. -/
def harcosLPolynomial (a b : ZMod p) : ℂ[X] :=
  ∑ n ∈ Finset.range 3, Polynomial.monomial n (harcosCoefficient a b n)

theorem harcosLPolynomial_coeff (a b : ZMod p) (ha : a ≠ 0) (n : ℕ) :
    (harcosLPolynomial a b).coeff n = harcosCoefficient a b n := by
  classical
  simp only [harcosLPolynomial, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < 3
  · simp [hn]
  · rw [harcosCoefficient_ge_three a b ha n (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := Finset.mem_range.mp hi; omega)]

theorem harcosLPolynomial_eq (a : ZMod p) (b : ℤ) (ha : a ≠ 0)
    (hb : (b : ZMod p) ≠ 0) :
    harcosLPolynomial a (b : ZMod p) =
      1 + C (completeKloosterman p a b) * X + C (p : ℂ) * X ^ 2 := by
  simp [harcosLPolynomial, Finset.sum_range_succ, harcosCoefficient_zero,
    harcosCoefficient_one, harcosCoefficient_two a (b : ZMod p) ha hb,
    ← C_mul_X_pow_eq_monomial]

theorem harcosLSeries_eq_polynomial (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b = (harcosLPolynomial a b : PowerSeries ℂ) := by
  ext n
  simp [harcosLSeries, harcosLPolynomial_coeff a b ha]

theorem harcosCoefficient_one_residue (a b : ZMod p) :
    harcosCoefficient a b 1 = completeKloosterman p a (b.val : ℤ) := by
  simpa using harcosCoefficient_one a (b.val : ℤ)

theorem harcosLPolynomial_eq_coefficients (a b : ZMod p) :
    harcosLPolynomial a b =
      1 + C (harcosCoefficient a b 1) * X + C (harcosCoefficient a b 2) * X ^ 2 := by
  simp [harcosLPolynomial, Finset.sum_range_succ, harcosCoefficient_zero,
    ← C_mul_X_pow_eq_monomial]

/-- The first reciprocal root, constructed from the actual coefficient sums. -/
def harcosReciprocalRootPlus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 +
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

/-- The second reciprocal root; the two choices may coincide. -/
def harcosReciprocalRootMinus (a b : ZMod p) : ℂ :=
  (-harcosCoefficient a b 1 -
    Complex.sqrt ((harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2)) / 2

theorem harcosReciprocalRoots_add (a b : ZMod p) :
    harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b =
      -harcosCoefficient a b 1 := by
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  ring

theorem harcosReciprocalRoots_mul (a b : ZMod p) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b =
      harcosCoefficient a b 2 := by
  have hs : Complex.sqrt ((harcosCoefficient a b 1) ^ 2 -
      4 * harcosCoefficient a b 2) ^ 2 =
        (harcosCoefficient a b 1) ^ 2 - 4 * harcosCoefficient a b 2 := by
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  unfold harcosReciprocalRootPlus harcosReciprocalRootMinus
  linear_combination -hs / 4

/-- Factorization of the polynomial obtained from the monic-degree sums. -/
theorem harcosLPolynomial_factorization (a b : ZMod p) :
    harcosLPolynomial a b =
      (1 - C (harcosReciprocalRootPlus a b) * X) *
        (1 - C (harcosReciprocalRootMinus a b) * X) := by
  rw [harcosLPolynomial_eq_coefficients, ← harcosReciprocalRoots_mul,
    show harcosCoefficient a b 1 =
      -(harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b) by
        rw [harcosReciprocalRoots_add, neg_neg],
    map_neg, map_add, map_mul]
  ring

/-- The root factorization is an identity of the actual coefficient generating series. -/
theorem harcosLSeries_factorization (a b : ZMod p) (ha : a ≠ 0) :
    harcosLSeries a b =
      (1 - PowerSeries.C (harcosReciprocalRootPlus a b) * PowerSeries.X) *
        (1 - PowerSeries.C (harcosReciprocalRootMinus a b) * PowerSeries.X) := by
  rw [harcosLSeries_eq_polynomial a b ha, harcosLPolynomial_factorization]
  simp

theorem harcosReciprocalRoots_add_kloosterman (a b : ZMod p) :
    harcosReciprocalRootPlus a b + harcosReciprocalRootMinus a b =
      -completeKloosterman p a (b.val : ℤ) := by
  rw [harcosReciprocalRoots_add, harcosCoefficient_one_residue]

theorem harcosReciprocalRoots_mul_prime (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosReciprocalRootPlus a b * harcosReciprocalRootMinus a b = (p : ℂ) := by
  rw [harcosReciprocalRoots_mul, harcosCoefficient_two a b ha hb]

theorem harcosReciprocalRoots_ne_zero (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    harcosReciprocalRootPlus a b ≠ 0 ∧ harcosReciprocalRootMinus a b ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rw [harcosReciprocalRoots_mul_prime a b ha hb]
  exact Nat.cast_ne_zero.mpr (NeZero.ne p)

/-- The inverses are actual complex zeros of the coefficient-generated polynomial. -/
theorem harcosLPolynomial_roots (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    (harcosLPolynomial a b).IsRoot (harcosReciprocalRootPlus a b)⁻¹ ∧
      (harcosLPolynomial a b).IsRoot (harcosReciprocalRootMinus a b)⁻¹ := by
  obtain ⟨hplus, hminus⟩ := harcosReciprocalRoots_ne_zero a b ha hb
  simp [Polynomial.IsRoot, harcosLPolynomial_factorization, hplus, hminus]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
