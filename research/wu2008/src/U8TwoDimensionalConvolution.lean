import U8TwoDimensionalMain

/-! The missing logarithm is not hidden in Liu's denominator. It comes from
an independent reciprocal-totient factor, combined by exact lcm convolution. -/
noncomputable section
open Finset
open scoped BigOperators
namespace U8Literal.SmallProduct.TwoDimensional
open scoped Classical

def liuFactor (N : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ N then 0 else 1 / ((p : ℝ)-2))

def harmonicFactor : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => 1 / ((p : ℝ)-1))

def dimensionTwoFactor (N : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => roots N p / ((p : ℝ)-roots N p))

def lcmConvolution (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, if n = Nat.lcm d e then f d*g e else 0

theorem sum_lcmConvolution (f g : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, lcmConvolution f g k) =
      (∑ d ∈ n.divisors, f d)*(∑ e ∈ n.divisors, g e) := by
  have extend (k : ℕ) (hk : k ∈ n.divisors) :
      lcmConvolution f g k =
      ∑ d ∈ n.divisors, ∑ e ∈ n.divisors,
        if k = Nat.lcm d e then f d*g e else 0 := by
    unfold lcmConvolution
    rw [← Nat.divisors_filter_dvd_of_dvd hn (Nat.mem_divisors.mp hk).1]
    simp only [sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases hdk : d ∣ k
    · simp only [if_pos hdk]
      apply sum_congr rfl
      intro e _
      by_cases hek : e ∣ k
      · simp [hek]
      · have hne : k ≠ Nat.lcm d e := fun h => hek (h ▸ Nat.dvd_lcm_right d e)
        simp [hek,hne]
    · have hne (e : ℕ) : k ≠ Nat.lcm d e := fun h => hdk (h ▸ Nat.dvd_lcm_left d e)
      simp [hdk,hne]
  rw [sum_congr rfl extend, sum_comm, sum_mul_sum]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  exact sum_ite_eq_of_mem' n.divisors (Nat.lcm d e) (fun _ => f d*g e) (Nat.mem_divisors.mpr
    ⟨Nat.lcm_dvd (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp he).1,hn⟩)

theorem local_lcm_identity {N p : ℕ} (hN : Even N) (hp : p.Prime) :
    1 + dimensionTwoFactor N p = (1 + liuFactor N p)*(1 + harmonicFactor p) := by
  simp only [dimensionTwoFactor, liuFactor, harmonicFactor,
    ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors, prod_singleton]
  have hp1 : (p : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hp.one_lt))
  unfold roots
  split_ifs with h
  · ring
  · have hp2 : (p : ℝ)-2 ≠ 0 := by
      have := roots_lt hN hp
      rw [roots, if_neg h] at this
      linarith
    field_simp
    ring

theorem divisor_sum_dimensionTwoFactor {N n : ℕ} (hN : Even N) (hn : Squarefree n) :
    (∑ d ∈ n.divisors, dimensionTwoFactor N d) =
      (∑ d ∈ n.divisors, liuFactor N d)*(∑ e ∈ n.divisors, harmonicFactor e) := by
  rw [← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree hn,
    ← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree hn,
    ← (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _).prodPrimeFactors_one_add_of_squarefree hn,
    ← prod_mul_distrib]
  exact prod_congr rfl (fun p hp => local_lcm_identity hN (Nat.prime_of_mem_primeFactors hp))

/-- Exact coefficient-level convolution; it includes overlaps, not just coprime
Dirichlet convolution. Thus the second logarithm has a concrete positive source. -/
theorem dimensionTwoFactor_eq_lcmConvolution {N n : ℕ} (hN : Even N) (hn : Squarefree n) :
    dimensionTwoFactor N n = lcmConvolution (liuFactor N) harmonicFactor n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs := (divisor_sum_dimensionTwoFactor hN hn).trans
      (sum_lcmConvolution (liuFactor N) harmonicFactor hn.ne_zero).symm
    have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _,hn.ne_zero⟩
    rw [← add_sum_erase _ _ hnmem, ← add_sum_erase _ _ hnmem] at hs
    have heq :
        (∑ d ∈ n.divisors.erase n, dimensionTwoFactor N d) =
        ∑ d ∈ n.divisors.erase n, lcmConvolution (liuFactor N) harmonicFactor d := by
      apply sum_congr rfl
      intro d hd
      have hdm := mem_erase.mp hd
      have hdn := (Nat.mem_divisors.mp hdm.2).1
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) hdn) hdm.1)
        (hn.squarefree_of_dvd hdn)
    linarith

end U8Literal.SmallProduct.TwoDimensional
