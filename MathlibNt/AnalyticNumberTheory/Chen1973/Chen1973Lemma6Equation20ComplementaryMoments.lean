import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19DyadicPairEnergy
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6AggregateDerivativeMoment
import Mathlib.Algebra.Order.Chebyshev

noncomputable section
set_option maxHeartbeats 1200000
open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
open MathlibNt.SieveTheory.LiuWeight

def chen1973Lemma6Eq20MobiusCoefficient (s : ℂ) (n : ℤ) : ℂ :=
  ((ArithmeticFunction.moebius n.toNat : ℤ) : ℂ) / (n : ℂ) ^ s

def chen1973Lemma6Eq20MobiusSecondMoment
    (x L level H : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    chen1973Lemma6Eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2

private lemma eq20_sum_int_nat (H : ℕ) (f : ℤ → ℂ) :
    (∑ z ∈ Icc (1 : ℤ) (H : ℤ), f z) = ∑ n ∈ Icc 1 H, f (n : ℤ) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp hn).1,
      by exact_mod_cast (mem_Icc.mp hn).2⟩
  · intro a ha b hb hab
    exact_mod_cast hab
  · intro z hz
    have hzdata := mem_Icc.mp hz
    have hz0 : 0 ≤ z := by have := (mem_Icc.mp hz).1; omega
    refine ⟨z.toNat, mem_Icc.mpr ⟨?_, ?_⟩, Int.toNat_of_nonneg hz0⟩
    · omega
    · omega
  · intro n hn
    rfl

 theorem chen1973Lemma6_eq20_mobius_eq_linear
    (H : ℕ) (s : ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    chen1973Lemma6NaturalMobiusPolynomial H s χ =
      ∑ z ∈ Icc (1 : ℤ) (H : ℤ),
        chen1973Lemma6Eq20MobiusCoefficient s z * χ.1 (z : ZMod d) := by
  rw [eq20_sum_int_nat]
  unfold chen1973Lemma6NaturalMobiusPolynomial chen1973Lemma6MobiusPartialSum
  apply Finset.sum_congr rfl
  intro n hn
  simp only [chen1973Lemma6Eq20MobiusCoefficient, Int.toNat_natCast,
    Int.cast_natCast]
  ring

 theorem chen1973Lemma6_eq20_mobius_atom_energy
    (s : ℂ) (hs : 1 / 2 ≤ s.re) {n : ℤ} (hn : 1 ≤ n) :
    ‖chen1973Lemma6Eq20MobiusCoefficient s n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmu : ‖((ArithmeticFunction.moebius n.toNat : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n.toNat)
  unfold chen1973Lemma6Eq20MobiusCoefficient
  rw [norm_div, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
  calc
    _ ≤ (1 / (n : ℝ) ^ s.re) ^ 2 := by gcongr
    _ = (n : ℝ) ^ (-2 * s.re) := by
      rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
        one_div, ← Real.rpow_neg hnpos.le]
      congr 1
      ring
    _ ≤ (n : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    _ = _ := Real.rpow_neg_one _

 theorem chen1973Lemma6_eq20_mobius_coefficient_energy
    (H : ℕ) (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    (∑ z ∈ Icc (1 : ℤ) (H : ℤ), ‖chen1973Lemma6Eq20MobiusCoefficient s z‖ ^ 2) ≤
      1 + Real.log H := by
  calc
    _ ≤ ∑ z ∈ Icc (1 : ℤ) (H : ℤ), (z : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun z hz =>
        chen1973Lemma6_eq20_mobius_atom_energy s hs (mem_Icc.mp hz).1
    _ = liuHarmonic H := by
      unfold liuHarmonic
      symm
      apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
      · intro n hn
        exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp hn).1,
          by exact_mod_cast (mem_Icc.mp hn).2⟩
      · intro a ha b hb hab
        exact_mod_cast hab
      · intro z hz
        have hzdata := mem_Icc.mp hz
        have hz0 : 0 ≤ z := by have := (mem_Icc.mp hz).1; omega
        refine ⟨z.toNat, mem_Icc.mpr ⟨by omega, by omega⟩, Int.toNat_of_nonneg hz0⟩
      · intro n hn
        simp
    _ ≤ _ := liuHarmonic_le_one_add_log H

/-- Fresh sharp LS on M=0,N=H. Valid for every imaginary height. -/
theorem chen1973Lemma6_eq20_mobius_second_moment
    (x L level H D Q : ℕ) (s : ℂ) (hs : 1 / 2 ≤ s.re) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq20MobiusSecondMoment x L level H s ≤
      chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level *
        ((Q : ℝ) + (H : ℝ) / D) * (1 + Real.log H) := by
  have hLS := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6Eq20MobiusCoefficient s) 0 H D Q hD
  have hE := chen1973Lemma6_eq20_mobius_coefficient_energy H s hs
  have hlin : (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2) ≤
      chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) + (H : ℝ) / D) *
        (1 + Real.log H) := by
    simp only [Int.zero_add] at hLS
    simp_rw [chen1973Lemma6_eq20_mobius_eq_linear]
    exact hLS.trans (mul_le_mul_of_nonneg_left hE
      (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le (by positivity)))
  unfold chen1973Lemma6Eq20MobiusSecondMoment
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2 :=
      chen1973Lemma6_eq19_weight_transport _ (fun d => by positivity)
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (chen1973Lemma6Eq19I_pos x L level).le
      exact Finset.sum_le_sum_of_subset_of_nonneg hcell (fun d hd hnot => by positivity)
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) + (H : ℝ) / D) *
          (1 + Real.log H)) := mul_le_mul_of_nonneg_left hlin
            (chen1973Lemma6Eq19I_pos x L level).le
    _ = _ := by ring


/-- The unchanged actual pair polynomial from (17). -/
def chen1973Lemma6Eq20PairPolynomial
    (x B k m : ℕ) {d : ℕ} (s : ℂ) (χ : PrimitiveCharacter d) : ℂ :=
  ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
    χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
      ((pp.1 * pp.2 : ℂ) ^ s *
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))

def chen1973Lemma6Eq20PairFourthMoment
    (x L level B k m : ℕ) (s : ℂ) : ℝ :=
  ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
    chen1973Lemma6Eq19Weight d * ∑ χ : PrimitiveCharacter d,
      ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖ ^ 4

private lemma eq20_sum_mul_le_sqrt
    {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, f i * g i) ≤
      Real.sqrt (∑ i, f i ^ 2) * Real.sqrt (∑ i, g i ^ 2) := by
  simpa using Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) f g

private lemma eq20_sqrt_mono {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab

/-- Source equation-(20) Holder allocation: S², pair⁴, derivative⁴. -/
theorem chen1973Lemma6B_le_eq20_moment_product
    (x L level B k m H : ℕ) (s : ℂ) :
    chen1973Lemma6B x L level B k m H s ≤
      Real.sqrt (chen1973Lemma6Eq20MobiusSecondMoment x L level H s) *
        Real.sqrt
          (Real.sqrt (chen1973Lemma6Eq19LDerivFourthMoment x L level s) *
            Real.sqrt (chen1973Lemma6Eq20PairFourthMoment x L level B k m s)) := by
  let S := chen1973Lemma6ConductorBlock x L level
  let w : ℕ → ℝ := fun d => chen1973Lemma6Eq19Weight d
  let P : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ ^ 2
  let R : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    (‖chen1973PrimitiveLDeriv d s χ‖ *
      ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖) ^ 2
  let D4 : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973PrimitiveLDeriv d s χ‖ ^ 4
  let M4 : ℕ → ℝ := fun d => ∑ χ : PrimitiveCharacter d,
    ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖ ^ 4
  have hw (d : ℕ) : 0 ≤ w d := chen1973Lemma6_eq19Weight_nonneg d
  have hP (d : ℕ) : 0 ≤ P d := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR (d : ℕ) : 0 ≤ R d := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hD4 (d : ℕ) : 0 ≤ D4 d := Finset.sum_nonneg fun _ _ => by positivity
  have hM4 (d : ℕ) : 0 ≤ M4 d := Finset.sum_nonneg fun _ _ => by positivity
  have hchar (d : ℕ) :
      (∑ χ : PrimitiveCharacter d,
        ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖ *
        (‖chen1973PrimitiveLDeriv d s χ‖ *
          ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖)) ≤
        Real.sqrt (P d) * Real.sqrt (R d) := by
    simpa [P, R] using eq20_sum_mul_le_sqrt
      (fun χ : PrimitiveCharacter d =>
        ‖chen1973Lemma6NaturalMobiusPolynomial H s χ‖)
      (fun χ : PrimitiveCharacter d =>
        ‖chen1973PrimitiveLDeriv d s χ‖ *
          ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖)
  have hRpoint (d : ℕ) : R d ≤ Real.sqrt (D4 d) * Real.sqrt (M4 d) := by
    have h := eq20_sum_mul_le_sqrt
      (fun χ : PrimitiveCharacter d => ‖chen1973PrimitiveLDeriv d s χ‖ ^ 2)
      (fun χ : PrimitiveCharacter d =>
        ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖ ^ 2)
    simpa only [R, D4, M4, pow_two, pow_succ, pow_zero, mul_one, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using h
  have houter :
      (∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d))) ≤
        Real.sqrt (∑ d ∈ S, w d * P d) *
          Real.sqrt (∑ d ∈ S, w d * R d) := by
    calc
      _ = ∑ d ∈ S,
          (Real.sqrt (w d) * Real.sqrt (P d)) *
            (Real.sqrt (w d) * Real.sqrt (R d)) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [show (Real.sqrt (w d) * Real.sqrt (P d)) *
              (Real.sqrt (w d) * Real.sqrt (R d)) =
              Real.sqrt (w d) ^ 2 *
                (Real.sqrt (P d) * Real.sqrt (R d)) by ring,
            Real.sq_sqrt (hw d)]
      _ ≤ Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (P d)) ^ 2) *
          Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (R d)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ = _ := by
        congr 1 <;> apply congrArg Real.sqrt <;>
          apply Finset.sum_congr rfl <;> intro d hd <;>
          rw [mul_pow, Real.sq_sqrt (hw d)]
        · rw [Real.sq_sqrt (hP d)]
        · rw [Real.sq_sqrt (hR d)]
  have hprod :
      (∑ d ∈ S, w d * R d) ≤
        Real.sqrt (∑ d ∈ S, w d * D4 d) *
          Real.sqrt (∑ d ∈ S, w d * M4 d) := by
    calc
      _ ≤ ∑ d ∈ S, w d * (Real.sqrt (D4 d) * Real.sqrt (M4 d)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hRpoint d) (hw d)
      _ = ∑ d ∈ S,
          (Real.sqrt (w d) * Real.sqrt (D4 d)) *
            (Real.sqrt (w d) * Real.sqrt (M4 d)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [show (Real.sqrt (w d) * Real.sqrt (D4 d)) *
            (Real.sqrt (w d) * Real.sqrt (M4 d)) =
            Real.sqrt (w d) ^ 2 *
              (Real.sqrt (D4 d) * Real.sqrt (M4 d)) by ring,
          Real.sq_sqrt (hw d)]
      _ ≤ Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (D4 d)) ^ 2) *
          Real.sqrt (∑ d ∈ S,
            (Real.sqrt (w d) * Real.sqrt (M4 d)) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt S _ _
      _ = _ := by
        congr 1 <;> apply congrArg Real.sqrt <;>
          apply Finset.sum_congr rfl <;> intro d hd <;>
          rw [mul_pow, Real.sq_sqrt (hw d)]
        · rw [Real.sq_sqrt (hD4 d)]
        · rw [Real.sq_sqrt (hM4 d)]
  have hfirst : chen1973Lemma6B x L level B k m H s ≤
        ∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d)) := by
    unfold chen1973Lemma6B
    apply Finset.sum_le_sum
    intro d hd
    apply mul_le_mul_of_nonneg_left
    · have hc := hchar d
      simpa only [chen1973Lemma6Eq20PairPolynomial, norm_mul,
        chen1973Lemma6NaturalMobiusPolynomial, mul_assoc, mul_left_comm, mul_comm] using hc
    · exact hw d
  calc
    _ ≤ ∑ d ∈ S, w d * (Real.sqrt (P d) * Real.sqrt (R d)) := hfirst
    _ ≤ Real.sqrt (∑ d ∈ S, w d * P d) *
        Real.sqrt (∑ d ∈ S, w d * R d) := houter
    _ ≤ Real.sqrt (∑ d ∈ S, w d * P d) *
        Real.sqrt
          (Real.sqrt (∑ d ∈ S, w d * D4 d) *
            Real.sqrt (∑ d ∈ S, w d * M4 d)) := by
      exact mul_le_mul_of_nonneg_left
        (eq20_sqrt_mono (Finset.sum_nonneg fun d hd => mul_nonneg (hw d) (hR d)) hprod)
        (Real.sqrt_nonneg _)
    _ = _ := by
      rfl


private abbrev Eq20Four := (ℕ × ℕ) × (ℕ × ℕ)
private def eq20Product (a : Eq20Four) : ℕ := (a.1.1 * a.1.2) * (a.2.1 * a.2.2)

private lemma eq20_shell_primes {x B k m : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ chen1973Lemma6PrimePairShell x B k m) : p.1.Prime ∧ p.2.Prime := by
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hp
  have hh := hp.1.1
  rw [chen1973Lemma5PrimePairs, Finset.mem_filter] at hh
  exact ⟨hh.2.1, hh.2.2.1⟩

private lemma eq20_prime_four {p a b c d : ℕ} (hp : p.Prime)
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (h : p ∣ (a * b) * (c * d)) : p ∈ ({a, b, c, d} : Finset ℕ) := by
  have heq {r : ℕ} (hr : r.Prime) (hh : p ∣ r) : p = r := by
    rcases (Nat.dvd_prime hr).mp hh with hh | hh
    · exact (hp.ne_one hh).elim
    · exact hh
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · simp [heq ha h]
    · simp [heq hb h]
  · rcases hp.dvd_mul.mp h with h | h
    · simp [heq hc h]
    · simp [heq hd h]

/-- A structural (deliberately generous) bound: every one of the four prime
coordinates lies among the four fixed prime factors of one representative.
No enumeration or numerical search is used. -/
theorem chen1973Lemma6_eq20_pair_square_fiber_card (x B k m n : ℕ) :
    (((chen1973Lemma6PrimePairShell x B k m).product
      (chen1973Lemma6PrimePairShell x B k m)).filter
        (fun a => eq20Product a = n)).card ≤ 256 := by
  let S := chen1973Lemma6PrimePairShell x B k m
  let F := (S.product S).filter (fun a => eq20Product a = n)
  change F.card ≤ 256
  by_cases hF : F = ∅
  · simp [hF]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have ha' := Finset.mem_filter.mp ha
  have hap := Finset.mem_product.mp ha'.1
  obtain ⟨ha1, ha2⟩ := eq20_shell_primes hap.1
  obtain ⟨ha3, ha4⟩ := eq20_shell_primes hap.2
  let T : Finset ℕ := {a.1.1, a.1.2, a.2.1, a.2.2}
  have hsub : F ⊆ (T.product T).product (T.product T) := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hbp := Finset.mem_product.mp hb'.1
    obtain ⟨hb1, hb2⟩ := eq20_shell_primes hbp.1
    obtain ⟨hb3, hb4⟩ := eq20_shell_primes hbp.2
    have heq : eq20Product b = eq20Product a := hb'.2.trans ha'.2.symm
    have hp {p : ℕ} (hprime : p.Prime) (hdiv : p ∣ eq20Product b) : p ∈ T := by
      rw [heq] at hdiv
      exact eq20_prime_four hprime ha1 ha2 ha3 ha4 hdiv
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_product.mpr
    · exact ⟨hp hb1 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
        hp hb2 (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)⟩
    · exact ⟨hp hb3 (dvd_mul_of_dvd_right (dvd_mul_right _ _) _),
        hp hb4 (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)⟩
  have hT : T.card ≤ 4 := by
    have h1 := Finset.card_insert_le a.1.1 ({a.1.2, a.2.1, a.2.2} : Finset ℕ)
    have h2 := Finset.card_insert_le a.1.2 ({a.2.1, a.2.2} : Finset ℕ)
    have h3 := Finset.card_insert_le a.2.1 ({a.2.2} : Finset ℕ)
    simp only [Finset.card_singleton] at h3
    dsimp [T]
    omega
  calc
    F.card ≤ ((T.product T).product (T.product T)).card := Finset.card_le_card hsub
    _ = (T.card * T.card) * (T.card * T.card) :=
      (Finset.card_product (T.product T) (T.product T)).trans
        (congrArg (fun z : ℕ => z*z) (Finset.card_product T T))
    _ ≤ (4 * 4) * (4 * 4) := Nat.mul_le_mul (Nat.mul_le_mul hT hT) (Nat.mul_le_mul hT hT)
    _ = 256 := by norm_num

/-- The coefficient of the square of the actual shell polynomial. -/
def chen1973Lemma6Eq20PairSquareCoefficient
    (x B k m : ℕ) (s : ℂ) (n : ℤ) : ℂ :=
  ∑ a ∈ (chen1973Lemma6PrimePairShell x B k m).product
      (chen1973Lemma6PrimePairShell x B k m),
    if (eq20Product a : ℤ) = n then
      chen1973Lemma6Eq19PairAtom x s a.1 * chen1973Lemma6Eq19PairAtom x s a.2 else 0

private lemma eq20_product_interval {x B k m : ℕ} {a : Eq20Four}
    (ha : a ∈ (chen1973Lemma6PrimePairShell x B k m).product
      (chen1973Lemma6PrimePairShell x B k m)) :
    (eq20Product a : ℤ) ∈ Finset.Icc
      (((B * 2^k)^2 : ℕ) + 1 : ℤ) (((B * 2^k)^2 : ℕ) + (3 * (B * 2^k)^2 : ℕ) : ℤ) := by
  have hh := Finset.mem_product.mp ha
  have h1 := Finset.mem_Ioc.mp (chen1973Lemma6_eq19_dyadic_pair_product_mem hh.1)
  have h2 := Finset.mem_Ioc.mp (chen1973Lemma6_eq19_dyadic_pair_product_mem hh.2)
  have hlo : (B * 2^k)^2 < eq20Product a := by
    dsimp [eq20Product]
    nlinarith [Nat.mul_le_mul h1.1 h2.1]
  have hup : eq20Product a ≤ (B * 2^k)^2 + 3 * (B * 2^k)^2 := by
    dsimp [eq20Product]
    nlinarith [Nat.mul_le_mul h1.2 h2.2]
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hup

 theorem chen1973Lemma6_eq20_pair_square_eq_collected
    (x B k m : ℕ) (s : ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    (chen1973Lemma6Eq20PairPolynomial x B k m s χ)^2 =
      ∑ n ∈ Finset.Icc (((B * 2^k)^2 : ℕ) + 1 : ℤ)
        (((B * 2^k)^2 : ℕ) + (3 * (B * 2^k)^2 : ℕ) : ℤ),
        chen1973Lemma6Eq20PairSquareCoefficient x B k m s n * χ.1 (n : ZMod d) := by
  let S := chen1973Lemma6PrimePairShell x B k m
  have hid : chen1973Lemma6Eq20PairPolynomial x B k m s χ =
      ∑ p ∈ S, chen1973Lemma6Eq19PairAtom x s p * χ.1 ((p.1*p.2 : ℕ) : ZMod d) := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [chen1973Lemma6Eq19PairAtom]
    ring
  rw [hid, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product S S (fun a : Eq20Four =>
    (chen1973Lemma6Eq19PairAtom x s a.1 * χ.1 ((a.1.1*a.1.2 : ℕ) : ZMod d)) *
      (chen1973Lemma6Eq19PairAtom x s a.2 * χ.1 ((a.2.1*a.2.2 : ℕ) : ZMod d)))]
  symm
  unfold chen1973Lemma6Eq20PairSquareCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hn := eq20_product_interval ha
  rw [Finset.sum_eq_single (eq20Product a : ℤ)]
  · simp only [ite_true, Int.cast_natCast]
    rw [show (eq20Product a : ZMod d) =
      ((a.1.1*a.1.2 : ℕ) : ZMod d) * ((a.2.1*a.2.2 : ℕ) : ZMod d) by
        simp [eq20Product, Nat.cast_mul], map_mul]
    ring
  · intro n hn hne
    simp [Ne.symm hne]
  · exact fun h => (h hn).elim

 theorem chen1973Lemma6_eq20_pair_square_coefficient_energy
    (x B k m : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.Icc (((B * 2^k)^2 : ℕ) + 1 : ℤ)
        (((B * 2^k)^2 : ℕ) + (3 * (B * 2^k)^2 : ℕ) : ℤ),
      ‖chen1973Lemma6Eq20PairSquareCoefficient x B k m s n‖^2) ≤
      256 * (∑ p ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x s p‖^2)^2 := by
  let S := chen1973Lemma6PrimePairShell x B k m
  let A := fun a : Eq20Four =>
    chen1973Lemma6Eq19PairAtom x s a.1 * chen1973Lemma6Eq19PairAtom x s a.2
  have hpoint (n : ℤ) (hn : 0 ≤ n) :
      ‖chen1973Lemma6Eq20PairSquareCoefficient x B k m s n‖^2 ≤
        256 * ∑ a ∈ (S.product S).filter (fun a => (eq20Product a : ℤ) = n), ‖A a‖^2 := by
    let F := (S.product S).filter (fun a => (eq20Product a : ℤ) = n)
    have hcard : F.card ≤ 256 := by
      have hf : F = (S.product S).filter (fun a => eq20Product a = n.toNat) := by
        ext a
        simp only [F, Finset.mem_filter]
        constructor <;> rintro ⟨ha, heq⟩ <;> refine ⟨ha, ?_⟩
        · exact_mod_cast congrArg Int.toNat heq
        · exact_mod_cast (show (eq20Product a : ℤ) = n by omega)
      rw [hf]
      exact chen1973Lemma6_eq20_pair_square_fiber_card x B k m n.toNat
    have heq : chen1973Lemma6Eq20PairSquareCoefficient x B k m s n = ∑ a ∈ F, A a := by
      exact (Finset.sum_filter ..).symm
    rw [heq]
    calc
      _ ≤ (∑ a ∈ F, ‖A a‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (F.card : ℝ) * ∑ a ∈ F, ‖A a‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ 256 * ∑ a ∈ F, ‖A a‖^2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ Finset.Icc (((B * 2^k)^2 : ℕ) + 1 : ℤ)
        (((B * 2^k)^2 : ℕ) + (3 * (B * 2^k)^2 : ℕ) : ℤ),
        256 * ∑ a ∈ (S.product S).filter (fun a => (eq20Product a : ℤ) = n), ‖A a‖^2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply hpoint
      have hn1 := (Finset.mem_Icc.mp hn).1
      have hnn : (0 : ℤ) ≤ ((B * 2^k)^2 : ℕ) := by positivity
      omega
    _ = 256 * ∑ a ∈ S.product S, ‖A a‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (fun a ha => eq20_product_interval ha)]
    _ = _ := by
      apply congrArg (fun z : ℝ => 256*z)
      calc
        _ = ∑ a ∈ S, ∑ b ∈ S,
            ‖chen1973Lemma6Eq19PairAtom x s a‖^2 *
              ‖chen1973Lemma6Eq19PairAtom x s b‖^2 := by
          calc
            _ = ∑ a ∈ S.product S, ‖chen1973Lemma6Eq19PairAtom x s a.1‖^2 *
                ‖chen1973Lemma6Eq19PairAtom x s a.2‖^2 := by
              apply Finset.sum_congr rfl
              intro a ha
              dsimp [A]
              rw [norm_mul, mul_pow]
            _ = _ := Finset.sum_product S S (fun a =>
              ‖chen1973Lemma6Eq19PairAtom x s a.1‖^2 * ‖chen1973Lemma6Eq19PairAtom x s a.2‖^2)
        _ = _ := by
          rw [pow_two, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          rfl


/-- Sharp LS is re-applied on M=Y²,N=3Y², the true product support. -/
theorem chen1973Lemma6_eq20_pair_fourth_moment_fixed
    (x L level B k m D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq20PairFourthMoment x L level B k m s ≤
      chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((3 * (B * 2^k)^2 : ℕ) : ℝ) / D) *
          (256 * (∑ p ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x s p‖^2)^2)) := by
  have hLS := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6Eq20PairSquareCoefficient x B k m s)
      ((B * 2^k)^2 : ℕ) (3 * (B * 2^k)^2) D Q hD
  have hident (d : ℕ) (χ : PrimitiveCharacter d) :
      ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖^4 =
        ‖∑ n ∈ Finset.Icc (((B * 2^k)^2 : ℕ) + 1 : ℤ)
          (((B * 2^k)^2 : ℕ) + (3 * (B * 2^k)^2 : ℕ) : ℤ),
          chen1973Lemma6Eq20PairSquareCoefficient x B k m s n * χ.1 (n : ZMod d)‖^2 := by
    rw [← chen1973Lemma6_eq20_pair_square_eq_collected, norm_pow]
    ring
  have hE := chen1973Lemma6_eq20_pair_square_coefficient_energy x B k m s
  have hlin : (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖^4) ≤
        chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((3 * (B * 2^k)^2 : ℕ) : ℝ) / D) *
          (256 * (∑ p ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x s p‖^2)^2) := by
    simp_rw [hident]
    exact hLS.trans (mul_le_mul_of_nonneg_left hE
      (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le (by positivity)))
  unfold chen1973Lemma6Eq20PairFourthMoment
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖^4 :=
      chen1973Lemma6_eq19_weight_transport _ (fun d => by positivity)
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d, ‖chen1973Lemma6Eq20PairPolynomial x B k m s χ‖^4 := by
      apply mul_le_mul_of_nonneg_left _ (chen1973Lemma6Eq19I_pos x L level).le
      exact Finset.sum_le_sum_of_subset_of_nonneg hcell (fun d hd hnot => by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlin (chen1973Lemma6Eq19I_pos x L level).le

/-- Absolute-constant Eq20 pair fourth moment with the genuine Y² scale. -/
theorem chen1973Lemma6_eq20_pair_fourth_moment_scalar
    (x L level B k m D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (σ v : ℝ) (hσ : 1 / 2 ≤ σ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq20PairFourthMoment x L level B k m (σ + v * I) ≤
      62208 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
        Real.log x ^ 4 * ((Q : ℝ) + ((B * 2^k : ℕ) : ℝ)^2 / D) *
          ((B * 2^k : ℕ) : ℝ)^(2 - 4*σ) := by
  let Y : ℝ := (B * 2^k : ℕ)
  have hY : 0 < Y := by
    dsimp [Y]
    exact_mod_cast Nat.mul_pos hB (pow_pos (by omega) k)
  have hE := chen1973Lemma6_eq19_dyadic_pair_energy x B k m hx hB σ v hσ
  have hE2 : (∑ p ∈ chen1973Lemma6PrimePairShell x B k m,
      ‖chen1973Lemma6Eq19PairAtom x (σ + v*I) p‖^2)^2 ≤
        81 * Y^(2 - 4*σ) / Real.log x ^ 4 := by
    calc
      _ ≤ (9 * Y^(1-2*σ) / Real.log x ^ 2)^2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => sq_nonneg _) hE 2
      _ = _ := by
        have hp : (Y^(1-2*σ))^2 = Y^(2-4*σ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le]
          congr 1
          norm_num
          ring
        rw [div_pow, mul_pow, hp]
        ring
  have hscale : (Q : ℝ) + ((3 * (B * 2^k)^2 : ℕ) : ℝ) / D ≤
      3 * ((Q : ℝ) + Y^2 / D) := by
    dsimp [Y]
    push_cast
    rw [mul_div_assoc]
    nlinarith [Nat.cast_nonneg (α := ℝ) Q]
  have hfixed := chen1973Lemma6_eq20_pair_fourth_moment_fixed
    x L level B k m D Q (σ + v*I) hD hcell
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((3 * (B * 2^k)^2 : ℕ) : ℝ) / D) *
          (256 * (∑ p ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x (σ + v*I) p‖^2)^2)) := hfixed
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          (3 * ((Q : ℝ) + Y^2 / D)) *
          (256 * (81 * Y^(2 - 4*σ) / Real.log x ^ 4))) := by
      apply mul_le_mul_of_nonneg_left _ (chen1973Lemma6Eq19I_pos x L level).le
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hscale chen1973Lemma6_eq19SharpConstant_pos.le
      · exact mul_le_mul_of_nonneg_left hE2 (by norm_num)
      · positivity
      · exact mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le (by positivity)
    _ = _ := by dsimp [Y]; ring

/-- Explicit separated fourth roots, with the source-correct allocation. -/
theorem chen1973Lemma6B_le_eq20_three_roots
    (x L level B k m H : ℕ) (s : ℂ) :
    chen1973Lemma6B x L level B k m H s ≤
      Real.sqrt (chen1973Lemma6Eq20MobiusSecondMoment x L level H s) *
        Real.sqrt (Real.sqrt (chen1973Lemma6Eq20PairFourthMoment x L level B k m s)) *
        Real.sqrt (Real.sqrt (chen1973Lemma6Eq19LDerivFourthMoment x L level s)) := by
  have h := chen1973Lemma6B_le_eq20_moment_product x L level B k m H s
  rw [Real.sqrt_mul (Real.sqrt_nonneg _)] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h


/-- All three budgets are actual producers, applied on Chen's beta line.
The same finite cell weight W=Eq19I and conductor-height logarithm are retained. -/
theorem chen1973Lemma6B_eq20_beta_paid
    (x L level B k m H D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (hD : 0 < D) (hQ : 2 ≤ Q)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) (v : ℝ) :
    let β := chen1973Lemma6Beta x
    let r : ℝ := 1 / (2 * Real.log (x : ℝ))
    chen1973Lemma6B x L level B k m H (β + v * I) ≤
      Real.sqrt (chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level *
        ((Q : ℝ) + (H : ℝ) / D) * (1 + Real.log H)) *
      Real.sqrt (Real.sqrt
        (62208 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
          Real.log x ^ 4 * ((Q : ℝ) + ((B * 2^k : ℕ) : ℝ)^2 / D) *
            ((B * 2^k : ℕ) : ℝ)^(2 - 4*β))) *
      Real.sqrt (Real.sqrt (chen1973Lemma6Eq19I x L level *
        ((21000000 * (Q : ℝ)^2 * (|β| + |v| + r)^2 *
          (1 + Real.log ((Q : ℝ) * (1 + (|β| + |v| + r))))^4) / D / r^4))) := by
  dsimp only
  have hl : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hβ : 1 / 2 ≤ chen1973Lemma6Beta x := by
    unfold chen1973Lemma6Beta
    have hh : 0 ≤ (1 / Real.log (x : ℝ) : ℝ) := by positivity
    linarith
  have hS := chen1973Lemma6_eq20_mobius_second_moment x L level H D Q
    (chen1973Lemma6Beta x + v*I) (by simpa using hβ) hD hcell
  have hP := chen1973Lemma6_eq20_pair_fourth_moment_scalar x L level B k m D Q
    hx hB (chen1973Lemma6Beta x) v hβ hD hcell
  have hL := chen1973Lemma6_eq19_LDeriv_fourth_beta x L level D Q hx hD hQ hcell v
  apply (chen1973Lemma6B_le_eq20_three_roots x L level B k m H
    (chen1973Lemma6Beta x + v*I)).trans
  gcongr

end AnalyticNumberTheory.LargeSieve
