import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments
import Mathlib.Algebra.Order.Chebyshev

noncomputable section
open Classical Complex Finset
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve
open MathlibNt.SieveTheory.LiuWeight
set_option maxHeartbeats 1200000

private lemma eq14_mu_norm (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

private lemma eq14_atom (a b : ℕ) (s : ℂ) :
    (a : ℂ) ^ (-s) * (((ArithmeticFunction.moebius b : ℤ) : ℂ) / (b : ℂ) ^ s) =
      ((ArithmeticFunction.moebius b : ℤ) : ℂ) * ((a * b : ℕ) : ℂ) ^ (-s) := by
  have hp : (((a * b : ℕ) : ℂ) ^ (-s)) = (a : ℂ) ^ (-s) * (b : ℂ) ^ (-s) := by
    simpa using Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-s)
  rw [hp, Complex.cpow_neg (b : ℂ) s]
  ring

/-- Actual low-frequency cancellation, not a support assumption. -/
theorem chen1973Lemma6_CHWeightedCoefficient_eq_zero_of_le
    {H n : ℕ} (hn : 0 < n) (hnH : n ≤ H) (s : ℂ) :
    chen1973Lemma6CHWeightedCoefficient H s n = 0 := by
  have hf : (∑ ab ∈ chen1973PairFiber H n,
      ((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ)) =
      ∑ b ∈ n.divisors, ((ArithmeticFunction.moebius b : ℤ) : ℂ) := by
    apply Finset.sum_bij (fun ab _ => ab.2)
    · intro ab hab
      rw [chen1973PairFiber, Finset.mem_filter] at hab
      have hp : ab.1 * ab.2 = n := by exact_mod_cast hab.2
      exact Nat.mem_divisors.mpr ⟨⟨ab.1, by simpa [mul_comm] using hp.symm⟩, hn.ne'⟩
    · intro a ha b hb hab
      rw [chen1973PairFiber, Finset.mem_filter] at ha hb
      have ha2 := (Finset.mem_Icc.mp (Finset.mem_product.mp ha.1).2).1
      have hpa : a.1 * a.2 = n := by exact_mod_cast ha.2
      have hpb : b.1 * b.2 = n := by exact_mod_cast hb.2
      apply Prod.ext _ hab
      apply Nat.eq_of_mul_eq_mul_right (show 0 < a.2 by omega)
      simpa [← hab] using hpa.trans hpb.symm
    · intro b hb
      have hbd := (Nat.mem_divisors.mp hb).1
      have hbpos := Nat.pos_of_mem_divisors hb
      have hble := Nat.le_of_dvd hn hbd
      have hp := Nat.div_mul_cancel hbd
      refine ⟨(n / b, b), ?_, rfl⟩
      rw [chen1973PairFiber, Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.div_pos hble hbpos, (Nat.div_le_self _ _).trans hnH⟩,
        Finset.mem_Icc.mpr ⟨hbpos, hble.trans hnH⟩⟩, ?_⟩
      exact_mod_cast hp
    · intro ab hab
      rfl
  have hmu : (∑ b ∈ n.divisors, ((ArithmeticFunction.moebius b : ℤ) : ℂ)) =
      if n = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
    simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.one_apply] using h
  unfold chen1973Lemma6CHWeightedCoefficient chen1973Lemma6ProductCoefficient
  rw [← Finset.sum_filter]
  change (if (n : ℤ) = 1 then (1 : ℂ) else 0) -
    (∑ ab ∈ chen1973PairFiber H n, _) = 0
  have heq : (∑ ab ∈ chen1973PairFiber H n,
      (ab.1 : ℂ) ^ (-s) * (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) /
        (ab.2 : ℂ) ^ s)) =
      (∑ ab ∈ chen1973PairFiber H n, ((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ)) *
        (n : ℂ) ^ (-s) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    rw [eq14_atom]
    have hp : ab.1 * ab.2 = n := by
      exact_mod_cast (Finset.mem_filter.mp hab).2
    rw [hp]
  rw [heq, hf, hmu]
  by_cases hn1 : n = 1
  · subst n; simp
  · have hn1z : (n : ℤ) ≠ 1 := by exact_mod_cast hn1
    simp [hn1, hn1z]

/-- Retain the full reciprocal factor on Re(s) ≥ 1. -/
theorem chen1973Lemma6_CHWeightedCoefficient_norm_le_div
    {H : ℕ} (hH : 0 < H) {s : ℂ} {m : ℤ} (hs : 1 ≤ s.re)
    (hm : m ∈ Icc (1 : ℤ) (H * H : ℕ)) :
    ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ≤
      (m.toNat.divisors.card : ℝ) / (m.toNat : ℝ) := by
  by_cases hm1 : m = 1
  · subst m
    rw [show chen1973Lemma6CHWeightedCoefficient H s 1 = 0 from
      chen1973Lemma6_CHWeightedCoefficient_eq_zero_of_le (n := 1) (by omega) hH s]
    simp
  have hmposZ : 0 < m := lt_of_lt_of_le Int.zero_lt_one (mem_Icc.mp hm).1
  have hmpos : 0 < m.toNat := by omega
  have hmone : (1 : ℝ) ≤ m.toNat := by exact_mod_cast hmpos
  unfold chen1973Lemma6CHWeightedCoefficient
  rw [if_neg hm1, zero_sub, norm_neg]
  unfold chen1973Lemma6ProductCoefficient
  rw [← Finset.sum_filter]
  calc
    ‖∑ ab ∈ chen1973PairFiber H m, _‖ ≤ ∑ ab ∈ chen1973PairFiber H m,
        ‖(ab.1 : ℂ) ^ (-s) *
          (((ArithmeticFunction.moebius ab.2 : ℤ) : ℂ) / (ab.2 : ℂ) ^ s)‖ :=
      norm_sum_le _ _
    _ ≤ (chen1973PairFiber H m).card • ((m.toNat : ℝ)⁻¹) := by
      apply Finset.sum_le_card_nsmul
      intro ab hab
      have hp : ab.1 * ab.2 = m.toNat := by
        have hmn : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hmposZ.le
        exact_mod_cast (Finset.mem_filter.mp hab).2.trans hmn.symm
      rw [eq14_atom, hp, norm_mul]
      have hnorm : ‖(m.toNat : ℂ) ^ (-s)‖ = (m.toNat : ℝ) ^ (-s.re) := by
        simpa using Complex.norm_cpow_eq_rpow_re_of_pos
          (show (0 : ℝ) < m.toNat by exact_mod_cast hmpos) (-s)
      rw [hnorm]
      calc
        _ ≤ 1 * (m.toNat : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (eq14_mu_norm _) (by positivity)
        _ ≤ (m.toNat : ℝ)⁻¹ := by
          rw [one_mul, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hmone (by linarith)
    _ ≤ (m.toNat.divisors.card : ℝ) / (m.toNat : ℝ) := by
      simp only [nsmul_eq_mul, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast chen1973PairFiber_card_le_divisors hm) (by positivity)

/-- Weighted energy is exactly the harmonic divisor-square scale. -/
theorem chen1973Lemma6_CHWeightedCoefficient_weighted_energy
    (H : ℕ) (hH : 0 < H) (s : ℂ) (hs : 1 ≤ s.re) :
    (∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
      (m.toNat : ℝ) * ‖chen1973Lemma6CHWeightedCoefficient H s m‖ ^ 2) ≤
      (1 + Real.log (H * H : ℕ)) ^ 4 := by
  calc
    _ ≤ ∑ m ∈ Icc (1 : ℤ) (H * H : ℕ),
        ((m.toNat.divisors.card : ℝ) ^ 2) * (m.toNat : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      have hn : (0 : ℝ) < m.toNat := by
        have := (Finset.mem_Icc.mp hm).1
        exact_mod_cast (show 0 < m.toNat by omega)
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (chen1973Lemma6_CHWeightedCoefficient_norm_le_div hH hs hm) 2
      have hh := mul_le_mul_of_nonneg_left h hn.le
      convert hh using 1
      field_simp
    _ = ∑ n ∈ Icc 1 (H * H), ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹ := by
      exact sum_Icc_int_toNat_eq_sum_Icc
        (F := fun n => ((n.divisors.card : ℝ) ^ 2) * (n : ℝ)⁻¹) (H * H)
    _ ≤ liuHarmonic (H * H) ^ 4 := divisorSquareWeightedPrefix_le_fourth_harmonic _
    _ ≤ (1 + Real.log (H * H : ℕ)) ^ 4 :=
      pow_le_pow_left₀ (by unfold liuHarmonic; positivity)
        (liuHarmonic_le_one_add_log _) 4

/-- Dyadic integer intervals use their actual length H*2^j. -/
def eq14DyadicShell (H j : ℕ) : Finset ℤ :=
  Ioc (H * 2 ^ j : ℕ) (H * 2 ^ (j + 1) : ℕ)

private lemma eq14_sum_Ioc_split {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Ioc a b, f n) + (∑ n ∈ Ioc b c, f n) = ∑ n ∈ Ioc a c, f n := by
  have hd : Disjoint (Ioc a b) (Ioc b c) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  rw [← Finset.sum_union hd]
  congr 1
  ext n
  simp only [Finset.mem_union, Finset.mem_Ioc]
  omega

/-- Exact disjoint shell recombination, valid for any finite additive sum. -/
theorem eq14_sum_dyadicShell {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (H K : ℕ) :
    (∑ j ∈ range K, ∑ n ∈ eq14DyadicShell H j, f n) =
      ∑ n ∈ Ioc (H : ℤ) (H * 2 ^ K : ℕ), f n := by
  induction K with
  | zero => simp [eq14DyadicShell]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    unfold eq14DyadicShell
    apply eq14_sum_Ioc_split
    · exact_mod_cast Nat.le_mul_of_pos_right H (by positivity : 0 < 2 ^ K)
    · exact_mod_cast Nat.mul_le_mul_left H
        (show 2 ^ K ≤ 2 ^ (K + 1) by rw [pow_succ]; omega)

private lemma eq14_sum_truncate {A : Type*} [AddCommMonoid A]
    (f : ℤ → A) (H X T : ℕ) (_hHX : H ≤ X) (hXT : X ≤ T)
    (hlow : ∀ n ∈ Icc (1 : ℤ) H, f n = 0) :
    (∑ n ∈ Ioc (H : ℤ) T, if n ≤ (X : ℤ) then f n else 0) =
      ∑ n ∈ Icc (1 : ℤ) X, f n := by
  calc
    _ = ∑ n ∈ Ioc (H : ℤ) X, f n := by
      symm
      calc
        _ = ∑ n ∈ Ioc (H : ℤ) X, if n ≤ (X : ℤ) then f n else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (Finset.mem_Ioc.mp hn).2]
        _ = _ := by
          apply Finset.sum_subset
          · intro n hn
            simp only [Finset.mem_Ioc] at hn ⊢
            exact ⟨hn.1, hn.2.trans (by exact_mod_cast hXT)⟩
          · intro n hn hnX
            have : ¬n ≤ (X : ℤ) := by
              simp only [Finset.mem_Ioc] at hn hnX
              omega
            simp [this]
    _ = _ := by
      apply Finset.sum_subset
      · intro n hn
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
        constructor <;> omega
      · intro n hn hnH
        apply hlow
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn hnH ⊢
        omega

private lemma eq14_norm_sum_sq {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S f) 2).trans
    (sq_sum_le_card_mul_sum_sq)

/-- Sharp LS is freshly applied to each shell; its length is H*2^j,
not H². The upper bound pays the shell's own weighted energy. -/
theorem eq14_dyadicShell_moment (c : ℤ → ℂ) (H j D Q : ℕ)
    (hH : 0 < H) (hD : 0 < D) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ n ∈ eq14DyadicShell H j, c n * χ.1 (n : ZMod d)‖ ^ 2) ≤
      chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) / H + 1 / D) *
        ∑ n ∈ eq14DyadicShell H j, (n.toNat : ℝ) * ‖c n‖ ^ 2 := by
  let Y : ℕ := H * 2 ^ j
  have hHY : H ≤ Y := Nat.le_mul_of_pos_right H (by positivity)
  have hY : 0 < Y := lt_of_lt_of_le hH hHY
  have hset : eq14DyadicShell H j = Icc ((Y : ℤ) + 1) ((Y : ℤ) + Y) := by
    rw [Finset.Icc_add_one_left_eq_Ioc]
    unfold eq14DyadicShell
    congr 1
    simp only [Y, pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hls := chen1973Lemma2_equationThree_complex_fixed c Y Y D Q hD
  rw [← hset] at hls
  refine hls.trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnY : Y < n.toNat := by
    have h := (Finset.mem_Ioc.mp hn).1
    change (Y : ℤ) < n at h
    omega
  have hnH : H ≤ n.toNat := hHY.trans hnY.le
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hQr : (0 : ℝ) ≤ Q := by positivity
  have h1 : (Q : ℝ) ≤ ((Q : ℝ) / H) * n.toNat := by
    have he : (Q : ℝ) = ((Q : ℝ) / H) * H := by field_simp
    calc
      (Q : ℝ) = ((Q : ℝ) / H) * H := he
      _ ≤ ((Q : ℝ) / H) * n.toNat :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hnH) (by positivity)
  have h2 : (Y : ℝ) / D ≤ (1 / (D : ℝ)) * n.toNat := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnY.le) hDr.le
  have hfac : (Q : ℝ) + Y / D ≤ ((Q : ℝ) / H + 1 / D) * n.toNat := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hfac (sq_nonneg ‖c n‖))
    chen1973Lemma6_eq19SharpConstant_pos.le
  simpa only [mul_assoc] using hh

/-- A tail-supported finite polynomial: Cauchy costs one shell count,
while disjoint weighted energies are summed without a second loss. -/
theorem eq14_tail_polynomial_moment (c : ℤ → ℂ) (H X K D Q : ℕ)
    (hH : 0 < H) (hD : 0 < D) (hHX : H ≤ X) (hXK : X ≤ H * 2 ^ K)
    (hlow : ∀ n ∈ Icc (1 : ℤ) H, c n = 0) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ n ∈ Icc (1 : ℤ) X, c n * χ.1 (n : ZMod d)‖ ^ 2) ≤
      (K : ℝ) * chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) / H + 1 / D) *
        ∑ n ∈ Icc (1 : ℤ) X, (n.toNat : ℝ) * ‖c n‖ ^ 2 := by
  let b : ℤ → ℂ := fun n => if n ≤ (X : ℤ) then c n else 0
  let F : ℕ → (d : ℕ) → PrimitiveCharacter d → ℂ := fun j d χ =>
    ∑ n ∈ eq14DyadicShell H j, b n * χ.1 (n : ZMod d)
  have hid (d : ℕ) (χ : PrimitiveCharacter d) :
      (∑ n ∈ Icc (1 : ℤ) X, c n * χ.1 (n : ZMod d)) =
        ∑ j ∈ range K, F j d χ := by
    dsimp [F]
    rw [eq14_sum_dyadicShell]
    symm
    have ht := eq14_sum_truncate (fun n => c n * χ.1 (n : ZMod d)) H X
      (H * 2 ^ K) hHX hXK (by intro n hn; rw [hlow n hn, zero_mul])
    simpa only [b, ite_mul, zero_mul] using ht
  have henergy :
      (∑ j ∈ range K, ∑ n ∈ eq14DyadicShell H j, (n.toNat : ℝ) * ‖b n‖ ^ 2) =
        ∑ n ∈ Icc (1 : ℤ) X, (n.toNat : ℝ) * ‖c n‖ ^ 2 := by
    rw [eq14_sum_dyadicShell]
    have ht := eq14_sum_truncate (fun n => (n.toNat : ℝ) * ‖c n‖ ^ 2) H X
      (H * 2 ^ K) hHX hXK (by intro n hn; simp [hlow n hn])
    convert ht using 1
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [b]
    split_ifs <;> simp
  have hswap :
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d, (K : ℝ) * ∑ j ∈ range K, ‖F j d χ‖ ^ 2) =
      (K : ℝ) * ∑ j ∈ range K, ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d, ‖F j d χ‖ ^ 2 := by
    simp only [Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext d
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  calc
    _ ≤ ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d, (K : ℝ) * ∑ j ∈ range K, ‖F j d χ‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro χ hχ
      rw [hid]
      simpa using eq14_norm_sum_sq (range K) (fun j => F j d χ)
    _ = _ := hswap
    _ ≤ (K : ℝ) * ∑ j ∈ range K,
        chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) / H + 1 / D) *
          ∑ n ∈ eq14DyadicShell H j, (n.toNat : ℝ) * ‖b n‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      exact eq14_dyadicShell_moment b H j D Q hH hD
    _ = _ := by rw [← Finset.mul_sum, henergy]; ring

/-- The CH polynomial bound with its literal logarithmic dyadic count. -/
theorem chen1973Lemma6_CH_polynomial_moment_dyadic
    (H D Q : ℕ) (s : ℂ) (hH : 0 < H) (hD : 0 < D) (hs : 1 ≤ s.re) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ n ∈ Icc (1 : ℤ) (H * H : ℕ),
          chen1973Lemma6CHWeightedCoefficient H s n * χ.1 (n : ZMod d)‖ ^ 2) ≤
      ((Nat.log 2 H + 1 : ℕ) : ℝ) * chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) / H + 1 / D) * (1 + Real.log (H * H : ℕ)) ^ 4 := by
  have ht := eq14_tail_polynomial_moment (chen1973Lemma6CHWeightedCoefficient H s)
    H (H * H) (Nat.log 2 H + 1) D Q hH hD
    (Nat.le_mul_of_pos_right H hH)
    (Nat.mul_le_mul_left H (Nat.lt_pow_succ_log_self (by norm_num) H).le)
    (by
      intro n hn
      have hn0 : 0 < n.toNat := by have := (Finset.mem_Icc.mp hn).1; omega
      have hnH : n.toNat ≤ H := by have := (Finset.mem_Icc.mp hn).2; omega
      have he : (n.toNat : ℤ) = n := by have := (Finset.mem_Icc.mp hn).1; omega
      rw [← he]
      exact chen1973Lemma6_CHWeightedCoefficient_eq_zero_of_le hn0 hnH s)
  refine ht.trans (mul_le_mul_of_nonneg_left
    (chen1973Lemma6_CHWeightedCoefficient_weighted_energy H hH s hs) ?_)
  exact mul_nonneg (mul_nonneg (by positivity) chen1973Lemma6_eq19SharpConstant_pos.le)
    (by positivity)

/-- Absolute constant fixed before H,D,Q and the complete complex parameter. -/
def chen1973Lemma6Eq14DyadicConstant : ℝ :=
  16 * (1 + 1 / Real.log 2) * chen1973Lemma6Eq19SharpConstant

lemma chen1973Lemma6Eq14DyadicConstant_pos : 0 < chen1973Lemma6Eq14DyadicConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold chen1973Lemma6Eq14DyadicConstant
  exact mul_pos (by positivity) chen1973Lemma6_eq19SharpConstant_pos

private lemma eq14_dyadic_count_log (H : ℕ) (hH : 0 < H) :
    ((Nat.log 2 H + 1 : ℕ) : ℝ) ≤
      (1 + 1 / Real.log 2) * (1 + Real.log (H + 1 : ℕ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2 : ℝ) ^ Nat.log 2 H ≤ (H : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hH.ne'
  have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 H) hp
  rw [Real.log_pow] at hl
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hsucc : Real.log (H : ℝ) ≤ Real.log (H + 1 : ℕ) :=
    Real.log_le_log hHpos (by exact_mod_cast Nat.le_succ H)
  have hk : (Nat.log 2 H : ℝ) ≤ Real.log (H + 1 : ℕ) / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    linarith
  have hl0 : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg (by norm_cast; omega)
  have hi0 : 0 ≤ 1 / Real.log 2 := by positivity
  simp only [Nat.cast_add, Nat.cast_one] at hk hl0 ⊢
  rw [div_eq_mul_inv] at hk
  simp only [one_div] at hi0 ⊢
  nlinarith

private lemma eq14_log_four (H : ℕ) (hH : 0 < H) :
    (1 + Real.log (H * H : ℕ)) ^ 4 ≤ 16 * (1 + Real.log (H + 1 : ℕ)) ^ 4 := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have he : Real.log (H * H : ℕ) = 2 * Real.log H := by
    rw [Nat.cast_mul, Real.log_mul hHr.ne' hHr.ne']
    ring
  have hmon : Real.log (H : ℝ) ≤ Real.log (H + 1 : ℕ) :=
    Real.log_le_log hHr (by exact_mod_cast Nat.le_succ H)
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hh : 0 ≤ 1 + Real.log (H * H : ℕ) := by rw [he]; linarith
  have hbase : 1 + Real.log (H * H : ℕ) ≤ 2 * (1 + Real.log (H + 1 : ℕ)) := by
    rw [he]; linarith
  simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using
    pow_le_pow_left₀ hh hbase 4

/-- The genuine finite polynomial term of (14), on every vertical line
Re(s) ≥ 1. The fifth logarithm is the dyadic Cauchy cost; four logarithms
come from the globally recombined harmonic divisor-square energy.
This theorem does not assert the full printed equation (14): its L-function
truncation remainder is deliberately absent. -/
theorem chen1973Lemma6_CH_polynomial_moment_fixed_log_five
    (H D Q : ℕ) (s : ℂ) (hH : 2 ≤ H) (hD : 0 < D) (hs : 1 ≤ s.re) :
    (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
      ∑ χ : PrimitiveCharacter d,
        ‖∑ n ∈ Icc (1 : ℤ) (H * H : ℕ),
          chen1973Lemma6CHWeightedCoefficient H s n * χ.1 (n : ZMod d)‖ ^ 2) ≤
      chen1973Lemma6Eq14DyadicConstant * ((Q : ℝ) / H + 1 / D) *
        (1 + Real.log (H + 1 : ℕ)) ^ 5 := by
  have hHpos : 0 < H := by omega
  have hK := eq14_dyadic_count_log H hHpos
  have hE := eq14_log_four H hHpos
  have hC := chen1973Lemma6_eq19SharpConstant_pos.le
  have hA : 0 ≤ (Q : ℝ) / H + 1 / D := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ 1 + Real.log (H + 1 : ℕ) := by
    have : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg (by norm_cast; omega)
    linarith
  calc
    _ ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) * chen1973Lemma6Eq19SharpConstant *
        ((Q : ℝ) / H + 1 / D) * (1 + Real.log (H * H : ℕ)) ^ 4 :=
      chen1973Lemma6_CH_polynomial_moment_dyadic H D Q s hHpos hD hs
    _ ≤ ((1 + 1 / Real.log 2) * (1 + Real.log (H + 1 : ℕ))) *
        chen1973Lemma6Eq19SharpConstant * ((Q : ℝ) / H + 1 / D) *
          (16 * (1 + Real.log (H + 1 : ℕ)) ^ 4) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hC) hA
      · exact hE
      · positivity
      · exact mul_nonneg (mul_nonneg (by positivity) hC) hA
    _ = _ := by unfold chen1973Lemma6Eq14DyadicConstant; ring

/-- Explicit binder order: one absolute C works for every finite CH polynomial
and all imaginary parts of s, with no conductor-order assumption. -/
theorem chen1973Lemma6_CH_polynomial_moment_exists_absolute :
    ∃ C : ℝ, 0 < C ∧ ∀ (H D Q : ℕ) (s : ℂ),
      2 ≤ H → 0 < D → 1 ≤ s.re →
      (∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter d,
          ‖∑ n ∈ Icc (1 : ℤ) (H * H : ℕ),
            chen1973Lemma6CHWeightedCoefficient H s n * χ.1 (n : ZMod d)‖ ^ 2) ≤
        C * ((Q : ℝ) / H + 1 / D) * (1 + Real.log (H + 1 : ℕ)) ^ 5 := by
  exact ⟨chen1973Lemma6Eq14DyadicConstant, chen1973Lemma6Eq14DyadicConstant_pos,
    chen1973Lemma6_CH_polynomial_moment_fixed_log_five⟩


end AnalyticNumberTheory.LargeSieve
