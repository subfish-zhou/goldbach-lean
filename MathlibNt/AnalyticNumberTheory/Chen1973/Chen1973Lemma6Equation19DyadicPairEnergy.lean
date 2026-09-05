import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19UniformMoments
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19SourceParameters
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21UniformVerticalEstimate

/-! Actual pair-shell energy and sharp primitive large sieve on its true dyadic interval.
The weight remains the public `chen1973Lemma6Eq19I`; no printed exponential bridge
is asserted here. -/
noncomputable section
set_option maxHeartbeats 1200000
open Classical Complex Finset Set
open scoped BigOperators ArithmeticFunction
namespace AnalyticNumberTheory.LargeSieve

/-- The actual shell, without a source-parameter premise, maps into `(Y,2Y]`. -/
theorem chen1973Lemma6_eq19_dyadic_pair_product_mem
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    pp.1 * pp.2 ∈ Finset.Ioc (B * 2 ^ k) (2 * (B * 2 ^ k)) := by
  simp only [chen1973Lemma6PrimePairShell, chen1973Lemma6DyadicShell,
    Finset.mem_filter] at hpp
  apply Finset.mem_Ioc.mpr
  exact ⟨hpp.2.1, by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    using hpp.2.2⟩

/-- Injectivity of ordered prime products gives at most `Y` pairs, not `x²`. -/
theorem chen1973Lemma6_eq19_dyadic_pair_card (x B k m : ℕ) :
    (chen1973Lemma6PrimePairShell x B k m).card ≤ B * 2 ^ k := by
  have h := Finset.card_le_card_of_injOn (fun pp : ℕ × ℕ => pp.1 * pp.2)
    (fun pp hpp => chen1973Lemma6_eq19_dyadic_pair_product_mem hpp)
    (chen1973Lemma6_eq19_pair_product_injective x B k m)
  have h' : (chen1973Lemma6PrimePairShell x B k m).card ≤
      2 * (B * 2 ^ k) - B * 2 ^ k := by simpa using h
  omega

/-- Pointwise norm bound; the logarithmic lower bound is derived from the actual
prime-pair carrier, rather than assumed as an extra region hypothesis. -/
theorem chen1973Lemma6_eq19_dyadic_pair_atom_sq_le
    {x B k m : ℕ} (hx : 3 ≤ x) (hB : 0 < B)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) (v : ℝ) {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ ^ 2 ≤
      9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) / Real.log x ^ 2 := by
  have hY : (0 : ℝ) < (B * 2 ^ k : ℕ) := by exact_mod_cast
    (Nat.mul_pos hB (pow_pos (by omega) k))
  have hp := (Finset.mem_Ioc.mp (chen1973Lemma6_eq19_dyadic_pair_product_mem hpp)).1
  have hprod : (0 : ℝ) < (pp.1 : ℝ) * pp.2 := by
    have : (B * 2 ^ k : ℕ) < pp.1 * pp.2 := hp
    have hr : ((B * 2 ^ k : ℕ) : ℝ) < (pp.1 : ℝ) * pp.2 := by exact_mod_cast this
    exact hY.trans hr
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  obtain ⟨hy, hlogy⟩ := chen1973Lemma6_eq21_primeRegion_log_y hx
    (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m hpp)
  have hlogy0 := Real.log_pos hy
  have hn : ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ ^ 2 =
      ((pp.1 : ℝ) * pp.2) ^ (-2 * σ) /
        Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ 2 := by
    unfold chen1973Lemma6Eq19PairAtom
    rw [norm_div, norm_one, norm_mul]
    rw [show (pp.1 * pp.2 : ℂ) = (((pp.1 : ℝ) * pp.2 : ℝ) : ℂ) by push_cast; rfl]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hprod]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogy0]
    rw [div_pow, mul_pow, one_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul hprod.le]
    norm_num only [Nat.cast_ofNat]
    rw [show -2 * σ = -(σ * (2 : ℝ)) by ring, Real.rpow_neg hprod.le]
    ring
  rw [hn]
  have hpow : ((pp.1 : ℝ) * pp.2) ^ (-2 * σ) ≤
      ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) := by
    apply Real.rpow_le_rpow_of_nonpos hY
    · exact_mod_cast hp.le
    · linarith
  have hden : Real.log x ^ 2 ≤ 9 * Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ 2 := by
    nlinarith
  apply (div_le_div_iff₀ (sq_pos_of_pos hlogy0) (sq_pos_of_pos hlog)).mpr
  calc
    _ ≤ ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) * Real.log x ^ 2 :=
      mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ ≤ ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) *
        (9 * Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)) ^ 2) :=
      mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

/-- Uniform dyadic energy bound for Chen's literal pair shell. -/
theorem chen1973Lemma6_eq19_dyadic_pair_energy
    (x B k m : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (σ v : ℝ) (hσ : 1 / 2 ≤ σ) :
    (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ ^ 2) ≤
      9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (1 - 2 * σ) / Real.log x ^ 2 := by
  have hY : (0 : ℝ) < (B * 2 ^ k : ℕ) := by exact_mod_cast
    (Nat.mul_pos hB (pow_pos (by omega) k))
  calc
    _ ≤ ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) / Real.log x ^ 2 := by
      exact Finset.sum_le_sum fun pp hpp =>
        chen1973Lemma6_eq19_dyadic_pair_atom_sq_le hx hB hσ v hpp
    _ = (chen1973Lemma6PrimePairShell x B k m).card *
        (9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) / Real.log x ^ 2) := by simp
    _ ≤ ((B * 2 ^ k : ℕ) : ℝ) *
        (9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (-2 * σ) / Real.log x ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast chen1973Lemma6_eq19_dyadic_pair_card x B k m
      · positivity
    _ = _ := by
      rw [show 1 - 2 * σ = 1 + (-2 * σ) by ring, Real.rpow_add hY, Real.rpow_one]
      ring

private lemma dyadic_norm_collected_sq_eq_fiber_energy
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (g : ι → κ) (a : ι → ℂ)
    (hg : Set.InjOn g (S : Set ι)) (y : κ) :
    ‖∑ i ∈ S, if g i = y then a i else 0‖ ^ 2 =
      ∑ i ∈ S with g i = y, ‖a i‖ ^ 2 := by
  let T := S.filter fun i => g i = y
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro i j hi hj
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    exact hg hi'.1 hj'.1 (hi'.2.trans hj'.2.symm)
  rw [← Finset.sum_filter]
  change ‖∑ i ∈ T, a i‖ ^ 2 = ∑ i ∈ T, ‖a i‖ ^ 2
  by_cases hT : T = ∅
  · rw [hT]
    simp
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hsingle : T = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi, ?_⟩
      intro j hj
      exact (Finset.card_le_one.mp hcard) j hj i hi
    rw [hsingle]
    simp

private lemma dyadic_pair_product_mem_int
    {x B k m : ℕ} {pp : ℕ × ℕ}
    (hpp : pp ∈ chen1973Lemma6PrimePairShell x B k m) :
    (pp.1 * pp.2 : ℤ) ∈ Finset.Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)) := by
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp
    (chen1973Lemma6_eq19_dyadic_pair_product_mem hpp)
  apply Finset.mem_Icc.mpr
  constructor
  · have : B * 2 ^ k + 1 ≤ pp.1 * pp.2 := hl
    exact_mod_cast this
  · have : pp.1 * pp.2 ≤ B * 2 ^ k + B * 2 ^ k := by omega
    exact_mod_cast this

theorem chen1973Lemma6_eq19_dyadic_pairPolynomial_eq_collected
    (x B k m : ℕ) (s : ℂ) {d : ℕ} (χ : PrimitiveCharacter d) :
    (∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
      χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
        ((pp.1 * pp.2 : ℂ) ^ s *
          Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))) =
      ∑ n ∈ Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)),
        chen1973Lemma6Eq19PairCoefficient x B k m s n * χ.1 (n : ZMod d) := by
  unfold chen1973Lemma6Eq19PairCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pp hpp
  let n : ℤ := pp.1 * pp.2
  have hn := dyadic_pair_product_mem_int hpp
  rw [Finset.sum_eq_single n]
  · simp [n]
    ring
  · intro z hz hzne
    have hne : (pp.1 * pp.2 : ℤ) ≠ z := by
      simpa [n] using hzne.symm
    simp [hne]
  · exact fun h => False.elim (h hn)

theorem chen1973Lemma6_eq19_dyadic_pairCoefficient_square_energy
    (x B k m : ℕ) (s : ℂ) :
    (∑ n ∈ Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)),
      ‖chen1973Lemma6Eq19PairCoefficient x B k m s n‖ ^ 2) =
      ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
        ‖chen1973Lemma6Eq19PairAtom x s pp‖ ^ 2 := by
  let S := chen1973Lemma6PrimePairShell x B k m
  let g : ℕ × ℕ → ℤ := fun pp => pp.1 * pp.2
  have hg : Set.InjOn g (S : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact chen1973Lemma6_eq19_pair_product_injective x B k m ha hb
      (by
        change (a.1 * a.2 : ℤ) = b.1 * b.2 at hab
        exact_mod_cast hab)
  have hmap : ∀ pp ∈ S, g pp ∈ Finset.Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)) := by
    intro pp hpp
    exact dyadic_pair_product_mem_int hpp
  unfold chen1973Lemma6Eq19PairCoefficient
  change (∑ n ∈ Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)),
      ‖∑ pp ∈ S, if g pp = n then chen1973Lemma6Eq19PairAtom x s pp else 0‖ ^ 2) = _
  simp_rw [dyadic_norm_collected_sq_eq_fiber_energy S g (chen1973Lemma6Eq19PairAtom x s) hg]
  rw [Finset.sum_fiberwise_of_maps_to hmap]

theorem chen1973Lemma6_eq19_dyadic_pair_second_moment_fixed
    (x L level B k m D Q : ℕ) (s : ℂ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19PairSecondMoment x L level B k m s ≤
      chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x s pp‖ ^ 2) := by
  have hLS := chen1973Lemma2_equationThree_complex_fixed
    (chen1973Lemma6Eq19PairCoefficient x B k m s) (B * 2 ^ k : ℕ) (B * 2 ^ k) D Q hD
  have hnon : ∀ d : ℕ, 0 ≤
      ∑ χ : PrimitiveCharacter d,
        ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
            ((pp.1 * pp.2 : ℂ) ^ s *
              Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 :=
    fun d => Finset.sum_nonneg fun χ hχ => sq_nonneg _
  unfold chen1973Lemma6Eq19PairSecondMoment
  change (∑ d ∈ chen1973Lemma6ConductorBlock x L level,
      chen1973Lemma6Eq19Weight d * _) ≤ _
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ chen1973Lemma6ConductorBlock x L level,
          (1 / (d.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter d,
              ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
                χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
                  ((pp.1 * pp.2 : ℂ) ^ s *
                    Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 :=
      chen1973Lemma6_eq19_weight_transport _ hnon
    _ ≤ chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
              χ.1 ((pp.1 * pp.2 : ℕ) : ZMod d) /
                ((pp.1 * pp.2 : ℂ) ^ s *
                  Real.log ((x : ℝ) / ((pp.1 : ℝ) * pp.2)))‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg hcell
        intro d hd hdnot
        positivity
      · exact (chen1973Lemma6Eq19I_pos x L level).le
    _ = chen1973Lemma6Eq19I x L level *
        ∑ d ∈ Ioc D Q, (1 / (d.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter d,
            ‖∑ n ∈ Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)),
              chen1973Lemma6Eq19PairCoefficient x B k m s n *
                χ.1 (n : ZMod d)‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [← chen1973Lemma6_eq19_dyadic_pairPolynomial_eq_collected]
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          ∑ n ∈ Icc (((B * 2 ^ k : ℕ) : ℤ) + 1) (((B * 2 ^ k : ℕ) : ℤ) + (B * 2 ^ k : ℕ)),
            ‖chen1973Lemma6Eq19PairCoefficient x B k m s n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [Int.zero_add] using hLS)
        (chen1973Lemma6Eq19I_pos x L level).le
    _ = _ := by rw [chen1973Lemma6_eq19_dyadic_pairCoefficient_square_energy]

/-- Dyadic primitive-LS payment of the original pair second moment.  Sharp
Lemma 2 is applied with `M = Y` and `N = Y`, and its fixed absolute constant
is independent of every cell and vertical height. -/
theorem chen1973Lemma6_eq19_dyadic_pair_second_moment_scalar
    (x L level B k m D Q : ℕ) (hx : 3 ≤ x) (hB : 0 < B)
    (σ v : ℝ) (hσ : 1 / 2 ≤ σ) (hD : 0 < D)
    (hcell : chen1973Lemma6ConductorBlock x L level ⊆ Ioc D Q) :
    chen1973Lemma6Eq19PairSecondMoment x L level B k m (σ + v * I) ≤
      9 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
        Real.log x ^ 2 * ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          ((B * 2 ^ k : ℕ) : ℝ) ^ (1 - 2 * σ) := by
  have h := chen1973Lemma6_eq19_dyadic_pair_second_moment_fixed
    x L level B k m D Q (σ + v * I) hD hcell
  have hE := chen1973Lemma6_eq19_dyadic_pair_energy x B k m hx hB σ v hσ
  calc
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          ∑ pp ∈ chen1973Lemma6PrimePairShell x B k m,
            ‖chen1973Lemma6Eq19PairAtom x (σ + v * I) pp‖ ^ 2) := h
    _ ≤ chen1973Lemma6Eq19I x L level *
        (chen1973Lemma6Eq19SharpConstant *
          ((Q : ℝ) + ((B * 2 ^ k : ℕ) : ℝ) / D) *
          (9 * ((B * 2 ^ k : ℕ) : ℝ) ^ (1 - 2 * σ) / Real.log x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (chen1973Lemma6Eq19I_pos x L level).le
      exact mul_le_mul_of_nonneg_left hE
        (mul_nonneg chen1973Lemma6_eq19SharpConstant_pos.le (by positivity))
    _ = _ := by ring

/-- Literal positive-level source-cell specialization.  The interval containment
is derived from the real source packet; `Eq19I` is not replaced by an unproved
printed exponential expression. -/
theorem chen1973Lemma6_eq19_dyadic_pair_second_moment_source
    {x L B lastD level k : ℕ}
    (P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k)
    (m : ℕ) (σ v : ℝ) (hσ : 1 / 2 ≤ σ) :
    chen1973Lemma6Eq19PairSecondMoment x L level B k m (σ + v * I) ≤
      9 * chen1973Lemma6Eq19SharpConstant * chen1973Lemma6Eq19I x L level /
        Real.log x ^ 2 *
        ((chen1973Lemma6Eq19SourceQ L level : ℝ) +
          (chen1973Lemma6Eq19PairD B k : ℝ) / chen1973Lemma6Eq19SourceD L level) *
        (chen1973Lemma6Eq19PairD B k : ℝ) ^ (1 - 2 * σ) := by
  exact chen1973Lemma6_eq19_dyadic_pair_second_moment_scalar
    x L level B k m (chen1973Lemma6Eq19SourceD L level)
    (chen1973Lemma6Eq19SourceQ L level) P.hx P.hB σ v hσ
    (chen1973Lemma6Eq19SourceD_pos P)
    (chen1973Lemma6_eq19_conductorBlock_subset_source_Ioc P)

end AnalyticNumberTheory.LargeSieve
