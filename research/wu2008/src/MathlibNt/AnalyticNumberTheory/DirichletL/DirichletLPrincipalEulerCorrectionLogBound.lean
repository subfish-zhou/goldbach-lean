import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLWeakStripValueBound

open Complex Finset

namespace DirichletCharacter

private lemma primeSubsetProduct_injective (q : ℕ) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) q.primeFactors.powerset := by
  have subset_of_prod_eq : ∀ t ∈ q.primeFactors.powerset,
      ∀ u ∈ q.primeFactors.powerset, (∏ p ∈ t, p) = (∏ p ∈ u, p) → t ⊆ u := by
    intro t ht u hu htu p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    have hpd : p ∣ ∏ a ∈ u, a := htu ▸ Finset.dvd_prod_of_mem id hp
    obtain ⟨a, ha, hpa⟩ := (Prime.dvd_finsetProd_iff hpp.prime id).mp hpd
    have hap : a.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hu ha)
    have : p = a := (Nat.dvd_prime hap).mp hpa |>.resolve_left hpp.ne_one
    simpa [this] using ha
  intro t ht u hu htu
  exact Finset.Subset.antisymm (subset_of_prod_eq t ht u hu htu)
    (subset_of_prod_eq u hu t ht htu.symm)

/-- Expanding the squarefree Euler product injects its terms into the harmonic
sum.  In particular this also handles `q = 1`, when both products are empty. -/
lemma prod_one_add_inv_primeFactors_le_one_add_log (q : ℕ) (hq : 1 ≤ q) :
    (∏ p ∈ q.primeFactors, (1 + ((p : ℝ)⁻¹))) ≤ 1 + Real.log q := by
  let d : Finset ℕ → ℕ := fun t => ∏ p ∈ t, p
  have himage : Finset.image d q.primeFactors.powerset ⊆ Finset.Icc 1 q := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    have ht' : t ⊆ q.primeFactors := Finset.mem_powerset.mp ht
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors (ht' hp)).pos
    · exact Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one hq)
        ((Finset.prod_dvd_prod_of_subset t q.primeFactors id ht').trans
          (Nat.prod_primeFactors_dvd q))
  have hsumImage :
      (∑ n ∈ Finset.image d q.primeFactors.powerset, ((n : ℝ)⁻¹)) =
        ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ)⁻¹) := by
    rw [Finset.sum_image (primeSubsetProduct_injective q)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
  calc
    (∏ p ∈ q.primeFactors, (1 + ((p : ℝ)⁻¹))) =
        ∑ t ∈ q.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ)⁻¹) := by
      simp_rw [add_comm (1 : ℝ), Finset.prod_add]
      simp
    _ = ∑ n ∈ Finset.image d q.primeFactors.powerset, ((n : ℝ)⁻¹) :=
      hsumImage.symm
    _ ≤ ∑ n ∈ Finset.Icc 1 q, ((n : ℝ)⁻¹) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro i hi hni
        positivity)
    _ = (harmonic q : ℝ) := by
      simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using
        congrArg (fun x : ℚ => (x : ℝ)) (harmonic_eq_sum_Icc (n := q)).symm
    _ ≤ 1 + Real.log q := by exact_mod_cast harmonic_le_one_add_log q

/-- On `re s ≥ 1`, each omitted Euler factor has norm at most `1 + 1/p`. -/
lemma principalEulerFactorNorm_le_one_add_inv
    {s : ℂ} (hs : 1 ≤ s.re) {p : ℕ} (hp : p.Prime) :
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ)⁻¹ := by
  have hpow : ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
    calc
      ‖(p : ℂ) ^ (-s)‖ ≤ ‖(p : ℂ) ^ (-(1 : ℂ))‖ := by
        apply Complex.norm_natCast_cpow_le_norm_natCast_cpow_of_pos hp.pos
        simp only [neg_re, one_re]
        linarith
      _ = (p : ℝ)⁻¹ := by
        rw [show -(1 : ℂ) = (-1 : ℤ) by norm_num, cpow_intCast]
        simp
  calc
    ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (p : ℝ)⁻¹ := by simpa using add_le_add_left hpow 1

/-- The principal-character Euler correction has only logarithmic modulus cost. -/
lemma principalEulerCorrectionNorm_le_one_add_log
    (q : ℕ) (hq : 1 ≤ q) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ 1 + Real.log q := by
  calc
    ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))‖ =
        ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖ := by simp
    _ ≤ ∏ p ∈ q.primeFactors, (1 + (p : ℝ)⁻¹) := by
      gcongr with p hp
      exact principalEulerFactorNorm_le_one_add_inv hs
        (Nat.prime_of_mem_primeFactors hp)
    _ ≤ 1 + Real.log q := prod_one_add_inv_primeFactors_le_one_add_log q hq

/-- A logarithmic-modulus bound for the principal Dirichlet `L`-function in
the closed half-plane `re s ≥ 1`, away from the zeta pole. -/
theorem norm_LFunctionTrivChar_le_one_add_log_mul_riemannZeta
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) (hsne : s ≠ 1) :
    ‖LFunctionTrivChar q s‖ ≤ (1 + Real.log q) * ‖riemannZeta s‖ := by
  rw [LFunctionTrivChar_eq_mul_riemannZeta hsne, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (principalEulerCorrectionNorm_le_one_add_log q
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hs) (norm_nonneg _)

/-- If a character squares to the trivial character, the same logarithmic
bound applies to the `L`-function of its square. -/
theorem norm_LFunction_sq_le_one_add_log_mul_riemannZeta
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1)
    {s : ℂ} (hs : 1 ≤ s.re) (hsne : s ≠ 1) :
    ‖(χ ^ 2).LFunction s‖ ≤ (1 + Real.log q) * ‖riemannZeta s‖ := by
  rw [hquad, ← LFunctionTrivChar]
  exact norm_LFunctionTrivChar_le_one_add_log_mul_riemannZeta q hs hsne

end DirichletCharacter