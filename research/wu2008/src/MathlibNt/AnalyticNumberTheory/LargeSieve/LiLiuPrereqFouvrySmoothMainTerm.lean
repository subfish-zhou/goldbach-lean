import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryArithmeticPoisson

/-!
# A common smooth main term for the signed U and V dispersion sums

The restricted Möbius density is evaluated by a finite prime-factor argument.
Consequently the two actual dispersion sums have the same zero mode. Their
errors are bounded by explicit coefficient envelopes, with constants chosen
before the scale, supports, coefficients, moduli, and residue. No growth bound
for those envelopes and no well-factorability hypothesis is asserted here.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

private theorem totient_real_prod (n : ℕ) :
    (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (algebraMap ℚ ℝ) (Nat.totient_eq_mul_prod_factors n)
  simpa only [map_natCast, map_mul, map_sub, map_one, map_inv₀, map_prod] using h

/-- Only the squarefree divisors supported on primes coprime to `q` contribute. -/
theorem restricted_moebius_density_prod (q : ℕ) {r : ℕ} (hr : r ≠ 0) :
    (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
      (ArithmeticFunction.moebius d : ℝ) / d) =
        ∏ p ∈ r.primeFactors.filter (fun p ↦ p.Coprime q), (1 - (p : ℝ)⁻¹) := by
  let t := r.primeFactors.filter (fun p ↦ p.Coprime q)
  let k := ∏ p ∈ t, p
  have ht : ∀ p ∈ t, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ (ht p hp).ne_zero
  have hkr : k ∣ r :=
    (Finset.prod_dvd_prod_of_subset t r.primeFactors id (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd r)
  have hkq : k.Coprime q :=
    Nat.Coprime.prod_left fun p hp ↦ (Finset.mem_filter.mp hp).2
  have hsub : k.divisors ⊆ r.divisors.filter (fun d ↦ d.Coprime q) := by
    intro d hd
    have hdk := Nat.dvd_of_mem_divisors hd
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdk.trans hkr, hr⟩, hkq.of_dvd_left hdk⟩
  have hsum :
      (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        (ArithmeticFunction.moebius d : ℝ) / d) =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) / d := by
    symm
    apply Finset.sum_subset hsub
    intro d hd hdk
    have hsf : ¬Squarefree d := by
      intro hsf
      apply hdk
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hk⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsf]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp,
            hpd.trans (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1), hr⟩,
          (Finset.mem_filter.mp hd).2.of_dvd_left hpd⟩
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
  rw [hsum, moebius_density hk, totient_real_prod, Nat.primeFactors_prod ht]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  exact mul_div_cancel_left₀ _ hkR

/-- The exact finite arithmetic identity identifying the U and V zero modes. -/
theorem restricted_moebius_density {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
      (ArithmeticFunction.moebius d : ℝ) / d) / q =
        ((q * r).totient : ℝ) / ((q.totient : ℝ) * (q * r : ℕ)) := by
  have hfilter : r.primeFactors.filter (fun p ↦ p.Coprime q) =
      r.primeFactors \ q.primeFactors := by
    ext p
    by_cases hp : p ∈ r.primeFactors
    · simp only [Finset.mem_filter, Finset.mem_sdiff, hp, true_and,
        (Nat.prime_of_mem_primeFactors hp).coprime_iff_not_dvd,
        Nat.mem_primeFactors_of_ne_zero hq, Nat.prime_of_mem_primeFactors hp]
    · simp [hp]
  have hprod :
      (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) *
          (∏ p ∈ r.primeFactors \ q.primeFactors, (1 - (p : ℝ)⁻¹)) =
        ∏ p ∈ (q * r).primeFactors, (1 - (p : ℝ)⁻¹) := by
    rw [Nat.primeFactors_mul hq hr, ← Finset.prod_union
      (Finset.disjoint_left.mpr fun p hp hpd ↦ (Finset.mem_sdiff.mp hpd).2 hp),
      Finset.union_sdiff_self_eq_union]
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hqrR : ((q * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hq hr)
  have hphi : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  rw [restricted_moebius_density_prod q hr, hfilter]
  apply (div_eq_div_iff hqR (mul_ne_zero hphi hqrR)).mpr
  rw [totient_real_prod q, totient_real_prod (q * r)]
  calc
    _ = ((q : ℝ) * (q * r : ℕ)) *
        ((∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ r.primeFactors \ q.primeFactors, (1 - (p : ℝ)⁻¹)) := by ring
    _ = _ := by rw [hprod]; ring

/-- The common zero-frequency contribution, with all coefficient signs retained. -/
def smoothUMain (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    uModulusCoefficient N β c q r *
      ((M * dyadicCutoffMass) * ((q * r).totient : ℝ) / (q * r : ℕ))

def vModulusCoefficient (N : Finset ℕ) (β c : ℕ → ℝ) (q r : ℕ) : ℝ :=
  (c q * c r / (r.totient : ℝ)) * coprimeMass N β r

/-- The zero mode obtained directly from the mixed progression expansion. -/
def smoothVZeroMode (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    vModulusCoefficient N β c q r *
      (coprimeMass N β q * ((M * dyadicCutoffMass / q) *
        ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
          (ArithmeticFunction.moebius d : ℝ) / d))

/-- Equality of the actual U and V zero-mode formulas, not an asymptotic premise. -/
theorem smoothVZeroMode_eq_smoothUMain
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    smoothVZeroMode M N Q β c a = smoothUMain M N Q β c a := by
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  have hd :
      (M * dyadicCutoffMass / q) *
          (∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
            (ArithmeticFunction.moebius d : ℝ) / d) =
        (M * dyadicCutoffMass) *
          (((q * r).totient : ℝ) / ((q.totient : ℝ) * (q * r : ℕ))) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, restricted_moebius_density
      (hQ q (Finset.mem_filter.mp hq).1) (hQ r (Finset.mem_filter.mp hr).1)]
  rw [hd]
  simp only [vModulusCoefficient, uModulusCoefficient, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The divisor-count envelope for U; no logarithmic growth estimate is implicit. -/
def smoothUErrorEnvelope (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    |uModulusCoefficient N β c q r| * ((q * r).divisors.card : ℝ)

/-- The mixed envelope uses the signed `r`-mass in its outer coefficient and
the absolute `q`-coprime beta mass only in the error majorant. -/
def smoothVErrorEnvelope (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    |vModulusCoefficient N β c q r| *
      coprimeMass N (fun n ↦ |β n|) q * (r.divisors.card : ℝ)

theorem smoothUErrorEnvelope_nonneg
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    0 ≤ smoothUErrorEnvelope N Q β c a := by
  exact Finset.sum_nonneg fun q _ ↦ Finset.sum_nonneg fun r _ ↦
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

theorem smoothVErrorEnvelope_nonneg
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    0 ≤ smoothVErrorEnvelope N Q β c a := by
  apply Finset.sum_nonneg
  intro q _
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg _ (Nat.cast_nonneg _)
  apply mul_nonneg (abs_nonneg _)
  exact Finset.sum_nonneg fun n _ ↦ by split_ifs <;> positivity

/-- The actual signed U dispersion sum is approximated by the common smooth
main term, uniformly before every changing scale, support, and arithmetic input. -/
theorem dispersionU_smooth_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      (∀ q ∈ Q, q ≠ 0) →
      |dispersionU S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤ C * smoothUErrorEnvelope N Q β c a := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_coprime_uniform_error
  refine ⟨C, hC, fun M hM S hS N Q β c a hQ ↦ ?_⟩
  rw [dispersionU_eq_double_sum]
  change |(∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      uModulusCoefficient N β c q r *
        ∑ m ∈ S, if m.Coprime (q * r) then scaledDyadicCutoff M m else 0) -
    (∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      uModulusCoefficient N β c q r *
        ((M * dyadicCutoffMass) * ((q * r).totient : ℝ) / (q * r : ℕ)))| ≤ _
  conv_rhs => simp only [smoothUErrorEnvelope, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [← mul_sub, abs_mul]
  calc
    _ ≤ |uModulusCoefficient N β c q r| * (C * ((q * r).divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (hbound M hM S hS (q * r)
          (mul_ne_zero (hQ q (Finset.mem_filter.mp hq).1)
            (hQ r (Finset.mem_filter.mp hr).1))) (abs_nonneg _)
    _ = _ := by ring

/-- The actual signed V dispersion sum has the same main term as U. -/
theorem dispersionV_smooth_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      (∀ q ∈ Q, q ≠ 0) →
      |dispersionV S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤ C * smoothVErrorEnvelope N Q β c a := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_coprime_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS N Q β c a hQ ↦ ?_⟩
  rw [dispersionV_eq_progression_sum, ← smoothVZeroMode_eq_smoothUMain M N Q β c a hQ]
  change |(∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      vModulusCoefficient N β c q r *
        ∑ n ∈ N, β n * ∑ m ∈ S,
          if n.Coprime q ∧ m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) -
    (∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      vModulusCoefficient N β c q r *
        (coprimeMass N β q * ((M * dyadicCutoffMass / q) *
          ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
            (ArithmeticFunction.moebius d : ℝ) / d)))| ≤ _
  conv_rhs => simp only [smoothVErrorEnvelope, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [← mul_sub, abs_mul]
  let z := (M * dyadicCutoffMass / q) *
    ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q), (ArithmeticFunction.moebius d : ℝ) / d
  have hinner :
      |(∑ n ∈ N, β n * ∑ m ∈ S,
          if n.Coprime q ∧ m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - coprimeMass N β q * z| ≤
        C * coprimeMass N (fun n ↦ |β n|) q * (r.divisors.card : ℝ) := by
    unfold coprimeMass
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ n ∈ N, |β n *
          (∑ m ∈ S, if n.Coprime q ∧ m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - (if n.Coprime q then β n else 0) * z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ N, C * (if n.Coprime q then |β n| else 0) * (r.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : n.Coprime q
        · simp only [Nat.Coprime] at hn ⊢
          simp only [hn, true_and, if_true]
          rw [← mul_sub, abs_mul]
          calc
            _ ≤ |β n| * (C * (r.divisors.card : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (hbound M hM S hS q r n
                  (Nat.pos_of_ne_zero (hQ q (Finset.mem_filter.mp hq).1))
                  (hQ r (Finset.mem_filter.mp hr).1) hn a (Finset.mem_filter.mp hq).2)
                (abs_nonneg _)
            _ = _ := by ring
        · simp only [Nat.Coprime] at hn ⊢
          simp [hn]
      _ = _ := by rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ ≤ |vModulusCoefficient N β c q r| *
        (C * coprimeMass N (fun n ↦ |β n|) q * (r.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
    _ = _ := by ring

/-- One universal constant controls U, V, and their difference; the common
signed zero mode cancels exactly in the last bound. -/
theorem dispersionUV_smooth_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      (∀ q ∈ Q, q ≠ 0) →
      (|dispersionU S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤ C * smoothUErrorEnvelope N Q β c a) ∧
      (|dispersionV S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| ≤ C * smoothVErrorEnvelope N Q β c a) ∧
      |dispersionV S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          dispersionU S N Q (fun m ↦ scaledDyadicCutoff M m) β c a| ≤
        C * (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a) := by
  obtain ⟨CU, hCU, hU⟩ := dispersionU_smooth_uniform_error
  obtain ⟨CV, hCV, hV⟩ := dispersionV_smooth_uniform_error
  refine ⟨CU + CV, add_pos hCU hCV, fun M hM S hS N Q β c a hQ ↦ ?_⟩
  have hu := (hU M hM S hS N Q β c a hQ).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCV.le)
      (smoothUErrorEnvelope_nonneg N Q β c a))
  have hv := (hV M hM S hS N Q β c a hQ).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCU.le)
      (smoothVErrorEnvelope_nonneg N Q β c a))
  refine ⟨hu, hv, ?_⟩
  calc
    _ = |(dispersionV S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a) -
        (dispersionU S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a)| := by congr 1; ring
    _ ≤ |dispersionV S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| +
        |dispersionU S N Q (fun m ↦ scaledDyadicCutoff M m) β c a -
          smoothUMain M N Q β c a| := abs_sub _ _
    _ ≤ (CU + CV) * smoothVErrorEnvelope N Q β c a +
        (CU + CV) * smoothUErrorEnvelope N Q β c a := add_le_add hv hu
    _ = _ := by ring

/-- The canonical cutoff support removes the support-containment hypothesis. -/
theorem dispersionV_sub_U_dyadicCutoff_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M →
      ∀ N Q : Finset ℕ, ∀ β c : ℕ → ℝ, ∀ a : ℤ,
      (∀ q ∈ Q, q ≠ 0) →
      |dispersionV (dyadicCutoffNatSupport M) N Q
          (fun m ↦ scaledDyadicCutoff M m) β c a -
        dispersionU (dyadicCutoffNatSupport M) N Q
          (fun m ↦ scaledDyadicCutoff M m) β c a| ≤
        C * (smoothUErrorEnvelope N Q β c a + smoothVErrorEnvelope N Q β c a) := by
  obtain ⟨C, hC, hbound⟩ := dispersionUV_smooth_uniform_error
  exact ⟨C, hC, fun M hM N Q β c a hQ ↦
    (hbound M hM _ (scaledDyadicCutoff_mem_natSupport hM) N Q β c a hQ).2.2⟩

/-- The constructed cutoff, rather than an assumed majorant, gives the
smoothed dispersion reduction for an alpha support in `[M, 2M]`. -/
theorem signedError_sq_le_dyadicCutoff_dispersion
    {M : ℝ} (hM : 0 < M) (A N Q : Finset ℕ)
    (α β c : ℕ → ℝ) (a : ℤ)
    (hA : ∀ m ∈ A, (m : ℝ) ∈ Set.Icc M (2 * M)) :
    signedError A N Q α β c a ^ 2 ≤
      (∑ m ∈ A, α m ^ 2) *
        (dispersionW (dyadicCutoffNatSupport M) N Q
            (fun m ↦ scaledDyadicCutoff M m) β c a -
          2 * dispersionV (dyadicCutoffNatSupport M) N Q
            (fun m ↦ scaledDyadicCutoff M m) β c a +
          dispersionU (dyadicCutoffNatSupport M) N Q
            (fun m ↦ scaledDyadicCutoff M m) β c a) := by
  apply signedError_sq_le_smoothed_dispersion
  · intro m hm
    apply scaledDyadicCutoff_mem_natSupport hM
    rw [scaledDyadicCutoff_eq_one hM (hA m hm)]
    exact one_ne_zero
  · intro m _
    exact scaledDyadicCutoff_nonneg M m
  · intro m hm
    exact (scaledDyadicCutoff_eq_one hM (hA m hm)).ge

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
