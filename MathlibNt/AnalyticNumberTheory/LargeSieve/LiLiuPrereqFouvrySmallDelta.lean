import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCovariance
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothErrorBounds

/-!
# Small gcd contribution to the actual W-minus-U zero mode

The beta input is an independent coprime-sieved AP discrepancy estimate.
An L-infinity times L-one covariance bound avoids a factor of the gcd.
Elementary reciprocal divisor means then evaluate the entire small-gcd
modulus sum. The complementary large-gcd contribution is left explicit.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem betaResidueMass_abs_le (N : Finset ℕ) (β : ℕ → ℝ) (q δ b : ℕ) :
    |betaResidueMass N β q δ b| ≤
      betaResidueMass N (fun n => |β n|) q δ b := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n _
  split_ifs <;> simp

/-- Centering on reduced classes costs at most twice the original L-one mass.
The partition uses the actual coprime sieve by `q`. -/
theorem sum_abs_betaResidueMass_centered_le
    (N : Finset ℕ) (β : ℕ → ℝ) {q δ : ℕ}
    (hδ : 0 < δ) (hdq : δ ∣ q) :
    (∑ b ∈ betaReducedResidues δ,
      |betaResidueMass N β q δ b - coprimeMass N β q / (δ.totient : ℝ)|) ≤
        2 * ∑ n ∈ N, |β n| := by
  have hφ : (δ.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hδ).ne'
  calc
    _ ≤ ∑ b ∈ betaReducedResidues δ,
        (betaResidueMass N (fun n => |β n|) q δ b +
          |coprimeMass N β q| / (δ.totient : ℝ)) := by
      apply sum_le_sum
      intro b _
      exact (abs_sub _ _).trans (add_le_add (betaResidueMass_abs_le N β q δ b)
        (by rw [abs_div, Nat.abs_cast]))
    _ = coprimeMass N (fun n => |β n|) q + |coprimeMass N β q| := by
      rw [sum_add_distrib, sum_betaResidueMass N _ hδ hdq]
      simp only [sum_const, nsmul_eq_mul, betaReducedResidues_card]
      rw [mul_div_cancel₀ _ hφ]
    _ ≤ _ := by
      have := coprimeMass_of_abs_le_sum_abs N β q
      have := coprimeMass_abs_le_sum_abs N β q
      linarith

/-- Only one independent AP bound is needed, with no totient/gcd factor. -/
theorem betaCovariance_abs_le_coprimeAP_lone
    (N : Finset ℕ) (β : ℕ → ℝ) {q r : ℕ} (hq : 0 < q)
    {E : ℝ} (hE : 0 ≤ E)
    (hAP : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaCoprimeAPDiscrepancy N β (q.gcd r) (q / q.gcd r) b| ≤ E) :
    |betaCovariance N β q r| ≤ 2 * E * ∑ n ∈ N, |β n| := by
  unfold betaCovariance
  calc
    _ ≤ ∑ b ∈ betaReducedResidues (q.gcd r),
        E * |betaResidueMass N β r (q.gcd r) b -
          coprimeMass N β r / ((q.gcd r).totient : ℝ)| := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [betaResidueMass_centered_eq_coprimeAPDiscrepancy N β
        (Nat.gcd_dvd_left q r) (mem_filter.mp hb).2]
      exact hAP b hb
    _ ≤ E * (2 * ∑ n ∈ N, |β n|) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_abs_betaResidueMass_centered_le N β
          (Nat.gcd_pos_of_pos_left r hq) (Nat.gcd_dvd_right q r)) hE
    _ = _ := by ring

/-- A single term of the divisor convolution suffices; no monotonicity
of prime-power divisor coefficients is required. -/
theorem fouvryTau_div_le_succ (κ : ℕ) {q δ : ℕ} (hq : q ≠ 0) (hdq : δ ∣ q) :
    fouvryTau κ (q / δ) ≤ fouvryTau (κ + 1) q := by
  rw [fouvryTau_succ]
  exact single_le_sum (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdq, hq⟩)

/-- The signed small-gcd part in the exact normalization of W zero minus U zero. -/
def smoothWUSmallDelta (M D : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  (M * dyadicCutoffMass) *
    ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      if (q.gcd r : ℝ) ≤ D then
        (c q * c r / (q.lcm r : ℝ)) * betaCovariance N β q r else 0

/-- The signed large-gcd remainder. No estimate for this term is asserted. -/
def smoothWULargeDelta (M D : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  (M * dyadicCutoffMass) *
    ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      if D < (q.gcd r : ℝ) then
        (c q * c r / (q.lcm r : ℝ)) * betaCovariance N β q r else 0

theorem smoothWMain_sub_smoothUMain_eq_small_add_large
    (M D : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    smoothWMain M N Q β c a - smoothUMain M N Q β c a =
      smoothWUSmallDelta M D N Q β c a + smoothWULargeDelta M D N Q β c a := by
  rw [smoothWMain_sub_smoothUMain_eq_betaCovariance M N Q β c a hQ]
  unfold smoothWUSmallDelta smoothWULargeDelta
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro q _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  by_cases h : (q.gcd r : ℝ) ≤ D
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

theorem sum_reduced_abs_mul_tau_div_le
    (j κ : ℕ) {L : ℝ} (hL : 1 ≤ L) (Q : Finset ℕ)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    (∑ q ∈ reducedModuli Q a, |c q| * (fouvryTau κ q : ℝ) / q) ≤
      (1 + Real.log L) ^ (j * κ) := by
  calc
    _ ≤ ∑ q ∈ reducedModuli Q a, (fouvryTau (j * κ) q : ℝ) / q := by
      apply sum_le_sum
      intro q hq
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_right (hc q (mem_filter.mp hq).1)
        (Nat.cast_nonneg _)).trans (by exact_mod_cast fouvryTau_mul_le j κ q)
    _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau (j * κ) q : ℝ) / q :=
      sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hQ)
        (fun _ _ _ => by positivity)
    _ ≤ _ := sum_fouvryTau_div_le_real _ hL

theorem sum_reduced_abs_div_le
    (j : ℕ) {L : ℝ} (hL : 1 ≤ L) (Q : Finset ℕ)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ) :
    (∑ q ∈ reducedModuli Q a, |c q| / q) ≤ (1 + Real.log L) ^ j := by
  calc
    _ ≤ ∑ q ∈ Ioc 0 ⌊L⌋₊, (fouvryTau j q : ℝ) / q := by
      apply (sum_le_sum (fun q hq => div_le_div_of_nonneg_right
        (hc q (mem_filter.mp hq).1) (Nat.cast_nonneg _))).trans
      exact sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hQ)
        (fun _ _ _ => by positivity)
    _ ≤ _ := sum_fouvryTau_div_le_real _ hL

private theorem abs_lcm_weight_mul_tau_le
    (κ : ℕ) (c : ℕ → ℝ) {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0)
    {D : ℝ} (hδ : (q.gcd r : ℝ) ≤ D) :
    |c q * c r / (q.lcm r : ℝ)| * (fouvryTau κ (q / q.gcd r) : ℝ) ≤
      D * ((|c q| * (fouvryTau (κ + 1) q : ℝ) / q) * (|c r| / r)) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hr' : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hl : (q.lcm r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hq hr)
  have he : (q.gcd r : ℝ) * (q.lcm r : ℝ) = (q : ℝ) * r := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  have hrec : (1 : ℝ) / (q.lcm r : ℝ) = (q.gcd r : ℝ) / ((q : ℝ) * r) := by
    apply (div_eq_div_iff hl (mul_ne_zero hq' hr')).mpr
    simpa only [one_mul] using he.symm
  calc
    _ = (q.gcd r : ℝ) *
        ((|c q| * (fouvryTau κ (q / q.gcd r) : ℝ) / q) * (|c r| / r)) := by
      rw [abs_div, abs_mul, Nat.abs_cast, div_eq_mul_one_div _ (q.lcm r : ℝ), hrec]
      ring
    _ ≤ _ := by
      gcongr
      · exact (Nat.cast_nonneg (q.gcd r)).trans hδ
      · exact fouvryTau_div_le_succ κ hq (Nat.gcd_dvd_left q r)

/-- The small-gcd double modulus sum is completely evaluated. Beta order
`k` and coprime-sieve order `κ` are independent, and all weights stay signed.
There is no AP hypothesis at large gcd and no assumption on the target error. -/
theorem smoothWUSmallDelta_abs_le
    {k : ℕ} (hk : 1 ≤ k) (j κ : ℕ)
    {T L D E : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (M : ℝ) (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊)
    (β c : ℕ → ℝ) (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (hAP : ∀ q ∈ Q, ∀ δ : ℕ, δ ∣ q → 0 < δ → (δ : ℝ) ≤ D →
      ∀ b ∈ betaReducedResidues δ,
        |betaCoprimeAPDiscrepancy N β δ (q / δ) b| ≤
          E * (fouvryTau κ (q / δ) : ℝ)) :
    |smoothWUSmallDelta M D N Q β c a| ≤
      2 * |M * dyadicCutoffMass| * E * (T * (1 + Real.log T) ^ (k - 1)) *
        D * (1 + Real.log L) ^ (j * (κ + 2)) := by
  let V := T * (1 + Real.log T) ^ (k - 1)
  let w := fun q : ℕ => |c q| * (fouvryTau (κ + 1) q : ℝ) / q
  let v := fun r : ℕ => |c r| / r
  have hlogT := Real.log_nonneg hT
  have hlogL := Real.log_nonneg hL
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hQ0 : ∀ q ∈ reducedModuli Q a, q ≠ 0 :=
    fun q hq => (mem_Ioc.mp (hQ (mem_filter.mp hq).1)).1.ne'
  have hcov : ∀ q ∈ reducedModuli Q a, ∀ r ∈ reducedModuli Q a,
      (q.gcd r : ℝ) ≤ D →
      |betaCovariance N β q r| ≤
        2 * (E * (fouvryTau κ (q / q.gcd r) : ℝ)) * V := by
    intro q hq r _ hδ
    apply (betaCovariance_abs_le_coprimeAP_lone N β (Nat.pos_of_ne_zero (hQ0 q hq))
      (by positivity) (hAP q (mem_filter.mp hq).1 _
        (Nat.gcd_dvd_left q r) (Nat.gcd_pos_of_pos_left r
          (Nat.pos_of_ne_zero (hQ0 q hq))) hδ)).trans
    exact mul_le_mul_of_nonneg_left (sum_abs_le_fouvryTau_mean hk hT N hN β hβ)
      (by positivity)
  unfold smoothWUSmallDelta
  rw [abs_mul]
  calc
    _ ≤ |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          (2 * E * V * D) * (w q * v r) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro r hr
      by_cases hδ : (q.gcd r : ℝ) ≤ D
      · rw [if_pos hδ, abs_mul]
        calc
          _ ≤ |c q * c r / (q.lcm r : ℝ)| *
              (2 * (E * (fouvryTau κ (q / q.gcd r) : ℝ)) * V) :=
            mul_le_mul_of_nonneg_left (hcov q hq r hr hδ) (abs_nonneg _)
          _ = (2 * E * V) * (|c q * c r / (q.lcm r : ℝ)| *
              (fouvryTau κ (q / q.gcd r) : ℝ)) := by ring
          _ ≤ (2 * E * V) * (D * (w q * v r)) :=
            mul_le_mul_of_nonneg_left
              (abs_lcm_weight_mul_tau_le κ c (hQ0 q hq) (hQ0 r hr) hδ) (by positivity)
          _ = _ := by ring
      · rw [if_neg hδ, abs_zero]
        dsimp [w, v]
        positivity
    _ = |M * dyadicCutoffMass| * (2 * E * V * D) *
        ((∑ q ∈ reducedModuli Q a, w q) * (∑ r ∈ reducedModuli Q a, v r)) := by
      rw [sum_mul_sum]
      simp only [mul_sum]
      ring
    _ ≤ |M * dyadicCutoffMass| * (2 * E * V * D) *
        ((1 + Real.log L) ^ (j * (κ + 1)) * (1 + Real.log L) ^ j) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul
      · exact sum_reduced_abs_mul_tau_div_le j (κ + 1) hL Q hQ c hc a
      · exact sum_reduced_abs_div_le j hL Q hQ c hc a
      · exact sum_nonneg (fun r _ => by dsimp [v]; positivity)
      · positivity
    _ = _ := by
      rw [← pow_add, show j * (κ + 1) + j = j * (κ + 2) by ring]
      ring

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
