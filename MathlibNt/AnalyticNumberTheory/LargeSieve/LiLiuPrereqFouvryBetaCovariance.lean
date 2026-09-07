import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmoothMainTerm
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWZeroMode

/-!
# Finite beta covariance in the actual W and U zero modes

The algebra of Fouvry (1984), p. 242, (9.2) and the following unnumbered
identity, for the full unpruned zero mode. No spectral estimate or use of
(9.1) is involved. All beta and modulus coefficients remain signed.

The discrepancy estimates below are conditional on independent beta
arithmetic-progression estimates; they do not prove a Siegel--Walfisz
estimate or the final Fouvry distribution bound.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

/-- Canonical representatives of the reduced residue classes, including
the representative zero when the modulus is one. -/
def betaReducedResidues (δ : ℕ) : Finset ℕ :=
  (Finset.range δ).filter (fun b ↦ b.Coprime δ)

theorem betaReducedResidues_card (δ : ℕ) :
    (betaReducedResidues δ).card = δ.totient := by
  simp only [betaReducedResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm]

/-- The original coprime sieve is retained, even when the progression modulus
is only a divisor of the sieving modulus. -/
def betaResidueMass (N : Finset ℕ) (β : ℕ → ℝ) (q δ b : ℕ) : ℝ :=
  ∑ n ∈ N, if n.Coprime q ∧ Nat.ModEq δ n b then β n else 0

private theorem sum_betaReducedResidues_indicator {δ n : ℕ}
    (hδ : 0 < δ) (hn : n.Coprime δ) (z : ℝ) :
    (∑ b ∈ betaReducedResidues δ, if Nat.ModEq δ n b then z else 0) = z := by
  have hm : n % δ ∈ betaReducedResidues δ := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hδ), ?_⟩
    change (n % δ).gcd δ = 1
    rw [(Nat.mod_modEq n δ).gcd_eq, hn.gcd_eq_one]
  rw [Finset.sum_eq_single (n % δ)]
  · simp [Nat.ModEq]
  · intro b hb hne
    apply if_neg
    intro he
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have he' : n % δ = b := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb'] using he
    exact hne he'.symm
  · exact fun h ↦ (h hm).elim

/-- Partition of the actual signed coprime mass over reduced classes.
This applies to either modulus in a pair since their gcd divides both. -/
theorem sum_betaResidueMass (N : Finset ℕ) (β : ℕ → ℝ)
    {q δ : ℕ} (hδ : 0 < δ) (hdq : δ ∣ q) :
    (∑ b ∈ betaReducedResidues δ, betaResidueMass N β q δ b) =
      coprimeMass N β q := by
  unfold betaResidueMass coprimeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Coprime q
  · have hn' := hn
    simp only [Nat.Coprime] at hn ⊢
    simp only [hn, true_and, if_true]
    exact sum_betaReducedResidues_indicator hδ (hn'.of_dvd_right hdq) _
  · simp [hn]

private theorem beta_pair_indicator {q r n₁ n₂ : ℕ}
    (hq : 0 < q) (z₁ z₂ : ℝ) :
    (∑ b ∈ betaReducedResidues (q.gcd r),
      (if n₁.Coprime q ∧ Nat.ModEq (q.gcd r) n₁ b then z₁ else 0) *
      (if n₂.Coprime r ∧ Nat.ModEq (q.gcd r) n₂ b then z₂ else 0)) =
        if WCompatible q r n₁ n₂ then z₁ * z₂ else 0 := by
  classical
  by_cases h₁ : n₁.Coprime q
  · by_cases h₂ : n₂.Coprime r
    · have h₁' := h₁
      simp only [Nat.Coprime] at h₁ h₂
      simp only [WCompatible, Nat.Coprime, h₁, h₂, true_and]
      by_cases hc : Nat.ModEq (q.gcd r) n₁ n₂
      · rw [if_pos hc]
        have he (b : ℕ) :
            Nat.ModEq (q.gcd r) n₁ b ↔ Nat.ModEq (q.gcd r) n₂ b :=
          ⟨fun h ↦ hc.symm.trans h, fun h ↦ hc.trans h⟩
        simp_rw [← he]
        simp only [ite_mul_ite, mul_zero]
        exact sum_betaReducedResidues_indicator (Nat.gcd_pos_of_pos_left r hq)
          (h₁'.of_dvd_right (Nat.gcd_dvd_left q r)) _
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro b _
        by_cases hb : Nat.ModEq (q.gcd r) n₁ b
        · have hb' : ¬Nat.ModEq (q.gcd r) n₂ b :=
            fun h ↦ hc (hb.trans h.symm)
          simp [hb']
        · simp [hb]
    · simp [h₂, WCompatible]
  · simp [h₁, WCompatible]

/-- The compatibility sum in `smoothWMain` is precisely a sum of products
of beta masses in the same reduced residue class. -/
theorem compatible_beta_sum_eq_residue_products
    (N : Finset ℕ) (β : ℕ → ℝ) {q r : ℕ} (hq : 0 < q) :
    (∑ n₁ ∈ N, ∑ n₂ ∈ N,
      if WCompatible q r n₁ n₂ then β n₁ * β n₂ else 0) =
        ∑ b ∈ betaReducedResidues (q.gcd r),
          betaResidueMass N β q (q.gcd r) b *
          betaResidueMass N β r (q.gcd r) b := by
  classical
  simp only [betaResidueMass, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₂ _
  exact (beta_pair_indicator hq (β n₁) (β n₂)).symm

/-- Centered beta covariance on the reduced classes modulo the gcd. -/
def betaCovariance (N : Finset ℕ) (β : ℕ → ℝ) (q r : ℕ) : ℝ :=
  ∑ b ∈ betaReducedResidues (q.gcd r),
    (betaResidueMass N β q (q.gcd r) b -
      coprimeMass N β q / ((q.gcd r).totient : ℝ)) *
    (betaResidueMass N β r (q.gcd r) b -
      coprimeMass N β r / ((q.gcd r).totient : ℝ))

/-- F84 p. 242, the unnumbered identity following (9.2). Both centering
identities are proved from the actual coprime masses, not assumed. -/
theorem beta_covariance_identity
    (N : Finset ℕ) (β : ℕ → ℝ) {q r : ℕ} (hq : 0 < q) :
    (∑ b ∈ betaReducedResidues (q.gcd r),
      betaResidueMass N β q (q.gcd r) b *
      betaResidueMass N β r (q.gcd r) b) -
        coprimeMass N β q * coprimeMass N β r / ((q.gcd r).totient : ℝ) =
      betaCovariance N β q r := by
  have hδ := Nat.gcd_pos_of_pos_left r hq
  have hφ : ((q.gcd r).totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hδ).ne'
  unfold betaCovariance
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, betaReducedResidues_card,
    sum_betaResidueMass N β hδ (Nat.gcd_dvd_left q r),
    sum_betaResidueMass N β hδ (Nat.gcd_dvd_right q r)]
  field_simp
  ring

/-- The totient and lcm identity responsible for the U coefficient in (9.2).
It holds for arbitrary nonzero moduli, not only coprime moduli. -/
theorem totient_pair_density_eq_lcm {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    ((q * r).totient : ℝ) /
        ((q.totient : ℝ) * (r.totient : ℝ) * (q * r : ℕ)) =
      1 / ((q.lcm r : ℝ) * ((q.gcd r).totient : ℝ)) := by
  have hφq : (q.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have hφr : (r.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr)).ne'
  have hqr : ((q * r : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hq hr)
  have hl : (q.lcm r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hq hr)
  have hφδ : ((q.gcd r).totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero hq))).ne'
  have ht : ((q.gcd r).totient : ℝ) * ((q * r).totient : ℝ) =
      (q.totient : ℝ) * (r.totient : ℝ) * (q.gcd r : ℝ) := by
    exact_mod_cast Nat.totient_gcd_mul_totient_mul q r
  have hlcm : (q.gcd r : ℝ) * (q.lcm r : ℝ) = (q * r : ℕ) := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hφq hφr) hqr)
    (mul_ne_zero hl hφδ)).mpr
  calc
    _ = (((q.gcd r).totient : ℝ) * ((q * r).totient : ℝ)) * (q.lcm r : ℝ) := by ring
    _ = _ := by rw [ht, mul_assoc _ (q.gcd r : ℝ), hlcm, one_mul]

/-- The U summand has exactly the lcm-times-totient denominator, with the
original signed modulus coefficients and signed beta totals. -/
theorem uModulusCoefficient_zeroMode_eq
    (N : Finset ℕ) (β c : ℕ → ℝ) {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    uModulusCoefficient N β c q r *
        (((q * r).totient : ℝ) / (q * r : ℕ)) =
      (c q * c r / ((q.lcm r : ℝ) * ((q.gcd r).totient : ℝ))) *
        coprimeMass N β q * coprimeMass N β r := by
  calc
    _ = (c q * c r * coprimeMass N β q * coprimeMass N β r) *
        (((q * r).totient : ℝ) /
          ((q.totient : ℝ) * (r.totient : ℝ) * (q * r : ℕ))) := by
      simp only [uModulusCoefficient, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [totient_pair_density_eq_lcm hq hr]; ring

/-- The full signed U zero mode in the normalization of the W zero mode. -/
theorem smoothUMain_eq_residue_means
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    smoothUMain M N Q β c a =
      (M * dyadicCutoffMass) *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          (c q * c r / (q.lcm r : ℝ)) *
            (coprimeMass N β q * coprimeMass N β r /
              ((q.gcd r).totient : ℝ)) := by
  unfold smoothUMain
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  calc
    _ = (M * dyadicCutoffMass) * (uModulusCoefficient N β c q r *
        (((q * r).totient : ℝ) / (q * r : ℕ))) := by ring
    _ = _ := by
      rw [uModulusCoefficient_zeroMode_eq N β c
        (hQ q (Finset.mem_filter.mp hq).1) (hQ r (Finset.mem_filter.mp hr).1)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Actual W-minus-U zero-mode cancellation, the independent finite algebra
of F84 (9.2), without assuming that this difference is small.
No positivity is imposed on the scale or either coefficient sequence. -/
theorem smoothWMain_sub_smoothUMain_eq_betaCovariance
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    smoothWMain M N Q β c a - smoothUMain M N Q β c a =
      (M * dyadicCutoffMass) *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          (c q * c r / (q.lcm r : ℝ)) * betaCovariance N β q r := by
  rw [smoothUMain_eq_residue_means M N Q β c a hQ]
  unfold smoothWMain
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← mul_sub, compatible_beta_sum_eq_residue_products N β
    (Nat.pos_of_ne_zero (hQ q (Finset.mem_filter.mp hq).1)),
    beta_covariance_identity N β (Nat.pos_of_ne_zero (hQ q (Finset.mem_filter.mp hq).1))]

/-- Conditional estimate from independent pointwise beta-AP discrepancies.
The error bounds need not be assumed nonnegative separately. -/
theorem betaCovariance_abs_le (N : Finset ℕ) (β : ℕ → ℝ)
    (q r : ℕ) (Eq Er : ℝ)
    (hEq : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaResidueMass N β q (q.gcd r) b -
        coprimeMass N β q / ((q.gcd r).totient : ℝ)| ≤ Eq)
    (hEr : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaResidueMass N β r (q.gcd r) b -
        coprimeMass N β r / ((q.gcd r).totient : ℝ)| ≤ Er) :
    |betaCovariance N β q r| ≤ ((q.gcd r).totient : ℝ) * Eq * Er := by
  unfold betaCovariance
  calc
    _ ≤ ∑ b ∈ betaReducedResidues (q.gcd r),
        |(betaResidueMass N β q (q.gcd r) b -
          coprimeMass N β q / ((q.gcd r).totient : ℝ)) *
         (betaResidueMass N β r (q.gcd r) b -
          coprimeMass N β r / ((q.gcd r).totient : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ betaReducedResidues (q.gcd r), Eq * Er := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul (hEq b hb) (hEr b hb) (abs_nonneg _)
        ((abs_nonneg _).trans (hEq b hb))
    _ = _ := by simp [betaReducedResidues_card, mul_assoc]

/-- The beta-AP discrepancy with the additional, exact coprime sieve.
This is an analytic input to a Siegel--Walfisz hypothesis, not a claim that
arbitrary beta coefficients satisfy one. -/
def betaCoprimeAPDiscrepancy (N : Finset ℕ) (β : ℕ → ℝ) (d h b : ℕ) : ℝ :=
  (∑ n ∈ N, if n.Coprime h ∧ Nat.ModEq d n b then β n else 0) -
    coprimeMass N β (d * h) / (d.totient : ℝ)

/-- On a reduced class, the sieve by `q` is exactly the sieve by `q / δ`.
No prime-support assumption on beta is made. -/
theorem betaResidueMass_eq_quotientSieve (N : Finset ℕ) (β : ℕ → ℝ)
    {q δ b : ℕ} (hdq : δ ∣ q) (hb : b.Coprime δ) :
    betaResidueMass N β q δ b =
      ∑ n ∈ N, if n.Coprime (q / δ) ∧ Nat.ModEq δ n b then β n else 0 := by
  apply Finset.sum_congr rfl
  intro n _
  have he : (n.Coprime q ∧ Nat.ModEq δ n b) ↔
      (n.Coprime (q / δ) ∧ Nat.ModEq δ n b) := by
    constructor
    · exact fun h ↦ ⟨h.1.of_dvd_right (Nat.div_dvd_of_dvd hdq), h.2⟩
    · rintro ⟨hn, hc⟩
      have hnδ : n.Coprime δ := by
        change n.gcd δ = 1
        rw [hc.gcd_eq, hb.gcd_eq_one]
      refine ⟨?_, hc⟩
      rw [← Nat.mul_div_cancel' hdq]
      exact hnδ.mul_right hn
  exact if_congr he rfl rfl

/-- Bridge to the F87 coprime-sieved beta-SW input. The total mass is at
`δ * (q / δ) = q`, rather than an unsieved or prime-only total. -/
theorem betaResidueMass_centered_eq_coprimeAPDiscrepancy
    (N : Finset ℕ) (β : ℕ → ℝ) {q δ b : ℕ}
    (hdq : δ ∣ q) (hb : b.Coprime δ) :
    betaResidueMass N β q δ b - coprimeMass N β q / (δ.totient : ℝ) =
      betaCoprimeAPDiscrepancy N β δ (q / δ) b := by
  rw [betaResidueMass_eq_quotientSieve N β hdq hb]
  simp only [betaCoprimeAPDiscrepancy, Nat.mul_div_cancel' hdq]

/-- Direct conditional covariance bound from the two independently supplied
coprime-sieved AP bounds, in the normalization of the F87 beta-SW input. -/
theorem betaCovariance_abs_le_of_coprimeAP
    (N : Finset ℕ) (β : ℕ → ℝ) (q r : ℕ) (Eq Er : ℝ)
    (hEq : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaCoprimeAPDiscrepancy N β (q.gcd r) (q / q.gcd r) b| ≤ Eq)
    (hEr : ∀ b ∈ betaReducedResidues (q.gcd r),
      |betaCoprimeAPDiscrepancy N β (q.gcd r) (r / q.gcd r) b| ≤ Er) :
    |betaCovariance N β q r| ≤ ((q.gcd r).totient : ℝ) * Eq * Er := by
  apply betaCovariance_abs_le N β q r Eq Er
  · intro b hb
    rw [betaResidueMass_centered_eq_coprimeAPDiscrepancy N β
      (Nat.gcd_dvd_left q r) (Finset.mem_filter.mp hb).2]
    exact hEq b hb
  · intro b hb
    rw [betaResidueMass_centered_eq_coprimeAPDiscrepancy N β
      (Nat.gcd_dvd_right q r) (Finset.mem_filter.mp hb).2]
    exact hEr b hb

/-- A conditional aggregate consequence of independent beta-AP input at
each positive divisor of each sieving modulus. This is not a logarithmic
saving: no estimate for the resulting modulus sum is asserted. -/
theorem smoothWMain_sub_smoothUMain_abs_le_of_coprimeAP
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) (E : ℕ → ℕ → ℝ)
    (hE : ∀ q ∈ Q, ∀ d : ℕ, d ∣ q → 0 < d →
      ∀ b ∈ betaReducedResidues d,
        |betaCoprimeAPDiscrepancy N β d (q / d) b| ≤ E q d) :
    |smoothWMain M N Q β c a - smoothUMain M N Q β c a| ≤
      |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)| *
            (((q.gcd r).totient : ℝ) * E q (q.gcd r) * E r (q.gcd r)) := by
  rw [smoothWMain_sub_smoothUMain_eq_betaCovariance M N Q β c a hQ, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hδ := Nat.gcd_pos_of_pos_left r
    (Nat.pos_of_ne_zero (hQ q (Finset.mem_filter.mp hq).1))
  exact betaCovariance_abs_le_of_coprimeAP N β q r _ _
    (hE q (Finset.mem_filter.mp hq).1 _ (Nat.gcd_dvd_left q r) hδ)
    (hE r (Finset.mem_filter.mp hr).1 _ (Nat.gcd_dvd_right q r) hδ)

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
