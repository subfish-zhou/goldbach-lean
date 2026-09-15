import MathlibNt.Wu2004MeanValue.AllSourceAP
import MathlibNt.Wu2004MeanValue.RealScale
import MathlibNt.Wu2004MeanValue.ActualResidueSup

/-!
# Actual weighted common-profile distribution at real scales

The complete natural-scale AP producer is consumed with normalized
coefficients. The residue supremum is attained separately at each modulus;
the source coefficients and prime profile remain common across moduli.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open scoped BigOperators Topology
noncomputable section

theorem actualAPSum_mul_coeff (S : Finset ℕ) (f r : ℕ → ℝ)
    (c : ℝ) (d b : ℕ) :
    actualAPSum S (fun m => c * f m) r d b = c * actualAPSum S f r d b := by
  simp only [actualAPSum, mul_sum]
  apply sum_congr rfl
  intro m _
  split_ifs <;> ring

/-- Real ambient scale, a fixed coefficient bound, and a fixed product
constant. All analytic constants precede the entire source and profile. -/
theorem common_profile_weighted_real (A F K : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) (_hK : 0 < K) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ → ℕ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |actualAPSum S f r d (b d)|) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hbound⟩ := common_profile_unit_natural A hA
  have hF1 : 0 < F + 1 := by linarith
  refine ⟨B + 1, (F + 1) * (C * (max 1 K + 1)), by positivity, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (max 1 K + 1),
    eventually_ge_atTop (Real.exp ((2 : ℝ) ^ B)), eventually_ge_atTop (N₀ : ℝ)]
    with x hx3 hxK hxexp hxN₀
  intro Q hQ S f r b hS hf hr hb
  obtain ⟨hxN, hKN, _⟩ := commonScale_bounds K x (by linarith)
  have hN₀ : N₀ ≤ commonScale K x := by exact_mod_cast hxN₀.trans hxN
  have hQN : (Q : ℝ) ≤ Real.sqrt (commonScale K x) /
      Real.log (commonScale K x : ℝ) ^ B :=
    hQ.trans (commonScale_cutoff K x B hB.le hx3 hxK hxexp)
  let g : ℕ → ℝ := fun m => f m / (F + 1)
  have hg : ∀ m ∈ S, |g m| ≤ 1 := by
    intro m hm
    dsimp [g]
    rw [abs_div, abs_of_pos hF1]
    exact (div_le_iff₀ hF1).mpr (by have := hf m hm; linarith)
  have hfg : f = fun m => (F + 1) * g m := by
    funext m
    dsimp [g]
    field_simp
  have hnatural := hbound (commonScale K x) hN₀ Q hQN S g r b
    (fun m hm => ⟨(hS m hm).1, (hS m hm).2.trans (Real.sqrt_le_sqrt hxN)⟩)
    hg (fun m hm => ⟨(hr m hm).1, (hr m hm).2.trans hKN⟩) hb
  calc
    _ = (F + 1) * ∑ d ∈ Icc 1 Q,
        wuModulusWeight d * |actualAPSum S g r d (b d)| := by
      conv_lhs => rw [hfg]
      simp only [actualAPSum_mul_coeff, abs_mul, abs_of_pos hF1, mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ (F + 1) * (C * (commonScale K x : ℝ) /
        Real.log (commonScale K x : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left hnatural hF1.le
    _ ≤ (F + 1) * ((C * (max 1 K + 1)) * x / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_left
        (commonScale_log_saving K x A C (by linarith) hA.le hC.le) hF1.le
    _ = _ := by ring

/-- The true reduced-residue supremum remains inside the Wu-weighted
modulus sum. No modulus-dependent prime profile is introduced. -/
theorem common_profile_residueSup_real (A F K : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) (hK : 0 < K) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ (S : Finset ℕ) (f r : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * actualAPResidueSup S f r d) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨B, C, hB, hC, x₀, hbound⟩ :=
    common_profile_weighted_real A F K hA hF hK
  refine ⟨B, C, hB, hC, x₀, ?_⟩
  intro x hx Q hQ S f r hS hf hr
  obtain ⟨b, hb, heq⟩ := actualAPResidueSup_sum_attained S f r Q wuModulusWeight
  rw [heq]
  exact hbound x hx Q hQ S f r b hS hf hr hb

/-- On positive source coordinates the quotient profile gives the literal
fixed product endpoint, with no change to the prime count or li main term. -/
theorem actualAPSum_div_profile (S : Finset ℕ) (f : ℕ → ℝ)
    (y : ℝ) (d b : ℕ) (hS : ∀ m ∈ S, 1 ≤ m) :
    actualAPSum S f (fun m => y / m) d b =
      ∑ m ∈ S, if m.Coprime d then f m * ebar y d b m else 0 := by
  unfold actualAPSum
  apply sum_congr rfl
  intro m hm
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by have := hS m hm; omega)
  have hprod : (m : ℝ) * (y / m) = y := by field_simp
  rw [hprod]

/-- The manuscript's W1 tail endpoints `x/m` and `eta*x/m`.
Both retain a genuine reduced-residue supremum inside the weighted sum.
The threshold ensures that both prime endpoints are at least two. -/
theorem common_profile_W1_tail_residueSup (A F η : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt x) →
      (∀ m ∈ S, |f m| ≤ F) →
      ((∑ d ∈ Icc 1 Q, wuModulusWeight d *
          actualAPResidueSup S f (fun m => x / m) d) ≤ C * x / Real.log x ^ A) ∧
      ((∑ d ∈ Icc 1 Q, wuModulusWeight d *
          actualAPResidueSup S f (fun m => η * x / m) d) ≤ C * x / Real.log x ^ A) := by
  obtain ⟨B, C, hB, hC, x₁, hbound⟩ :=
    common_profile_residueSup_real A F 1 hA hF (by norm_num)
  refine ⟨B, C, hB, hC, max x₁ ((2 / η) ^ 2), ?_⟩
  intro x hx Q hQ S f hS hf
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxη : (2 / η) ^ 2 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ x := (sq_nonneg _).trans hxη
  have hdomain (m : ℕ) (hm : m ∈ S) :
      2 ≤ η * x / m ∧ 2 ≤ x / m :=
    tail_prime_endpoint_domain x η hη hη1 hxη m
      (by have := (hS m hm).1; omega) (hS m hm).2
  have hprod (y : ℝ) (m : ℕ) (hm : m ∈ S) : (m : ℝ) * (y / m) = y := by
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by have := (hS m hm).1; omega)
    field_simp
  constructor
  · apply hbound x hx₁ Q hQ S f (fun m => x / m) hS hf
    intro m hm
    exact ⟨(hdomain m hm).2, by rw [hprod x m hm, one_mul]⟩
  · apply hbound x hx₁ Q hQ S f (fun m => η * x / m) hS hf
    intro m hm
    refine ⟨(hdomain m hm).1, ?_⟩
    rw [hprod (η * x) m hm, one_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hη1 hx0

/-- The literal manuscript block profiles, at the correct ambient scale
`2*H`. All constants precede `N,a,eta`; no restriction `N ≤ 2*H` is used.
Only prime source coordinates in nonempty blocks are assumed. -/
theorem common_profile_block_residueSup (A F : ℝ)
    (hA : 0 < A) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ X₀ : ℝ,
      ∀ H : ℝ, X₀ ≤ 2 * H →
      ∀ (N a η : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt (2 * H) / Real.log (2 * H) ^ B →
      ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ m ∈ S, m.Prime ∧ blockLower H m < blockUpper H N a η m) →
      (∀ m ∈ S, |f m| ≤ F) →
      ((∑ d ∈ Icc 1 Q, wuModulusWeight d *
          actualAPResidueSup S f (fun m => blockLower H m / m) d) ≤
        C * (2 * H) / Real.log (2 * H) ^ A) ∧
      ((∑ d ∈ Icc 1 Q, wuModulusWeight d *
          actualAPResidueSup S f (fun m => blockUpper H N a η m / m) d) ≤
        C * (2 * H) / Real.log (2 * H) ^ A) := by
  obtain ⟨B, C, hB, hC, X₀, hbound⟩ :=
    common_profile_residueSup_real A F 1 hA hF (by norm_num)
  refine ⟨B, C, hB, hC, X₀, ?_⟩
  intro H hH N a η Q hQ S f hS hf
  have hsource : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.sqrt (2 * H) := by
    intro m hm
    exact ⟨(hS m hm).1.one_le, block_source_sqrt_domain H N a η m (hS m hm).2⟩
  constructor
  · apply hbound (2 * H) hH Q hQ S f (fun m => blockLower H m / m) hsource hf
    intro m hm
    simpa only [one_mul] using
      (block_prime_endpoint_domain H N a η m (hS m hm).1 (hS m hm).2).1
  · apply hbound (2 * H) hH Q hQ S f (fun m => blockUpper H N a η m / m) hsource hf
    intro m hm
    simpa only [one_mul] using
      (block_prime_endpoint_domain H N a η m (hS m hm).1 (hS m hm).2).2

end
end Wu2004MeanValue
