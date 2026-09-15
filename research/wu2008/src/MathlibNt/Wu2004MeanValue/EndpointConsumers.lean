import MathlibNt.Wu2004MeanValue.MovingHighAggregate
import MathlibNt.Wu2004MeanValue.RealEndpoints

/-!
# Real moving endpoints and the manuscript's prime-endpoint domain

The natural product profile `a * floor(r(a))` exactly retains every prime
at the real endpoint `r(a)`. On every nonempty manuscript block both prime
endpoints are at least the source prime, hence at least 2. No extension of
the logarithmic integral below 2 is used.
-/

namespace Wu2004MeanValue

open Classical Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
open scoped BigOperators

noncomputable section

def realMovingAmplitude {q : ℕ} (A D : ℕ → ℂ) (r : ℕ → ℝ) (L U : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ a ∈ Ioc L U, A a * χ.1 (a : ZMod q) *
    ∑ p ∈ Icc 1 ⌊r a⌋₊, D p * χ.1 (p : ZMod q)

theorem realMovingAmplitude_eq_natural {q : ℕ} (A D : ℕ → ℂ) (r : ℕ → ℝ)
    (L U : ℕ) (χ : PrimitiveCharacter q) :
    realMovingAmplitude A D r L U χ =
      movingAmplitude A D (fun a => a * ⌊r a⌋₊) L U χ := by
  apply sum_congr rfl
  intro a ha
  have ha0 : 0 < a := (Nat.zero_le L).trans_lt (mem_Ioc.mp ha).1
  simp only [Nat.mul_div_cancel_left _ ha0]

theorem naturalProfile_le {x a : ℕ} {r : ℝ}
    (hr : 0 ≤ r) (har : (a : ℝ) * r ≤ x) :
    a * ⌊r⌋₊ ≤ x := by
  have h := (mul_le_mul_of_nonneg_left (Nat.floor_le hr)
    (Nat.cast_nonneg a)).trans har
  exact_mod_cast h

def realMovingHighSource (f : ℕ → ℂ) (r : ℕ → ℝ) (h x L U : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ Ioc ⌊lowConductor x B⌋₊ ⌊upperConductor x B⌋₊,
    (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
      ‖realMovingAmplitude (panSourceG f h) (panSourceD h) r L U χ‖

/-- Actual real prime cutoffs, common across the modulus sum, with no
rounding error and constants before the entire endpoint profile. -/
theorem chosen_high_source_real_moving_profile_log_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ B ε : ℝ, 0 ≤ B → 0 < ε →
      ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (h L U : ℕ) (f : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ a ∈ Ioc L U, 0 ≤ r a ∧ (a : ℝ) * r a ≤ x) →
      U ≤ x → (U : ℝ) ≤ (x : ℝ) ^ (1 - ε) →
      Real.log x ^ (2 * B) ≤ L → (∀ n, ‖f n‖ ≤ 1) →
      realMovingHighSource f r h x L U B ≤
        C * (x : ℝ) * Real.log x ^ (6 - B) +
          6984 * (Real.log x) ^ 2 / (x : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := chosen_high_source_common_moving_profile_log_saving
  refine ⟨C, hC, ?_⟩
  intro B ε hB hε
  obtain ⟨X₀, hX⟩ := hbound B ε hB hε
  refine ⟨X₀, ?_⟩
  intro x hx h L U f r hr hUx hUpow hL hf
  have hmain := hX x hx h L U f (fun a => a * ⌊r a⌋₊)
    (fun a ha => naturalProfile_le (hr a ha).1 (hr a ha).2) hUx hUpow hL hf
  simpa only [realMovingHighSource, realMovingAmplitude_eq_natural,
    movingHighSource] using hmain

def blockLower (H : ℝ) (m : ℕ) : ℝ := max H ((m : ℝ) ^ 2)

def blockUpper (H N a η : ℝ) (m : ℕ) : ℝ :=
  min (min (2 * H) ((m : ℝ) ^ (a / (a - 1)))) (η * N)

/-- On the manuscript's nonempty prime block, both actual li arguments lie
in the accepted domain, and both product endpoints are at most `2H`.
No asymptotic hypothesis or positive-power convention is needed for this
finite implication. -/
theorem block_prime_endpoint_domain (H N a η : ℝ) (m : ℕ) (hm : m.Prime)
    (hne : blockLower H m < blockUpper H N a η m) :
    (2 ≤ blockLower H m / m ∧
      (m : ℝ) * (blockLower H m / m) ≤ 2 * H) ∧
    (2 ≤ blockUpper H N a η m / m ∧
      (m : ℝ) * (blockUpper H N a η m / m) ≤ 2 * H) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.two_le
  have hm0 : (0 : ℝ) < m := by linarith
  have hlow : (m : ℝ) ^ 2 ≤ blockLower H m := le_max_right _ _
  have hupp : blockUpper H N a η m ≤ 2 * H :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hquot : 2 ≤ blockLower H m / m := by
    apply (le_div_iff₀ hm0).mpr
    nlinarith
  have hprod (t : ℝ) : (m : ℝ) * (t / m) = t := by field_simp
  rw [hprod, hprod]
  exact ⟨⟨hquot, hne.le.trans hupp⟩,
    ⟨hquot.trans (div_le_div_of_nonneg_right hne.le hm0.le), hupp⟩⟩

/-- The W1 tail's two prime endpoints are also at least 2 once
`x >= (2/eta)^2`, uniformly over `m <= sqrt(x)`. -/
theorem tail_prime_endpoint_domain (x η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hx : (2 / η) ^ 2 ≤ x) (m : ℕ) (hm : 0 < m)
    (hmx : (m : ℝ) ≤ Real.sqrt x) :
    2 ≤ η * x / m ∧ 2 ≤ x / m := by
  have hx0 : 0 ≤ x := (sq_nonneg _).trans hx
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : 2 / η ≤ Real.sqrt x :=
    (Real.le_sqrt (by positivity) hx0).mpr hx
  have hηroot : 2 ≤ η * Real.sqrt x := by
    have := (div_le_iff₀ hη).mp hsqrt
    nlinarith
  have hsquare := Real.sq_sqrt hx0
  have hfirst : 2 ≤ η * x / m := by
    apply (le_div_iff₀ hm0).mpr
    have h := mul_le_mul_of_nonneg_right hηroot (Real.sqrt_nonneg x)
    nlinarith
  exact ⟨hfirst, hfirst.trans (div_le_div_of_nonneg_right
    (by nlinarith : η * x ≤ x) hm0.le)⟩

end
end Wu2004MeanValue