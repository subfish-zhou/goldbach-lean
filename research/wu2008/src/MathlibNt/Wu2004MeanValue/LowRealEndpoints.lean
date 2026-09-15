import MathlibNt.Wu2004MeanValue.LowSource

/-! Actual real prime endpoints in the low primitive conductor source.
The scale `x` is natural; endpoints and the fixed product constant are real. -/

namespace Wu2004MeanValue
open Classical Finset
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.PanLow
open scoped BigOperators
noncomputable section

def lowPrimeSet (r : ℝ) (h : ℕ) : Finset ℕ :=
  (range (⌊r⌋₊ + 1)).filter (fun p => p.Prime ∧ p.Coprime h)

/-- The floor in the implementation introduces no endpoint error. -/
theorem mem_lowPrimeSet {r : ℝ} {h p : ℕ} (hr : 0 ≤ r) :
    p ∈ lowPrimeSet r h ↔ p.Prime ∧ p.Coprime h ∧ (p : ℝ) ≤ r := by
  simp only [lowPrimeSet, mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hr]
  tauto

def lowRealMovingSource (f : ℕ → ℂ)
    (r : (q : ℕ) → PrimitiveCharacter q → ℕ → ℝ) (S : Finset ℕ) (h Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 2 Q, (q.totient : ℝ)⁻¹ * ∑ χ : PrimitiveCharacter q,
    ‖∑ a ∈ S, f a * χ.1 (a : ZMod q) *
      ∑ p ∈ lowPrimeSet (r q χ a) h, χ.1 (p : ZMod q)‖

theorem lowRealMovingSource_eq_natural (f : ℕ → ℂ)
    (r : (q : ℕ) → PrimitiveCharacter q → ℕ → ℝ) (S : Finset ℕ) (h Q : ℕ) :
    lowRealMovingSource f r S h Q =
      lowMovingSource f (fun q χ a => ⌊r q χ a⌋₊) S h Q := by
  simp only [lowRealMovingSource, lowMovingSource, lowPrimeSet,
    sum_filter, coprimePrimePrefix]

/-- For every fixed saving, conductor exponent, coefficient bound and product
constant, the constants are uniform in the finite support, cofactor, weights,
and *independent* real endpoints `r(q, χ, a)`.

Only actual primes coprime to `h` occur; conductor one is excluded. Endpoints
may be any nonnegative reals (in particular the manuscript's endpoints ≥ 2).
This is the low-conductor source estimate, not the full weighted W1/W3 sum. -/
theorem low_source_real_moving (A b F K : ℝ)
    (hA : 0 < A) (hb : 0 ≤ b) (hF : 0 ≤ F) (_hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ, ∀ x ≥ x₀,
      ∀ (h Q : ℕ) (S : Finset ℕ) (f : ℕ → ℂ)
        (r : (q : ℕ) → PrimitiveCharacter q → ℕ → ℝ),
      1 ≤ h → (h : ℝ) ≤ Real.sqrt x →
      (∀ a ∈ S, 1 ≤ a ∧ (a : ℝ) ≤ Real.sqrt x) →
      (Q : ℝ) ≤ Real.log (x : ℝ) ^ b →
      (∀ a ∈ S, ‖f a‖ ≤ F) →
      (∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S,
        0 ≤ r q χ a ∧ (a : ℝ) * r q χ a ≤ K * x) →
      lowRealMovingSource f r S h Q ≤ C * x / Real.log (x : ℝ) ^ A := by
  obtain ⟨C, hC, N₀, hbound⟩ := low_source_nat_moving A b F hA hb hF
  let H : ℕ := max 1 ⌈K⌉₊
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hKH : K ≤ (H : ℝ) :=
    (Nat.le_ceil K).trans (by exact_mod_cast (le_max_right 1 ⌈K⌉₊))
  refine ⟨C * H, by positivity, max 3 N₀, ?_⟩
  intro x hx h Q S f r hh hhx hS hQ hf hr
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hxN : x ≤ H * x := Nat.le_mul_of_pos_left x (by omega)
  have hxNR : (x : ℝ) ≤ (H * x : ℕ) := by exact_mod_cast hxN
  have hN1 : (1 : ℝ) ≤ (H * x : ℕ) := by
    exact_mod_cast (show 1 ≤ H * x by omega)
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogs : Real.log (x : ℝ) ≤ Real.log (H * x : ℕ) :=
    Real.log_le_log hx0 hxNR
  have hroot : Real.sqrt x ≤ (H * x : ℕ) ^ (2 / 3 : ℝ) := by
    calc
      _ ≤ Real.sqrt (H * x : ℕ) := Real.sqrt_le_sqrt hxNR
      _ ≤ _ := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hU : (⌊Real.sqrt x⌋₊ : ℝ) ≤ (H * x : ℕ) ^ (2 / 3 : ℝ) :=
    (Nat.floor_le (Real.sqrt_nonneg _)).trans hroot
  have hSU : S ⊆ Icc 1 ⌊Real.sqrt x⌋₊ := by
    intro a ha
    exact mem_Icc.mpr ⟨(hS a ha).1, Nat.le_floor (hS a ha).2⟩
  have hQN : (Q : ℝ) ≤ Real.log (H * x : ℕ) ^ b :=
    hQ.trans (Real.rpow_le_rpow hlogx.le hlogs hb)
  have ht : ∀ q ∈ Icc 2 Q, ∀ χ : PrimitiveCharacter q, ∀ a ∈ S,
      ⌊r q χ a⌋₊ ≤ (H * x) / a := by
    intro q hq χ a ha
    have ha0 : 0 < a := by have := (hS a ha).1; omega
    apply (Nat.le_div_iff_mul_le ha0).mpr
    have hp := (mul_le_mul_of_nonneg_left (Nat.floor_le (hr q hq χ a ha).1)
      (Nat.cast_nonneg a)).trans ((hr q hq χ a ha).2.trans
        (mul_le_mul_of_nonneg_right hKH hx0.le))
    have hp' : a * ⌊r q χ a⌋₊ ≤ H * x := by exact_mod_cast hp
    simpa only [Nat.mul_comm] using hp'
  rw [lowRealMovingSource_eq_natural]
  refine (hbound (H * x) (((le_max_right _ _).trans hx).trans hxN)
    h ⌊Real.sqrt x⌋₊ Q S f (fun q χ a => ⌊r q χ a⌋₊)
    hh (hhx.trans (Real.sqrt_le_sqrt hxNR)) hU hSU hQN hf ht).trans ?_
  calc
    C * (H * x : ℕ) / Real.log (H * x : ℕ) ^ A ≤
        C * (H * x : ℕ) / Real.log (x : ℝ) ^ A :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlogx A)
        (Real.rpow_le_rpow hlogx.le hlogs hA.le)
    _ = _ := by push_cast; ring

end
end Wu2004MeanValue