import MathlibNt.Wu2008DoubleSieve.OmegaWeighted
import MathlibNt.Wu2008DoubleSieve.SingleUpperCounts

namespace Wu2008DoubleSieve.HighSix
open Finset Real
open scoped Classical

noncomputable def s : ℝ := 13 / 5
noncomputable def S : ℝ := 179 / 50
noncomputable def alpha : ℝ := 100 / 1327
noncomputable def left : ℝ := 807 / 2654
noncomputable def right : ℝ := 827 / 2654
noncomputable def P (N : ℕ) : Finset ℕ := primeWindow N ((N : ℝ)^left) ((N : ℝ)^right)
noncomputable def R (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ := (N : ℝ)^(1/2-δ)/(p : ℝ)
noncomputable def z (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ := wuLocalCutoff N δ p S
noncomputable def w (N : ℕ) (δ : ℝ) (p : ℕ) : ℝ := wuLocalCutoff N δ p s

/-- Exact input arithmetic, checked in Lean rather than by a numerical certificate. -/
theorem parameters : 0 < alpha ∧ alpha < left ∧ left < right ∧
    1 - 1/s - 2/S = 132/2327 ∧ S-S/s = 716/325 ∧ 2 ≤ S-S/s := by
  norm_num [alpha, left, right, s, S]

theorem ratio_bounds {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    1 < R N δ p ∧ R N δ p ≤ (N : ℝ)^(alpha*s) ∧
      (N : ℝ)^(1/2-δ-right) ≤ R N δ p := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  obtain ⟨hpp, _, hpl, hpr⟩ := mem_primeWindow.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlo : (N : ℝ)^(1/2-δ-right) ≤ R N δ p := by
    apply (le_div_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ)^(1/2-δ-right) * (N : ℝ)^right :=
        mul_le_mul_of_nonneg_left hpr.le (by positivity)
      _ = (N : ℝ)^(1/2-δ) := by rw [← rpow_add hN0]; congr 1; ring
  refine ⟨?_, ?_, hlo⟩
  · exact (one_lt_rpow hN1 (by dsimp [right]; linarith)).trans_le hlo
  · apply (div_le_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ)^(alpha*s+left) :=
        rpow_le_rpow_of_exponent_le hN1.le (by norm_num [alpha, s, left]; linarith)
      _ = (N : ℝ)^(alpha*s) * (N : ℝ)^left := rpow_add hN0 _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hpl (by positivity)

/-- The original half-open windows have the required strict prime separation. -/
theorem cutoff_geometry {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    1 < z N δ p ∧ z N δ p ≤ w N δ p ∧
      w N δ p ≤ (N : ℝ)^alpha ∧ (N : ℝ)^alpha < (p : ℝ) := by
  have hr := ratio_bounds hN hδ hδhi hp
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  refine ⟨one_lt_rpow hr.1 (by norm_num [S]),
    rpow_le_rpow_of_exponent_le hr.1.le (by norm_num [S, s]), ?_, ?_⟩
  · calc
      w N δ p ≤ ((N : ℝ)^(alpha*s))^(1/s) :=
        rpow_le_rpow (le_of_lt hr.1 |>.trans' zero_le_one) hr.2.1 (by norm_num [s])
      _ = (N : ℝ)^alpha := by
        rw [← rpow_mul hN0]
        congr 1
        norm_num [alpha, s]
  · exact (rpow_lt_rpow_of_exponent_lt hN1 (by norm_num [alpha, left])).trans_le
      (mem_primeWindow.mp hp).2.2.1

theorem inner_lt_outer {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) : q < p := by
  have hg := cutoff_geometry hN hδ hδhi hp
  exact_mod_cast (mem_primeWindow.mp hq).2.2.2.trans_le (hg.2.2.1.trans hg.2.2.2.le)

/-- The repeated-prime lane is genuinely empty, before any analytic estimate. -/
theorem repeated_zero {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    wuOmegaRepeated N p δ s S = 0 := by
  apply sum_eq_zero
  intro q hq
  obtain ⟨hq, hd⟩ := mem_filter.mp hq
  have hlt := inner_lt_outer hN hδ hδhi hp hq
  have hqp := (mem_primeWindow.mp hq).1
  rcases (Nat.dvd_prime (mem_primeWindow.mp hp).1).mp hd with he | he
  · exact False.elim (hqp.ne_one he)
  · exact False.elim (Nat.ne_of_lt hlt he)

/-- Adding q to the modulus is justified only at or above the strict cutoff. -/
theorem source_pair_count {N p q : ℕ} {v : ℝ} (hq : q.Prime) (hv : v ≤ (q : ℝ)) :
    sourceSieveCount N (p*q) (p*N) v = sourceSieveCount N (p*q) ((p*q)*N) v := by
  have hc : sourceSieveCarrier N (p*q) (p*N) v =
      sourceSieveCarrier N (p*q) ((p*q)*N) v := by
    ext a
    simp only [sourceSieveCarrier, mem_filter]
    rw [show p*q*N = q*(p*N) by ring,
      SingleUpperCounts.sifted_selected_modulus hq hv]
  exact congrArg (fun t : Finset ℕ => (t.card : ℤ)) hc

/-- A fixed positive exponent works for every inner prime and every permitted delta. -/
theorem inner_lower_cutoff {N p : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N) :
    (N : ℝ)^(1/25 : ℝ) ≤ z N δ p := by
  have hr := ratio_bounds hN hδ hδhi hp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    _ ≤ (N : ℝ)^((1/2-δ-right)*(1/S)) :=
      rpow_le_rpow_of_exponent_le hN1 (by norm_num [right, S]; linarith)
    _ = ((N : ℝ)^(1/2-δ-right))^(1/S) :=
      rpow_mul (Nat.cast_nonneg N) _ _
    _ ≤ _ := rpow_le_rpow (by positivity) hr.2.2 (by norm_num [S])

/-- The lower Rosser condition concerns pq, not the square of the outer prime. -/
theorem pair_level_geometry {N p q : ℕ} {δ : ℝ} (hN : 2 ≤ N)
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hp : p ∈ P N)
    (hq : q ∈ primeWindow N (z N δ p) (w N δ p)) :
    (z N δ p)^2 ≤ (N : ℝ)^(1/2-δ)/(p*q : ℕ) ∧
      z N δ p ≤ (wuVariableRosserLevel N δ (p*q) : ℝ) := by
  have hr := ratio_bounds hN hδ hδhi hp
  have hg := cutoff_geometry hN hδ hδhi hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  have hR0 : 0 < R N δ p := zero_lt_one.trans hr.1
  have hzq : (z N δ p)^2 * (q : ℝ) ≤ R N δ p := by
    calc
      _ ≤ (z N δ p)^2 * w N δ p :=
        mul_le_mul_of_nonneg_left (mem_primeWindow.mp hq).2.2.2.le (sq_nonneg _)
      _ = (R N δ p)^(2/S+1/s) := by
        change ((R N δ p)^(1/S))^2 * (R N δ p)^(1/s) = _
        rw [pow_two, ← rpow_add hR0, ← rpow_add hR0]
        congr 1
        ring
      _ ≤ (R N δ p)^(1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hr.1.le (by norm_num [S, s])
      _ = _ := rpow_one _
  have hzz : (z N δ p)^2 ≤ (N : ℝ)^(1/2-δ)/(p*q : ℕ) := by
    rw [Nat.cast_mul, ← div_div]
    change (z N δ p)^2 ≤ R N δ p / (q : ℝ)
    exact (le_div_iff₀ hq0).mpr hzq
  refine ⟨hzz, ?_⟩
  have hfloor : (N : ℝ)^(1/2-δ)/(p*q : ℕ) <
      (wuVariableRosserLevel N δ (p*q) : ℝ) := by
    unfold wuVariableRosserLevel
    exact_mod_cast Nat.lt_floor_add_one ((N : ℝ)^(1/2-δ)/(p*q : ℕ))
  exact (show z N δ p ≤ (z N δ p)^2 by nlinarith [hg.1]).trans (hzz.trans hfloor.le)

end Wu2008DoubleSieve.HighSix
