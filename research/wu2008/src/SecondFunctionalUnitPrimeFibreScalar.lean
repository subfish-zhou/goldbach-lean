import SecondFunctionalUnitPrimeFibreFinite

open scoped BigOperators Classical
namespace SecondFunctionalUnitPrimeFibre
open Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset

 theorem scaled_main {R : ℝ} (hR : 1 < R) (t v : ℝ) :
    (log R * R ^ (-v)) * (R ^ t / (t * log R)) = R ^ (t-v) / t := by
  have hR0 : 0 < R := by linarith
  rw [sub_eq_add_neg, rpow_add hR0]
  field_simp [ne_of_gt (log_pos hR)]

 theorem scaled_prefix_threshold (a tau : ℝ) (ha : 0 < a) (ht : 0 < tau) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ t v : ℝ, a ≤ t →
      |log R * R ^ (-v) * primePi (R ^ t) - R ^ (t-v) / t| ≤
        tau * (R ^ (t-v) / t) := by
  obtain ⟨T,hT,h⟩ := secondFunctional_primePrefix_power_threshold a ha tau ht
  refine ⟨T,hT,?_⟩
  intro R hRT t v hat
  have hR := hT.trans_le hRT
  have hR0 : 0 ≤ R := by linarith
  have he := h R hRT t hat
  rw [secondFunctional_primePrefix_card (rpow_nonneg hR0 _)] at he
  have hs : 0 ≤ log R * R ^ (-v) := mul_nonneg (log_pos hR).le (rpow_nonneg hR0 _)
  have hh := mul_le_mul_of_nonneg_left he hs
  rw [← abs_of_nonneg hs, ← abs_mul] at hh
  rw [abs_of_nonneg hs] at hh
  have hh' : |log R * R ^ (-v) * primePi (R ^ t) -
      (log R * R ^ (-v)) * (R ^ t / (t * log R))| ≤
      tau * ((log R * R ^ (-v)) * (R ^ t / (t * log R))) := by
    simpa only [mul_sub, mul_assoc, mul_left_comm] using hh
  simpa only [scaled_main hR] using hh'

 theorem weight_nonneg {R : ℝ} (hR : 1 < R) (v ell b : ℝ) :
    0 ≤ weight R v ell b := by
  exact mul_nonneg (mul_nonneg (log_pos hR).le (rpow_nonneg (by linarith) _))
    (count_nonneg _ _ _ _)

 theorem weight_le_scaled_prefix {R v ell b : ℝ} (hR : 1 < R) :
    weight R v ell b ≤ log R * R ^ (-v) * primePi (R ^ min v b) := by
  have hs : fibre (R ^ ell) (R ^ min v b) ⊆ primesIcc 0 (R ^ min v b) := filter_subset _ _
  have hh : count R v ell b ≤ ((primesIcc 0 (R ^ min v b)).card : ℝ) := by
    unfold count
    exact_mod_cast card_le_card hs
  rw [secondFunctional_primePrefix_card (rpow_nonneg (by linarith : 0 ≤ R) _)] at hh
  exact mul_le_mul_of_nonneg_left hh
    (mul_nonneg (log_pos hR).le (rpow_nonneg (by linarith) _))

 theorem decay_le_one {R x : ℝ} (hR : 1 < R) (hx : x ≤ 0) : R ^ x ≤ 1 := by
  simpa using rpow_le_rpow_of_exponent_le hR.le hx

 theorem ratio_le {a t d : ℝ} (ha : 0 < a) (ht : a ≤ t) (hd : 0 ≤ d) :
    d / t ≤ d / a := div_le_div_of_nonneg_left hd ha ht

/-- One threshold precedes every fibre endpoint, and both absolute endpoint errors are retained. -/
theorem scalar_threshold (a tau : ℝ) (ha : 0 < a) (ht : 0 < tau) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ v ell b : ℝ, a ≤ ell → ell ≤ b →
      (0 ≤ weight R v ell b ∧ weight R v ell b ≤ (1+tau)/a) ∧
      (ell ≤ v →
        |weight R v ell b - (R ^ (min v b-v)/(min v b) - R ^ (ell-v)/ell)| ≤
          (tau/a) * (R ^ (min v b-v) + R ^ (ell-v)) ∧
        (tau/a) * (R ^ (min v b-v) + R ^ (ell-v)) ≤ 2*tau/a) ∧
      (∀ eta : ℝ, 0 < eta → ell+eta ≤ v → v ≤ b →
        |weight R v ell b - 1/v| ≤ 2*tau/a + R ^ (-eta)/a) ∧
      (∀ eta : ℝ, 0 < eta → b+eta ≤ v →
        weight R v ell b ≤ (1+tau) * R ^ (-eta)/b) := by
  obtain ⟨T,hT,h⟩ := scaled_prefix_threshold a tau ha ht
  refine ⟨T,hT,?_⟩
  intro R hRT v ell b hel heb
  have hR := hT.trans_le hRT
  have hR0 : 0 ≤ R := by linarith
  have hpos (x : ℝ) : 0 ≤ R ^ x := rpow_nonneg hR0 x
  have hnn := weight_nonneg hR v ell b
  have feasible (hv : ell ≤ v) :
      |weight R v ell b - (R ^ (min v b-v)/(min v b) - R ^ (ell-v)/ell)| ≤
        (tau/a) * (R ^ (min v b-v) + R ^ (ell-v)) ∧
      (tau/a) * (R ^ (min v b-v) + R ^ (ell-v)) ≤ 2*tau/a := by
    have hu : a ≤ min v b := hel.trans (le_min hv heb)
    have he1 := h R hRT (min v b) v hu
    have he2 := h R hRT ell v hel
    have he := abs_sub_le (log R * R ^ (-v) * primePi (R ^ min v b) - R ^ (min v b-v)/min v b)
      0 (log R * R ^ (-v) * primePi (R ^ ell) - R ^ (ell-v)/ell)
    simp only [sub_zero, zero_sub, abs_neg] at he
    have hw : weight R v ell b - (R ^ (min v b-v)/min v b - R ^ (ell-v)/ell) =
        (log R * R ^ (-v) * primePi (R ^ min v b) - R ^ (min v b-v)/min v b) -
        (log R * R ^ (-v) * primePi (R ^ ell) - R ^ (ell-v)/ell) := by
      rw [weight, count_feasible hR hv heb]; ring
    have hd1 := mul_le_mul_of_nonneg_left (ratio_le ha hu (hpos (min v b-v))) ht.le
    have hd2 := mul_le_mul_of_nonneg_left (ratio_le ha hel (hpos (ell-v))) ht.le
    constructor
    · rw [hw]
      calc
        _ ≤ tau * (R ^ (min v b-v)/min v b) + tau * (R ^ (ell-v)/ell) := by linarith
        _ ≤ (tau/a) * (R ^ (min v b-v) + R ^ (ell-v)) := by
          calc
            _ ≤ tau * (R ^ (min v b-v)/a) + tau * (R ^ (ell-v)/a) := add_le_add hd1 hd2
            _ = _ := by ring
    · have hh1 := decay_le_one hR (sub_nonpos.mpr (min_le_left v b))
      have hh2 := decay_le_one hR (sub_nonpos.mpr hv)
      have hh := mul_le_mul_of_nonneg_left (add_le_add hh1 hh2) (div_nonneg ht.le ha.le)
      calc
        _ ≤ (tau/a) * (1+1) := hh
        _ = _ := by ring
  have global : weight R v ell b ≤ (1+tau)/a := by
    by_cases hv : ell ≤ v
    · have hu : a ≤ min v b := hel.trans (le_min hv heb)
      have he := (abs_le.mp (h R hRT (min v b) v hu)).2
      have hbnd := weight_le_scaled_prefix (v := v) (ell := ell) (b := b) hR
      have hr := ratio_le ha hu (hpos (min v b-v))
      have hd := div_le_div_of_nonneg_right
        (decay_le_one hR (sub_nonpos.mpr (min_le_left v b))) ha.le
      have hh := mul_le_mul_of_nonneg_left (hr.trans hd) (by linarith : 0 ≤ 1+tau)
      calc
        _ ≤ (1+tau) * (R ^ (min v b-v)/min v b) := by linarith
        _ ≤ (1+tau) * (1/a) := hh
        _ = _ := by ring
    · rw [weight_empty hR (le_of_not_ge hv)]
      positivity
  refine ⟨⟨hnn,global⟩, feasible, ?_, ?_⟩
  · intro eta heta hv hb
    have hvl : ell ≤ v := by linarith
    have hf := (feasible hvl).1.trans (feasible hvl).2
    rw [min_eq_left hb, sub_self, rpow_zero] at hf
    have hd : R ^ (ell-v)/ell ≤ R ^ (-eta)/a :=
      (ratio_le ha hel (hpos (ell-v))).trans
        (div_le_div_of_nonneg_right (rpow_le_rpow_of_exponent_le hR.le (by linarith)) ha.le)
    have he := abs_sub_le (weight R v ell b) (1/v - R ^ (ell-v)/ell) (1/v)
    have heq : 1/v - R ^ (ell-v)/ell - 1/v = -(R ^ (ell-v)/ell) := by ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg (hpos _) (ha.le.trans hel))] at he
    linarith
  · intro eta heta hv
    have hb : b ≤ v := by linarith
    have he := (abs_le.mp (h R hRT b v (hel.trans heb))).2
    have hbnd := weight_le_scaled_prefix (v := v) (ell := ell) (b := b) hR
    rw [min_eq_right hb] at hbnd
    have hd : R ^ (b-v)/b ≤ R ^ (-eta)/b :=
      div_le_div_of_nonneg_right (rpow_le_rpow_of_exponent_le hR.le (by linarith))
        (ha.le.trans (hel.trans heb))
    calc
      _ ≤ (1+tau) * (R ^ (b-v)/b) := by linarith
      _ ≤ (1+tau) * (R ^ (-eta)/b) := mul_le_mul_of_nonneg_left hd (by linarith)
      _ = _ := by ring

 theorem scalar_tenth (tau : ℝ) (ht : 0 < tau) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ v ell b : ℝ,
      1/10 ≤ ell → ell ≤ b →
      (0 ≤ weight R v ell b ∧ weight R v ell b ≤ (1+tau)/(1/10)) ∧
      (ell ≤ v →
        |weight R v ell b - (R ^ (min v b-v)/(min v b) - R ^ (ell-v)/ell)| ≤
          (tau/(1/10)) * (R ^ (min v b-v) + R ^ (ell-v))) := by
  obtain ⟨T,hT,h⟩ := scalar_threshold (1/10) tau (by norm_num) ht
  refine ⟨T,hT,?_⟩
  intro R hR v ell b hel heb
  exact ⟨(h R hR v ell b hel heb).1, fun hv => (h R hR v ell b hel heb).2.1 hv |>.1⟩
end SecondFunctionalUnitPrimeFibre
