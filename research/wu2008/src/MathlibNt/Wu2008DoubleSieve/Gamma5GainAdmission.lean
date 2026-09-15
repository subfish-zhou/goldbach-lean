import MathlibNt.Wu2008DoubleSieve.Gamma5GainGrid

/-!
# Admission of complete original-box microcells
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

theorem gamma5Gain_window_coordinate {N p : ℕ} {R A B : ℝ}
    (hR : 1 < R) (hp : p ∈ primeWindow N (R ^ A) (R ^ B)) :
    A ≤ gamma5MassCoordinate R p ∧ gamma5MassCoordinate R p < B := by
  have h := mem_primeWindow.mp hp
  have hR0 : 0 < R := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast h.1.pos
  constructor
  · apply (le_div_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using log_le_log (rpow_pos_of_pos hR0 _) h.2.2.1
  · apply (div_lt_iff₀ (log_pos hR)).mpr
    simpa only [log_rpow hR0] using (log_lt_log hp0 h.2.2.2)

theorem gamma5Gain_endpoint_admission {R t u : ℝ} (hR : 1 < R)
    (r : Gamma5GainRectangle) (ht : t ∈ Icc r.A r.B) (hu : u ∈ Icc r.C r.D) :
    R ^ (1 / 10 : ℝ) ≤ R ^ u ∧ R ^ u ≤ R ^ (1 / 2 : ℝ) ∧
      (R / R ^ u) ^ (1 / 10 : ℝ) ≤ R ^ t ∧ R ^ t ≤ (R / R ^ u) ^ (1 / 2 : ℝ) := by
  have hb := gamma5Gain_rectangle_bounds r
  have hR0 : 0 < R := by linarith
  have he : R / R ^ u = R ^ (1 - u) := by rw [rpow_sub hR0, rpow_one]
  rw [he, ← rpow_mul hR0.le, ← rpow_mul hR0.le]
  refine ⟨rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_⟩
  · linarith [gamma5Mass_constants.1, hb.2.2.2.2.2.2.2.2.1, hu.1]
  · linarith [hb.2.2.2.2.1, hu.2]
  · linarith [gamma5Mass_constants.1, r.lower, ht.1, hu.1, hb.2.1]
  · linarith [r.legal, ht.2, hu.2]

theorem gamma5Gain_coarse_label {i k N : ℕ} {δ Δ e : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hb : wuSourceBox k δ N i Δ V)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (r : Gamma5GainRectangle) (heA : e ≤ r.A - gamma5MassA)
    (hes : 2 * gamma5ClassicalS * e ≤ r.s - gamma5GainV r.A r.C)
    (hmesh : (i : ℝ) * gamma5GainStep (gamma5GainScale N δ V) Δ ≤ e)
    {x : Gamma5ClassicalLabel}
    (hd : x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : x.2.1 ∈ primeWindow N ((gamma5GainScale N δ V) ^ r.A) ((gamma5GainScale N δ V) ^ r.B))
    (hq : x.2.2 ∈ primeWindow N ((gamma5GainScale N δ V) ^ r.C) ((gamma5GainScale N δ V) ^ r.D)) :
    x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V) ∧
      gamma5GainV
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.s := by
  have hr := gamma5Gain_rectangle_bounds r
  have hpc := gamma5Gain_window_coordinate hR hp
  have hqc := gamma5Gain_window_coordinate hR hq
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  have hbase := gamma5Mass_support_geometry hN hδ (by linarith) hb hd
  have hV : ∀ j, 0 < V j := fun j =>
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _).trans_le (hb.2.2.2.2.1 j)
  have hlev := (reboxing_support_level_bounds (Q := (N : ℝ) ^ (1 / 2 - δ))
    (rpow_nonneg (Nat.cast_nonneg N) _) (by linarith : 0 < Δ) hV hd).1
  have hpR : (x.2.1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := by
    calc
      _ ≤ (gamma5GainScale N δ V) ^ r.B := hp'.2.2.2.le
      _ ≤ gamma5GainScale N δ V := by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hR.le hr.2.2.1.le
      _ ≤ _ := hlev
  have hqR : (x.2.2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := by
    calc
      _ ≤ (gamma5GainScale N δ V) ^ r.D := hq'.2.2.2.le
      _ ≤ gamma5GainScale N δ V := by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hR.le hr.2.2.2.1.le
      _ ≤ _ := hlev
  have hpd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hp'.1.one_le hpR
  have hqd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hq'.1.one_le hqR
  have hm : (i : ℝ) * log Δ / log (gamma5GainScale N δ V) ≤ e := by
    simpa only [gamma5GainStep, mul_div_assoc] using hmesh
  have hpa : gamma5MassA ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 := by
    linarith
  have hqb : gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 < gamma5ClassicalB := by
    linarith [r.upper]
  have hpq : x.2.1 < x.2.2 := by
    have hpow := rpow_le_rpow_of_exponent_le hR.le r.ordered.le
    exact_mod_cast hp'.2.2.2.trans_le (hpow.trans hq'.2.2.1)
  have hplo : wuLocalCutoff N δ x.1 gamma5ClassicalS ≤ (x.2.1 : ℝ) := by
    have hpB : gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 ≤ gamma5ClassicalB := by
      linarith [r.ordered, r.second, r.upper]
    have hh := (gamma5Mass_coordinate_mem_iff hbase.2.2.1 x.2.1).mpr ⟨hp'.1, hpa, hpB⟩
    exact ((LiLiuPrereqBuchstab.mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mp hh).2.1
  have hqhi : (x.2.2 : ℝ) < ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ gamma5ClassicalB := by
    apply (log_lt_log_iff (by exact_mod_cast hq'.1.pos)
      (rpow_pos_of_pos (by linarith : 0 < (N : ℝ) ^ (1 / 2 - δ) / x.1) _)).mp
    rw [log_rpow (by linarith : 0 < (N : ℝ) ^ (1 / 2 - δ) / x.1)]
    exact (div_lt_iff₀ (log_pos hbase.2.2.1)).mp hqb
  refine ⟨(gamma5Classical_mem_labels_iff hN hδ (by linarith) hb x).mpr
    ⟨hd, hp'.1, hq'.1, hp'.2.1, hq'.2.1, hplo, hpq, hqhi⟩, ?_⟩
  dsimp [gamma5GainV] at hes ⊢
  have hs : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
  nlinarith [hpd.2.trans hm, hqd.2.trans hm, hpc.1, hqc.1]

end Wu2008DoubleSieve
