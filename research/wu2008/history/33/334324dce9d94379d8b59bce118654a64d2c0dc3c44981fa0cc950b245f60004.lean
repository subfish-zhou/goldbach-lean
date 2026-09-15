import MathlibNt.Wu2008DoubleSieve.Gamma6BaseCount
import MathlibNt.Wu2008DoubleSieve.Gamma5GainMain

namespace Wu2008DoubleSieve

open Finset Set Real Filter
open scoped Classical Topology

structure Gamma6GainRectangle where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  s : ℝ
  lower : gamma5MassA < A
  first : A < B
  firstUpper : B < gamma6BaseB
  secondLower : gamma6BaseC < C
  second : C < D
  upper : D < gamma6BaseF
  rightEnd : gamma5GainV A C < s
  parameter : s < 3

theorem gamma6Gain_domain_bounds {t u : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) (hu : u ∈ Icc gamma6BaseC gamma6BaseF) :
    0 < t ∧ 0 < u ∧ t < u ∧ t < 1 ∧ u < 1 ∧
      2 * u < 1 ∧ u + 2 * t < 1 ∧
      1 < gamma5GainV t u ∧ gamma5GainV t u < 2 ∧ 1 / 4 ≤ 1 - t - u := by
  norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB, gamma6BaseC, gamma6BaseF] at ht hu
  dsimp [gamma5GainV, gamma5ClassicalS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith [ht.1, ht.2, hu.1, hu.2]

theorem gamma6Gain_rectangle_bounds (r : Gamma6GainRectangle) :
    0 < r.A ∧ 0 < r.C ∧ r.B < r.C ∧ r.B < 1 ∧ r.D < 1 ∧
      2 * r.D < 1 ∧ r.D + 2 * r.B < 1 ∧ 1 < r.s := by
  have h := gamma6Gain_domain_bounds ⟨r.lower.le, (r.first.trans r.firstUpper).le⟩
    ⟨r.secondLower.le, (r.second.trans r.upper).le⟩
  have h' := gamma6Gain_domain_bounds ⟨(r.lower.trans r.first).le, r.firstUpper.le⟩
    ⟨(r.secondLower.trans r.second).le, r.upper.le⟩
  exact ⟨h.1, h.2.1, (r.firstUpper.trans gamma6Base_constants.2.2.1).trans r.secondLower,
    h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1.trans r.rightEnd⟩

theorem gamma6Gain_endpoint_admission {R t u : ℝ} (hR : 1 < R)
    (r : Gamma6GainRectangle) (ht : t ∈ Icc r.A r.B) (hu : u ∈ Icc r.C r.D) :
    R ^ (1 / 10 : ℝ) ≤ R ^ u ∧ R ^ u ≤ R ^ (1 / 2 : ℝ) ∧
      (R / R ^ u) ^ (1 / 10 : ℝ) ≤ R ^ t ∧ R ^ t ≤ (R / R ^ u) ^ (1 / 2 : ℝ) := by
  have hb := gamma6Gain_rectangle_bounds r
  have hR0 : 0 < R := by linarith
  have he : R / R ^ u = R ^ (1 - u) := by rw [rpow_sub hR0, rpow_one]
  rw [he, ← rpow_mul hR0.le, ← rpow_mul hR0.le]
  refine ⟨rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_,
    rpow_le_rpow_of_exponent_le hR.le ?_⟩
  · have hc : 1 / 10 < gamma6BaseC := by norm_num [gamma6BaseC]
    linarith [r.secondLower, hu.1]
  · linarith [hb.2.2.2.2.2.1, hu.2]
  · linarith [gamma6Base_constants.1, r.lower, ht.1, hu.1, hb.2.1]
  · linarith [hb.2.2.2.2.2.2.1, ht.2, hu.2]

theorem gamma6Gain_coarse_label {i k N : ℕ} {δ Δ e : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hb : wuSourceBox k δ N i Δ V)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (r : Gamma6GainRectangle) (heA : e ≤ r.A - gamma5MassA)
    (heC : e ≤ r.C - gamma6BaseC)
    (hes : 2 * gamma5ClassicalS * e ≤ r.s - gamma5GainV r.A r.C)
    (hmesh : (i : ℝ) * gamma5GainStep (gamma5GainScale N δ V) Δ ≤ e)
    {x : Gamma5ClassicalLabel}
    (hd : x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : x.2.1 ∈ primeWindow N ((gamma5GainScale N δ V) ^ r.A) ((gamma5GainScale N δ V) ^ r.B))
    (hq : x.2.2 ∈ primeWindow N ((gamma5GainScale N δ V) ^ r.C) ((gamma5GainScale N δ V) ^ r.D)) :
    x ∈ gamma6BaseLabels N δ (convolutionWuWindows N Δ V) ∧
      gamma5GainV
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.s := by
  have hr := gamma6Gain_rectangle_bounds r
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
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hR.le hr.2.2.2.1.le
      _ ≤ _ := hlev
  have hqR : (x.2.2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1 := by
    calc
      _ ≤ (gamma5GainScale N δ V) ^ r.D := hq'.2.2.2.le
      _ ≤ gamma5GainScale N δ V := by
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hR.le hr.2.2.2.2.1.le
      _ ≤ _ := hlev
  have hpd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hp'.1.one_le hpR
  have hqd := gamma5Gain_coordinate_drift hN hδ hδhi hb hd hq'.1.one_le hqR
  have hm : (i : ℝ) * log Δ / log (gamma5GainScale N δ V) ≤ e := by
    simpa only [gamma5GainStep, mul_div_assoc] using hmesh
  have hpa : gamma5MassA ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 := by linarith
  have hqcl : gamma6BaseC ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 := by linarith
  have hpb : gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 < gamma6BaseB := by
    linarith [r.firstUpper]
  have hqf : gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 < gamma6BaseF := by
    linarith [r.upper]
  have hpm := gamma5Gain_coordinate_window hbase.2.2.1 hp'.1 hp'.2.1 hpa hpb
  have hqm := gamma5Gain_coordinate_window hbase.2.2.1 hq'.1 hq'.2.1 hqcl hqf
  refine ⟨(gamma6Base_mem_labels_iff hN hδ (by linarith) hb x).mpr
    ⟨hd, hp'.1, hq'.1, hp'.2.1, hq'.2.1, (mem_primeWindow.mp hpm).2.2.1,
      (mem_primeWindow.mp hpm).2.2.2, (mem_primeWindow.mp hqm).2.2.1,
      (mem_primeWindow.mp hqm).2.2.2⟩, ?_⟩
  dsimp [gamma5GainV] at hes ⊢
  have hs : 0 < gamma5ClassicalS := by norm_num [gamma5ClassicalS]
  nlinarith [hpd.2.trans hm, hqd.2.trans hm, hpc.1, hqc.1]

end Wu2008DoubleSieve
