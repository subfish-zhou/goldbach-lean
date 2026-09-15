import Wu18938Campaign.M1.Confirmed.PairSeed
import MathlibNt.Wu2008DoubleSieve.MotherPairGainAdmission

noncomputable section

namespace Wu18938Campaign.M1.Confirmed

open Wu2008DoubleSieve MotherPair Finset Real Filter
open scoped Classical Topology

theorem RoughBox.weaken {m m' i N : ℕ} {η η' δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 1 ≤ N) (hm : m ≤ m') (hη : η' ≤ η) :
    RoughBox m' η' δ N i Δ V where
  depth := hb.depth.trans hm
  ratio_lower := hb.ratio_lower
  ratio_upper := hb.ratio_upper
  lower := fun j => (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hη).trans (hb.lower j)
  upper := hb.upper
  support_large := hb.support_large
  remaining := fun d hd => (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hη).trans (hb.remaining d hd)

namespace Pair

theorem gain_mesh (m : ℕ) {η δ ε : ℝ} (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      1 < Δ ∧ 1 < gamma5GainScale N δ V ∧
        ((m : ℝ) + 1) * log Δ / log (gamma5GainScale N δ V) < ε := by
  obtain ⟨T0,hT04,h0⟩ := Rebox.scale m hη hδ
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    ((tendsto_const_nhds.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) :
      Tendsto (fun N : ℕ => (4 * ((m : ℝ) + 1) / η) / log N) atTop (nhds 0)).eventually
        (gt_mem_nhds he))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb
  obtain ⟨hΔ,hL,hqlo,hq,_,_⟩ := h0 N (by omega) i Δ V hb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : (η / 2) * log (N : ℝ) ≤ log (gamma5GainScale N δ V) := by
    simpa only [log_rpow hN0,gamma5GainScale] using log_le_log (rpow_pos_of_pos hN0 _) hqlo
  have hΔ2 : log Δ ≤ 2 := (log_le_sub_one_of_pos (by linarith)).trans
    (by linarith [(Rebox.mesh_log hb hL).2.2])
  refine ⟨hΔ,hq,lt_of_le_of_lt ?_ (h1 N (by omega))⟩
  calc
    _ ≤ (((m : ℝ) + 1) * 2) / ((η / 2) * log N) := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hΔ2 (by positivity)) (by positivity) hlog
    _ = _ := by ring

theorem coordinate_drift {m i N a : ℕ} {η δ Δ : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ) {d : ℕ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (ha : 1 ≤ a) (haR : (a : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d) :
    0 ≤ gamma5MassCoordinate (gamma5GainScale N δ V) a -
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) a ∧
      gamma5MassCoordinate (gamma5GainScale N δ V) a -
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) a ≤
        (i : ℝ) * log Δ / log (gamma5GainScale N δ V) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hV : ∀ j, 0 < V j := fun j => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower j)
  have hr := reboxing_support_level_bounds (rpow_nonneg hN0.le (1 / 2 - δ))
    (show 0 < Δ by linarith) hV hd
  have hRd := (hb.support_geometry hN hη hδ hd).2.2.1
  have hlo := log_le_log (show 0 < gamma5GainScale N δ V by linarith) hr.1
  have hhi := log_le_log (show 0 < (N : ℝ) ^ (1 / 2 - δ) / d by linarith) hr.2
  change log ((N : ℝ) ^ (1 / 2 - δ) / d) ≤ log (gamma5GainScale N δ V * Δ ^ i) at hhi
  rw [log_mul (by linarith : gamma5GainScale N δ V ≠ 0)
    (pow_pos (by linarith : 0 < Δ) i).ne',log_pow] at hhi
  have hLa : 0 ≤ log (a : ℝ) := log_nonneg (by exact_mod_cast ha)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have haL := log_le_log ha0 haR
  have ht : 0 ≤ log (a : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    div_nonneg hLa (log_pos hRd).le
  have ht1 : log (a : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d) ≤ 1 :=
    (div_le_one (log_pos hRd)).mpr haL
  have hid : gamma5MassCoordinate (gamma5GainScale N δ V) a -
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) a =
      (log (a : ℝ) / log ((N : ℝ) ^ (1 / 2 - δ) / d)) *
        ((log ((N : ℝ) ^ (1 / 2 - δ) / d) - log (gamma5GainScale N δ V)) /
          log (gamma5GainScale N δ V)) := by
    have halg (x y z : ℝ) (hy : y ≠ 0) (hz : z ≠ 0) :
        x / y - x / z = (x / z) * ((z - y) / y) := by field_simp
    exact halg _ _ _ (log_pos hR).ne' (log_pos hRd).ne'
  rw [hid]
  refine ⟨mul_nonneg ht (div_nonneg (sub_nonneg.mpr hlo) (log_pos hR).le),?_⟩
  calc
    _ ≤ 1 * ((i : ℝ) * log Δ / log (gamma5GainScale N δ V)) :=
      mul_le_mul ht1 (div_le_div_of_nonneg_right (by linarith) (log_pos hR).le)
        (div_nonneg (sub_nonneg.mpr hlo) (log_pos hR).le) (by norm_num)
    _ = _ := one_mul _

theorem micro_source {m i N a : ℕ} {η δ Δ P A B : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hR : 1 < gamma5GainScale N δ V) (hΔ : 1 < Δ)
    (hB : B ≤ 1) (hPA : (gamma5GainScale N δ V) ^ A ≤ P)
    (hPB : P ≤ (gamma5GainScale N δ V) ^ B)
    {d : ℕ} (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (ha : a ∈ primeWindow N (P / Δ) P) :
    A - (((m : ℝ) + 1) * log Δ / log (gamma5GainScale N δ V)) ≤
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) a ∧
      gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / d) a < B := by
  have hm := micro_coordinate hR (show 0 < Δ by linarith) hPA hPB ha
  have hV : ∀ b, 0 < V b := fun b =>
    (rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) η).trans_le (hb.endpoint_lower b)
  have hlev := (reboxing_support_level_bounds (Q := (N : ℝ) ^ (1 / 2 - δ))
    (rpow_nonneg (Nat.cast_nonneg N) _) (show 0 < Δ by linarith) hV hd).1
  have ha' := mem_primeWindow.mp ha
  have haR : (a : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d := by
    apply ((ha'.2.2.2.le.trans hPB).trans _).trans hlev
    simpa only [rpow_one,gamma5GainScale] using rpow_le_rpow_of_exponent_le hR.le hB
  have hdri := coordinate_drift hb hN hη hδ hR hΔ hd ha'.1.one_le haR
  have him : (i : ℝ) ≤ m := by exact_mod_cast hb.depth
  have hmul := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right him (log_pos hΔ).le) (log_pos hR).le
  have heq : ((m : ℝ) + 1) * log Δ / log (gamma5GainScale N δ V) =
      (m : ℝ) * log Δ / log (gamma5GainScale N δ V) +
        log Δ / log (gamma5GainScale N δ V) := by ring
  constructor <;> linarith

theorem rectangle_admitted (p : SecondFunctionalParameters) (hp : AnalyticParameters p)
    (j : Term) (r : GainRectangle p j) (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      1 < gamma5GainScale N δ V ∧ ∀ P Q : ℝ,
      (gamma5GainScale N δ V) ^ r.A ≤ P → P ≤ (gamma5GainScale N δ V) ^ r.B →
      (gamma5GainScale N δ V) ^ r.C ≤ Q → Q ≤ (gamma5GainScale N δ V) ^ r.D →
      gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V) ⊆
        termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      ∀ x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V),
        Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
          (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.sample := by
  obtain ⟨e,he,hratio⟩ := ratio_margin p hp j r
  let ε := min e (min (r.A - 1 / p.S) (min (r.C - lowerQ p j) (r.C - r.B)))
  have hε : 0 < ε := lt_min he (lt_min (sub_pos.mpr r.lowerP_lt_A)
    (lt_min (sub_pos.mpr r.lowerQ_lt_C) (sub_pos.mpr r.B_lt_C)))
  have hεe : ε ≤ e := min_le_left _ _
  have hεA : ε ≤ r.A - 1 / p.S := (min_le_right _ _).trans (min_le_left _ _)
  have hεC : ε ≤ r.C - lowerQ p j :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεgap : ε ≤ r.C - r.B :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hD : r.D ≤ 1 := by linarith [r.twiceD_lt_one]
  have hB : r.B ≤ 1 := by linarith [r.B_lt_C,r.C_lt_D]
  obtain ⟨T,hT4,hT⟩ := gain_mesh m hη hδ hε
  refine ⟨T,hT4,?_⟩
  intro N hN i Δ V hb
  obtain ⟨hΔ,hR,hmesh⟩ := hT N hN i Δ V hb
  refine ⟨hR,?_⟩
  intro P Q hPA hPB hQC hQD
  have point (x : Gamma5ClassicalLabel)
      (hx : x ∈ gamma5GainCell N Δ P Q (convolutionWuWindows N Δ V)) :
      x ∈ termLabels p j N δ (convolutionWuWindows N Δ V) ∧
      Hratio p j (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1)
        (gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2) ≤ r.sample := by
    obtain ⟨hd,hpq⟩ := mem_product.mp hx
    obtain ⟨ha,hb'⟩ := mem_product.mp hpq
    have hac := micro_source hb (by omega) hη hδ hR hΔ hB hPA hPB hd ha
    have hbc := micro_source hb (by omega) hη hδ hR hΔ hD hQC hQD hd hb'
    have ha' := mem_primeWindow.mp ha
    have hb'' := mem_primeWindow.mp hb'
    have hgeo := hb.support_geometry (by omega) hη hδ hd
    have hRd := hgeo.2.2.1
    have hpa : 1 / p.S ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 := by
      linarith [hac.1]
    have hqa : lowerQ p j ≤ gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 := by
      linarith [hbc.1]
    have hpw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd ha'.1 ha'.2.1 hpa hac.2)
    have hqw := mem_primeWindow.mp (gamma5Gain_coordinate_window hRd hb''.1 hb''.2.1 hqa hbc.2)
    have hcut (E : ℝ) (hE : E ≤ 1) : ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ E ≤ N :=
      (by simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hRd.le hE :
        ((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ E ≤ (N : ℝ) ^ (1 / 2 - δ) / x.1).trans hgeo.2.2.2
    have hpN : x.2.1 < N + 1 := by
      have hh : x.2.1 ≤ N := by exact_mod_cast hpw.2.2.2.le.trans (hcut r.B hB)
      omega
    have hqN : x.2.2 < N + 1 := by
      have hh : x.2.2 ≤ N := by exact_mod_cast hqw.2.2.2.le.trans (hcut r.D hD)
      omega
    have hpq' : x.2.1 < x.2.2 := by
      by_contra hn
      have hn' : (x.2.2 : ℝ) ≤ x.2.1 := by exact_mod_cast (not_lt.mp hn)
      have hl := div_le_div_of_nonneg_right
        (log_le_log (by exact_mod_cast hb''.1.pos) hn') (log_pos hRd).le
      change gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 ≤
        gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 at hl
      linarith [hac.2,hbc.1]
    constructor
    · rw [termLabels_eq_rect]
      apply mem_filter.mpr
      refine ⟨mem_product.mpr ⟨hd,mem_product.mpr ⟨mem_range.mpr hpN,mem_range.mpr hqN⟩⟩,
        ha'.1,hb''.1,ha'.2.1,hb''.2.1,hpw.2.2.1,?_,hqw.2.2.1,?_,hpq'⟩
      · exact hpw.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hRd.le r.B_lt_upperP.le)
      · exact hqw.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hRd.le r.D_lt_upperQ.le)
    · exact hratio _ _ (by linarith [hac.1]) (by linarith [hbc.1])
  exact ⟨fun x hx => (point x hx).1,fun x hx => (point x hx).2⟩

end Pair
end Wu18938Campaign.M1.Confirmed
