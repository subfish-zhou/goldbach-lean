import Wu18938Campaign.M1.Confirmed.ReverseBlocks
import Wu18938Campaign.M1.Confirmed.BuchstabIntegral
import Wu18938Campaign.M1.Confirmed.Omega2Boundary

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical Interval

def inverseTransform (t v : ℝ) : ℝ :=
  t / (t - min (10 * t / 11) (max (t / 2) v)) - 1

theorem inverseTransform_bounds {t : ℝ} (ht : 0 < t) (v : ℝ) :
    inverseTransform t v ∈ Set.Icc (1 : ℝ) 10 := by
  have hlo : t / 2 ≤ min (10 * t / 11) (max (t / 2) v) :=
    le_min (by linarith) (le_max_left _ _)
  have hhi := min_le_left (10 * t / 11) (max (t / 2) v)
  have hd : 0 < t - min (10 * t / 11) (max (t / 2) v) := by linarith
  unfold inverseTransform
  constructor
  · have hh : 2 ≤ t / (t - min (10 * t / 11) (max (t / 2) v)) :=
      (le_div_iff₀ hd).mpr (by linarith)
    linarith
  · have hh : t / (t - min (10 * t / 11) (max (t / 2) v)) ≤ 11 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith

theorem inverseTransform_mono {t : ℝ} (ht : 0 < t) : Monotone (inverseTransform t) := by
  intro a b hab
  have hhi := min_le_left (10 * t / 11) (max (t / 2) b)
  exact sub_le_sub_right (div_le_div_of_nonneg_left ht.le
    (by linarith : 0 < t - min (10 * t / 11) (max (t / 2) b))
    (sub_le_sub_left (min_le_min le_rfl (max_le_max le_rfl hab)) t)) 1

theorem inverseTransform_cancel {t x : ℝ} (ht : 0 < t) (hx : x ∈ Set.Icc (1 : ℝ) 10) :
    inverseTransform t (omega2ParameterTransform t x) = x := by
  have hx0 : 0 < x + 1 := by linarith [hx.1]
  have hlo : t / 2 ≤ omega2ParameterTransform t x := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) (by linarith [hx.1] : 2 ≤ x + 1)
    unfold omega2ParameterTransform
    nlinarith [mul_le_mul_of_nonneg_left hh ht.le]
  have hhi : omega2ParameterTransform t x ≤ 10 * t / 11 := by
    have hh := one_div_le_one_div_of_le hx0 (by linarith [hx.2] : x + 1 ≤ 11)
    unfold omega2ParameterTransform
    nlinarith [mul_le_mul_of_nonneg_left hh ht.le]
  rw [inverseTransform,max_eq_right hlo,min_eq_right hhi,omega2ParameterTransform]
  have heq : t - t * (1 - 1 / (x + 1)) = t / (x + 1) := by ring
  rw [heq]
  field_simp
  ring

theorem lower_node_integral (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      (∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
        ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
        f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
          wuBoxPhi N δ (convolutionWuWindows N Δ U) v) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 →
      ((∫ v in (s - 1)..(t - 1), f v / v) - ε) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        reboxingRawPrimeSum true N δ s t (convolutionWuWindows N Δ V) := by
  have he5 : 0 < ε / 5 := by positivity
  obtain ⟨T0,hT04,h0⟩ := lower_node_to_raw m hη hδ he5
  obtain ⟨T1,_,h1⟩ := geometric_to_node m hη hδ
  obtain ⟨T2,_,h2⟩ := repeated_relative m hη hδ (show 0 < η / 20 by positivity)
    (show 0 < ε / 55 by positivity)
  obtain ⟨T3,_,h3⟩ := absolute_boundary_relative m hη hδ he5
  obtain ⟨T4,_,h4⟩ := shifted_prime_integral m hη hδ he5
  obtain ⟨T5,_,h5⟩ := scale m hη hδ
  refine ⟨max T0 (max T1 (max T2 (max T3 (max T4 T5)))),
    hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb f hf hfb hn s t hs hst ht ht5
  have ht0 : 0 < t := by linarith
  let g := fun v => f (inverseTransform t v)
  have hg : MonotoneOn g (Set.Icc 1 10) := fun a _ b _ hab =>
    hf (inverseTransform_bounds ht0 a) (inverseTransform_bounds ht0 b) (inverseTransform_mono ht0 hab)
  have hgb (v : ℝ) (_hv : v ∈ Set.Icc (1 : ℝ) 10) : |g v| ≤ 11 :=
    hfb _ (inverseTransform_bounds ht0 v)
  obtain ⟨r,hrlo,hrhi,hraw⟩ := h0 N (by omega) heven i Δ V hb f hn s t hs hst (by linarith)
  obtain ⟨hΔ,_,_,hq,_,hmesh⟩ := h5 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hnorm := h1 N (by omega) i Δ V hb g hg hgb s t hs hst ht ht5 r hrlo
  have heq : nodeMain g N δ Δ V t r = lowerMain f N δ Δ V t r := by
    unfold nodeMain lowerMain
    apply sum_congr rfl
    intro j hj
    have htop := ((reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
      (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hrlo
    have hd := (reboxing_parameter_domain hq hΔ hs hst (by linarith : t ≤ 10)
      (show (1 : ℝ) ≤ j + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]) htop hmesh).2.2
    dsimp [g]
    rw [inverseTransform_cancel ht0 hd]
  rw [heq] at hnorm
  have hwindow := prime_to_geometric hb (by omega) hη hδ g hs hst hrlo
  have hsource : reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
      (fun d p => g (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) =
      reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
      (fun d p => f (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) := by
    unfold reboxingPrimeSum
    simp only [Bool.false_eq_true,if_false]
    congr 1
    apply sum_congr rfl
    intro d hd
    congr 1
    apply sum_congr rfl
    intro p hp
    have hp' := mem_primeWindow.mp hp
    have hD := (hb.support_geometry (by omega) hη hδ hd).2.2.1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
    have hv := shifted_parameter_mem hD hp1 hs hst (by linarith) hp'.2.2.1 hp'.2.2.2
    rw [← omega2_fixed_cutoff_transform hD hp1]
    dsimp [g]
    rw [inverseTransform_cancel ht0 hv]
  rw [hsource] at hwindow
  have hr := h3 N (by omega) i Δ V hb g hgb s t hs hst ht ht5 r ⟨hrlo,hrhi⟩
  have hz : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
      q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
    constructor
    · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
    · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq0 (1 / t))
  have hl := h3 N (by omega) i Δ V hb g hgb t t (hs.trans hst) le_rfl ht ht5 0 hz
  have hrep := h2 N (by omega) i Δ V hb
  have hint := (abs_le.mp (h4 N (by omega) i Δ V hb f hf hfb s t hs hst (by linarith))).1
  linarith only [hraw,hnorm,hwindow,hr,hl,hrep,hint]

end Wu18938Campaign.M1.Confirmed.Rebox
