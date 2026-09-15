import Wu18938Campaign.M1.Confirmed.Omega2Cutoff
import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR1

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter MathlibNt.SieveTheory.SingularSeries
open scoped Classical Topology

theorem cutoff_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      0 ≤ omega2CutoffError N δ Δ V t r ∧
        omega2CutoffError N δ Δ V t r ≤
          ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨B,hB,T0,hT04,h0⟩ := cutoff_atom m hη hδ
  obtain ⟨T1,_,h1⟩ := scale m hη hδ
  have hU := liuUniversalProduct_pos
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (B / (liuUniversalProduct * ε))))
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5 r hr
  obtain ⟨hΔ,hL,_,hq,hqN,_⟩ := h1 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let L := log (N : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hatom := h0 N (by omega) heven i Δ V hb s t hs hst ht ht5 r hr
  have hnon : 0 ≤ omega2CutoffError N δ Δ V t r := by
    unfold omega2CutoffError
    apply sum_nonneg
    intro j hj
    apply sum_nonneg
    intro d hd
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro p hp
    have hh := hatom (j + 1) (by omega) (by have := mem_range.mp hj; omega) d hd p
    simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
    exact (hh hp).1
  have hsum : omega2CutoffError N δ Δ V t r ≤
      (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p := by
    calc
      _ ≤ ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) := by
        unfold omega2CutoffError
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply sum_le_sum
        intro p hp
        have hh := hatom (j + 1) (by omega) (by have := mem_range.mp hj; omega) d hd p
        simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hh
        exact (hh hp).2
      _ = ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) :=
        (reboxingAlpha_convolution_sum_partition hq0 hΔ N r W _).symm
      _ = _ := by
        unfold boxConvolutionReciprocalMass
        simp only [mul_sum,sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro p _
        ring
  have hZ : reboxingAlpha q Δ t r ≤ N := hr.trans ((show q ^ (1 / s) ≤ q by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le
      ((div_le_iff₀ (by linarith : 0 < s)).mpr (by linarith) : 1 / s ≤ 1)).trans hqN)
  have hp : (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r),
      (1 : ℝ) / p) ≤ 2 * L :=
    (reboxing_prime_mass_le_harmonic N hZ).trans (by dsimp [L]; linarith)
  have hmass : 0 ≤ boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    positivity
  have hθ := hb.theta_reciprocal_lower (by omega) hη hδ
  have hθ0 : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W :=
    (show 0 ≤ 2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 * boxConvolutionReciprocalMass W
      by positivity).trans hθ
  have hpay : B / liuUniversalProduct / L ^ (2 : ℕ) ≤ ε := by
    have hh := (div_le_iff₀ (mul_pos hU he)).mp (h2 N (by omega))
    simp only [Function.comp_apply] at hh
    apply (div_le_iff₀ (by positivity)).mpr
    apply (div_le_iff₀ hU).mpr
    dsimp [L]
    nlinarith
  refine ⟨hnon,hsum.trans ?_⟩
  calc
    _ ≤ (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W * (2 * L) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (B / liuUniversalProduct / L ^ (2 : ℕ)) *
        (2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 * boxConvolutionReciprocalMass W) := by
      dsimp [L]
      field_simp
    _ ≤ (B / liuUniversalProduct / L ^ (2 : ℕ)) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) W :=
      mul_le_mul_of_nonneg_left hθ (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hpay hθ0

theorem terminal_geometry {m i N r : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η)
    (hL : 1 ≤ log (N : ℝ))
    (hqlo : (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) ∧
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) <
        reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (r + 1)) :
    let Y := reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r
    (N : ℝ) ^ (η / 20) ≤ Y ∧
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        Y ≤ wuLocalCutoff N δ d s ∧
        log (wuLocalCutoff N δ d s / Y) ≤ (2 + (m : ℝ)) / log (N : ℝ) ^ (4 : ℕ) := by
  dsimp only
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let Y := reboxingAlpha q Δ t r
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hΔ,hΔlog,_⟩ := mesh_log hb hL
  have hΔ0 : 0 < Δ := by linarith
  have hq : 1 < q := (one_lt_rpow hNr (half_pos hη)).trans_le hqlo
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hY0 : 0 < Y := reboxingAlpha_pos hq0 hΔ0
  have hYlo : q ^ (1 / t) ≤ Y := by
    simpa only [reboxingAlpha_zero] using
      (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone (show (0 : ℝ) ≤ r by positivity)
  constructor
  · calc
      _ = ((N : ℝ) ^ (η / 2)) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ q ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) hqlo (by norm_num)
      _ ≤ q ^ (1 / t) := rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le ht0 ht)
      _ ≤ _ := hYlo
  · intro d hd
    have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower l)
    have hcuts := reboxing_support_cutoff_bounds (rpow_nonneg hN0.le (1 / 2 - δ))
      hΔ0 hV hs0 hd
    have hlow : Y ≤ wuLocalCutoff N δ d s := hr.1.trans hcuts.1
    refine ⟨hlow,?_⟩
    have hterm : q ^ (1 / s) ≤ Y * Δ := by
      have hh := hr.2.le
      rwa [reboxingAlpha_step hΔ0] at hh
    have hhigh : wuLocalCutoff N δ d s ≤ Y * Δ ^ (1 + (i : ℝ) / s) := by
      calc
        _ ≤ q ^ (1 / s) * Δ ^ ((i : ℝ) / s) := hcuts.2
        _ ≤ (Y * Δ) * Δ ^ ((i : ℝ) / s) :=
          mul_le_mul_of_nonneg_right hterm (rpow_nonneg hΔ0.le _)
        _ = _ := by rw [rpow_add hΔ0,rpow_one]; ring
    have hratio : wuLocalCutoff N δ d s / Y ≤ Δ ^ (1 + (i : ℝ) / s) :=
      (div_le_iff₀ hY0).mpr (by simpa only [mul_comm] using hhigh)
    have hlog := log_le_log (div_pos (hY0.trans_le hlow) hY0) hratio
    rw [log_rpow hΔ0] at hlog
    have him : (i : ℝ) ≤ m := by exact_mod_cast hb.depth
    have his : (i : ℝ) / s ≤ (m : ℝ) / 2 :=
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) hs).trans
        (div_le_div_of_nonneg_right him (by norm_num))
    calc
      _ ≤ (1 + (i : ℝ) / s) * log Δ := hlog
      _ ≤ (1 + (m : ℝ) / 2) * (2 / log (N : ℝ) ^ (4 : ℕ)) :=
        mul_le_mul (by linarith) hΔlog (log_pos hΔ).le (by positivity)
      _ = _ := by ring

theorem boundary_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) ∧
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) <
          reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (r + 1)) →
      reboxingR1 N δ Δ V s t r ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,h0⟩ := reboxing_boundary_relative (show 0 < η / 20 by positivity)
    (show 0 < 2 + (m : ℝ) by positivity) he
  obtain ⟨T1,hT14,h1⟩ := scale m hη hδ
  refine ⟨max T0 T1,hT14.trans (le_max_right _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht r hr
  obtain ⟨_,hL,hqlo,_,_,_⟩ := h1 N (by omega) i Δ V hb
  have hg := terminal_geometry hb (by omega) hη hL hqlo hs hst ht hr
  apply h0 N (by omega) heven i ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)
    (fun _ => reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r)
    (fun d => wuLocalCutoff N δ d s) (fun d hd => hb.support_pos hd)
    (fun d hd => (hb.support_geometry (by omega) hη hδ hd).2.2)
  intro d hd
  exact ⟨hg.1,(hg.2 d hd).1,(hg.2 d hd).2⟩

end Wu18938Campaign.M1.Confirmed.Rebox
