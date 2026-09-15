import Wu18938Campaign.M1.Confirmed.Omega2Mass
import MathlibNt.Wu2008DoubleSieve.ReboxingLowerNormalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology

def geometricPrime {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (t : ℝ) (r : ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t 0)
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r),
        f (omega2ParameterTransform t (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) /
          (((p : ℝ) - 2) * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))

theorem geometric_to_node (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc 1 10) →
      (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      geometricPrime f N δ Δ V t r ≤ nodeMain f N δ Δ V t r +
        11 * reboxingRepeatedTheta N ((N : ℝ) ^ (1 / 2 - δ)) (η / 20)
          (convolutionWuWindows N Δ V) := by
  obtain ⟨T0,hT04,h0⟩ := scale m hη hδ
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < η / 20 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb f hf hfb s t hs hst ht ht5 r hr
  obtain ⟨hΔ,hL,hqlo,hq,_,hmesh⟩ := h0 N (by omega) i Δ V hb
  have hlarge := h1 N (by omega)
  simp only [Function.comp_apply] at hlarge
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let g := fun x => f (omega2ParameterTransform t x)
  let u := fun d p : ℕ => log (Q / d) / log p - 1
  let w := fun d : ℕ => wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))
  let K := fun d p : ℕ => 1 / (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  let P := primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r)
  let Pj := fun j : ℕ => primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1))
  let I := fun d p : ℕ => wuSingularSeries ((d * p) * N) /
    ((Nat.totient (d * p) : ℝ) * log (Q / ((d : ℝ) * p)))
  let E := 4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * w d *
      ∑ p ∈ P, if p ∣ d then K d p else 0
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hQpos : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) η).trans_le (hb.endpoint_lower l)
  have hΔ0 : 0 < Δ := by linarith
  have hq0 : 0 < q := by dsimp [q,Q]; linarith
  have hD := fun d hd => reboxing_support_level_bounds hQpos.le hΔ0 hV (N := N) (d := d) hd
  have hsp := fun d hd => hb.support_geometry (by omega) hη hδ (d := d) hd
  have hw (d : ℕ) (hd : d ∈ boxConvolutionSupport W) : 0 ≤ w d :=
    div_nonneg (wuSingularSeries_pos _ (Nat.mul_pos (hsp d hd).1 (by omega))).le
      (mul_nonneg (Nat.cast_nonneg _) (log_pos (hsp d hd).2.2.1).le)
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  have hmono : MonotoneOn g (Set.Icc 1 10) := by
    intro a ha b hb hab
    exact hf (omega2ParameterTransform_domain ht ht5 ha.1)
      (omega2ParameterTransform_domain ht ht5 hb.1)
      (omega2ParameterTransform_mono (by linarith) ha.1 hab)
  have hgb (x : ℝ) (hx : x ∈ Set.Icc 1 10) : |g x| ≤ 11 :=
    hfb _ (omega2ParameterTransform_domain ht ht5 hx.1)
  have hlow : (N : ℝ) ^ (η / 20) ≤ reboxingAlpha q Δ t 0 := by
    have hz : reboxingAlpha q Δ t (0 : ℕ) ≤ q ^ (1 / t) ∧
        q ^ (1 / t) < reboxingAlpha q Δ t ((0 : ℕ) + 1) := by
      constructor
      · simp only [Nat.cast_zero,reboxingAlpha_zero,le_refl]
      · simpa [reboxingAlpha] using mul_lt_mul_of_pos_left hΔ (rpow_pos_of_pos hq0 (1 / t))
    simpa only [Nat.cast_zero] using (terminal_geometry hb (by omega) hη hL hqlo
      (by linarith) le_rfl (by linarith : t ≤ 10) hz).1
  have hgeom (d : ℕ) (hd : d ∈ boxConvolutionSupport W) (p : ℕ) (hp : p ∈ P) :
      (N : ℝ) ^ (η / 20) ≤ p ∧ (p : ℝ) < (Q / d) ^ (1 / 2 : ℝ) := by
    have hh := mem_primeWindow.mp hp
    have hc := (reboxing_support_cutoff_bounds hQpos.le hΔ0 hV
      (show 0 < s by linarith) hd).1
    exact ⟨hlow.trans hh.2.2.1,(hh.2.2.2.trans_le (hr.trans hc)).trans_le
      (window_geometry hb (by omega) hη hδ hd hs hst (by linarith)).2⟩
  have hpoint (j : ℕ) (hj : j ∈ range r) (d : ℕ) (hd : d ∈ boxConvolutionSupport W)
      (p : ℕ) (hp : p ∈ Pj j) :
      w d * (g (u d p) * K d p) ≤
        g (reboxingS2 q Δ t i (j + 1)) * I d p +
          11 * w d * (if p ∣ d then K d p else 0) := by
    have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
    have htop := (hm (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hr
    have hpar := reboxing_parameter_domain hq hΔ hs hst (by linarith : t ≤ 10)
      (show (1 : ℝ) ≤ j + 1 by linarith [Nat.cast_nonneg (α := ℝ) j]) htop hmesh
    have hh := mem_primeWindow.mp hp
    have hmem : p ∈ P := mem_primeWindow.mpr ⟨hh.1,hh.2.1,
      (hm (by positivity : (0 : ℝ) ≤ j)).trans hh.2.2.1,
      hh.2.2.2.trans_le (hm (by exact_mod_cast mem_range.mp hj))⟩
    have ha : 1 < reboxingAlpha q Δ t ((j : ℝ) + 1 - 1) := by
      simp only [add_sub_cancel_right]
      exact (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le
        (by simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j by positivity))
    have hpwin : reboxingAlpha q Δ t ((j : ℝ) + 1 - 1) ≤ p := by
      simpa only [add_sub_cancel_right] using hh.2.2.1
    have hu := reboxing_parameter_bounds hq hΔ (hD d hd).1 (hD d hd).2 ha hpwin hh.2.2.2
    have hux : u d p ∈ Set.Icc (1 : ℝ) 10 :=
      ⟨hpar.1.trans hu.1,hu.2.trans hpar.2.2.2⟩
    have hab := hmono hux ⟨hpar.2.2.1,hpar.2.2.2⟩ hu.2
    have haB := (le_abs_self (g (u d p))).trans (hgb _ hux)
    have hp4 := hlarge.trans (hgeom d hd p hmem).1
    have hp2 : 2 < p := by exact_mod_cast (show (2 : ℝ) < p by linarith)
    have h := wu_inserted_theta_lower_coefficient (show 0 < N by omega) (hsp d hd).1
      hh.1 hp2 hh.2.1 (hsp d hd).2.2.1 (hgeom d hd p hmem).2.le hab haB
      (by norm_num : (0 : ℝ) ≤ 11)
    simpa only [w,u,g,K,I,q,Q,div_eq_mul_inv,one_mul] using h
  have hfinite : geometricPrime f N δ Δ V t r ≤ nodeMain f N δ Δ V t r + 11 * E := by
    have hp := reboxingAlpha_convolution_sum_partition (t := t) hq0 hΔ N r W
      (fun d p => w d * (g (u d p) * K d p))
    have he := reboxingAlpha_convolution_sum_partition (t := t) hq0 hΔ N r W
      (fun d p => w d * (if p ∣ d then K d p else 0))
    have hsum : (∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j, w d * (g (u d p) * K d p)) ≤
      ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
        (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j,
          (g (reboxingS2 q Δ t i (j + 1)) * I d p +
            11 * w d * (if p ∣ d then K d p else 0)) := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact sum_le_sum (fun p hp => hpoint j hj d hd p hp)
    have hh := mul_le_mul_of_nonneg_left hsum hli
    rw [← hp] at hh
    have he' : E = 4 * logarithmicIntegral N *
        ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W,
          (convolutionCoeff W d : ℝ) * ∑ p ∈ Pj j, w d * (if p ∣ d then K d p else 0) := by
      rw [← he]
      dsimp [E,P]
      simp only [mul_sum,mul_assoc]
    rw [he']
    unfold nodeMain
    simp only [convolutionWuWindows_cons,reboxingAlpha_previous hΔ0,
      add_sub_cancel_right,boxTheta_cons]
    convert hh using 2
    · rfl
    · simp only [geometricPrime,w,g,u,K,W,q,Q,mul_sum,div_eq_mul_inv,mul_inv_rev,one_mul]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro p _
      ring
    · simp only [Pj,w,g,K,I,W,q,Q,mul_sum,sum_add_distrib,mul_add,div_eq_mul_inv,mul_inv_rev,one_mul]
      congr 1 <;>
        (apply sum_congr rfl
         intro j _
         apply sum_congr rfl
         intro d _
         apply sum_congr rfl
         intro p _
         ring)
  have hE : E ≤ reboxingRepeatedTheta N Q (η / 20) W := by
    unfold reboxingRepeatedTheta
    dsimp only [E]
    apply mul_le_mul_of_nonneg_left _ hli
    apply sum_le_sum
    intro d hd
    have hcoef : 0 ≤ (convolutionCoeff W d : ℝ) * w d := mul_nonneg (Nat.cast_nonneg _) (hw d hd)
    have hsub : P.filter (fun p => p ∣ d) ⊆
        (primeWindow N ((N : ℝ) ^ (η / 20)) ((Q / d) ^ (1 / 2 : ℝ))).filter (fun p => p ∣ d) := by
      intro p hp
      obtain ⟨hp,hpd⟩ := mem_filter.mp hp
      have hh := mem_primeWindow.mp hp
      exact mem_filter.mpr ⟨mem_primeWindow.mpr
        ⟨hh.1,hh.2.1,(hgeom d hd p hp).1,(hgeom d hd p hp).2⟩,hpd⟩
    have hsum : (∑ p ∈ P, if p ∣ d then K d p else 0) ≤
        ∑ p ∈ (primeWindow N ((N : ℝ) ^ (η / 20)) ((Q / d) ^ (1 / 2 : ℝ))).filter
          (fun p => p ∣ d), K d p := by
      rw [← sum_filter]
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hh := mem_primeWindow.mp (mem_filter.mp hp).1
      exact (reboxing_prime_weight_le_four_div (hsp d hd).2.2.1
        (hlarge.trans hh.2.2.1) hh.2.2.2.le).1
    convert mul_le_mul_of_nonneg_left hsum hcoef using 1
    dsimp [w,K]
    ring
  exact hfinite.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (by norm_num)))

end Wu18938Campaign.M1.Confirmed.Rebox
