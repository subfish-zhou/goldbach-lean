import Wu18938Campaign.M1.Confirmed.ReboxingScale
import Wu18938Campaign.M1.Confirmed.ClassicalLeaves
import MathlibNt.Wu2008DoubleSieve.Omega2RawBlocks

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real
open scoped Classical

theorem single_support {i N d : ℕ} {Δ P : ℝ} {V : Fin i → ℝ}
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons P V))) :
    ∃ a ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∃ p ∈ primeWindow N (P / Δ) P, a * p = d := by
  rw [convolutionWuWindows_cons] at hd
  obtain ⟨v,hv,hvd⟩ := mem_image.mp hd
  have hv' := Fintype.mem_piFinset.mp hv
  let w : Fin i → ℕ := fun j => v j.succ
  refine ⟨∏ j, w j,mem_image.mpr
    ⟨w,Fintype.mem_piFinset.mpr (fun j => hv' j.succ),rfl⟩,v 0,hv' 0,?_⟩
  rw [← hvd,Fin.prod_univ_succ]
  dsimp [w]
  ring

theorem single_sum {i N : ℕ} (Δ P : ℝ) (V : Fin i → ℝ) (F : ℕ → ℝ) :
    (∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons P V)),
      (convolutionCoeff (convolutionWuWindows N Δ (Fin.cons P V)) d : ℝ) * F d) =
      ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        ∑ p ∈ primeWindow N (P / Δ) P, F (d * p) := by
  rw [convolutionWuWindows_cons,boxConvolution_sum_cons]

theorem child {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η)
    (hΔ : 1 < Δ)
    (hqlo : (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l))
    (hqN : (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l) ≤ N)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) (j : ℕ)
    (hj : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1) ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    RoughBox (m + 1) (η / 20) δ N (i + 1) Δ
      (Fin.cons (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V) := by
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let P := reboxingAlpha q Δ t (j + 1)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hq : 1 < q := (one_lt_rpow hNr (half_pos hη)).trans_le hqlo
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hPlo : (N : ℝ) ^ (η / 20) ≤ P / Δ := by
    rw [reboxingAlpha_previous (by linarith : 0 < Δ)]
    simp only [add_sub_cancel_right]
    calc
      _ = ((N : ℝ) ^ (η / 2)) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ q ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) hqlo (by norm_num)
      _ ≤ q ^ (1 / t) := rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le ht0 ht)
      _ ≤ _ := by simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j by positivity)
  have hPN : P ≤ N :=
    hj.trans ((show q ^ (1 / s) ≤ q by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le
        ((div_le_iff₀ hs0).mpr (by linarith) : 1 / s ≤ 1)).trans hqN)
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower l)
  have hP0 : 0 < P := reboxingAlpha_pos hq0 (by linarith)
  refine ⟨by have := hb.depth; omega,hb.ratio_lower,hb.ratio_upper,?_,?_,?_,?_⟩
  · exact Fin.cases hPlo (fun l =>
      (rpow_le_rpow_of_exponent_le hNr.le (show η / 20 ≤ η by linarith)).trans (hb.lower l))
  · exact Fin.cases hPN hb.upper
  · intro e he
    obtain ⟨d,hd,p,hp,rfl⟩ := single_support he
    exact (hb.support_large d hd).trans (by
      exact_mod_cast Nat.le_mul_of_pos_right d (mem_primeWindow.mp hp).1.pos)
  · intro e he
    obtain ⟨d,hd,p,hp,rfl⟩ := single_support he
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
    have hRd := (reboxing_support_level_bounds (rpow_nonneg hN0.le (1 / 2 - δ))
      (by linarith : 0 < Δ) hV hd).1
    have hple : (p : ℝ) ≤ q ^ (1 / 2 : ℝ) :=
      (mem_primeWindow.mp hp).2.2.2.le.trans
        (hj.trans (rpow_le_rpow_of_exponent_le hq.le
          (one_div_le_one_div_of_le (by norm_num) hs)))
    calc
      _ ≤ (N : ℝ) ^ (η / 4) := rpow_le_rpow_of_exponent_le hNr.le (by linarith)
      _ = ((N : ℝ) ^ (η / 2)) ^ (1 / 2 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ q ^ (1 / 2 : ℝ) := rpow_le_rpow (by positivity) hqlo (by norm_num)
      _ = q / q ^ (1 / 2 : ℝ) := by
        apply (eq_div_iff (rpow_pos_of_pos hq0 (1 / 2 : ℝ)).ne').mpr
        rw [← rpow_add hq0]
        norm_num
      _ ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) / p :=
        div_le_div₀ (hq0.le.trans hRd) hRd hp0 hple
      _ = _ := by rw [Nat.cast_mul,div_div]

theorem block_lower {m i N : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η)
    (hΔ : 1 < Δ)
    (hqlo : (N : ℝ) ^ (η / 2) ≤ (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l))
    (hqN : (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l) ≤ N)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (f : ℝ → ℝ) (u : ℕ → ℝ) (r : ℕ)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s))
    (hnode : ∀ (k : ℕ) (U : Fin k → ℝ), RoughBox (m + 1) (η / 20) δ N k Δ U →
      ∀ v : ℝ, 1 ≤ v → v ≤ 10 →
      f v * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ U) ≤
        wuBoxPhi N δ (convolutionWuWindows N Δ U) v)
    (hu : ∀ j ∈ range r, 1 ≤ u j ∧ u j ≤ 10) :
    (∑ j ∈ range r, f (u j) * boxTheta N ((N : ℝ) ^ (1 / 2 - δ))
      (convolutionWuWindows N Δ (Fin.cons
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V))) ≤
      reboxingGeometricCutoff N δ Δ V t r u := by
  apply sum_le_sum
  intro j hj
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hq := (one_lt_rpow hNr (half_pos hη)).trans_le hqlo
  have htop := ((reboxingAlpha_strictMono (t := t) (by linarith : 0 <
      (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) hΔ).monotone
      (show (j : ℝ) + 1 ≤ r by exact_mod_cast mem_range.mp hj)).trans hr
  have hchild := child hb hN hη hΔ hqlo hqN hs hst ht j htop
  have hn := hnode _ _ hchild (u j) (hu j hj).1 (hu j hj).2
  change _ ≤ ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ (Fin.cons
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V)),
    (convolutionCoeff (convolutionWuWindows N Δ (Fin.cons
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (j + 1)) V)) d : ℝ) *
      (sourceSieveCount N d (d * N) (wuLocalCutoff N δ d (u j)) : ℝ) at hn
  rw [single_sum] at hn
  simpa only [reboxingAlpha_previous (by linarith : 0 < Δ),Nat.cast_add,
    Nat.cast_one,add_sub_cancel_right] using hn

end Wu18938Campaign.M1.Confirmed.Rebox
