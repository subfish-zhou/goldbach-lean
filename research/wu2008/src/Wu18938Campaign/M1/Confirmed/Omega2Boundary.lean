import Wu18938Campaign.M1.Confirmed.Omega2Normalization

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical Topology

def boundaryAbsolute {i : ℕ} (f : ℝ → ℝ) (N : ℕ) (δ Δ : ℝ)
    (V : Fin i → ℝ) (s t : ℝ) (r : ℕ) : ℝ :=
  4 * logarithmicIntegral N *
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ((convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d))) *
      ∑ p ∈ primeWindow N
          (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r)
          (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s)),
        |f (omega2ParameterTransform t (log ((N : ℝ) ^ (1 / 2 - δ) / d) / log p - 1)) /
          (((p : ℝ) - 2) * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))|

theorem absolute_boundary_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ f : ℝ → ℝ, (∀ v ∈ Set.Icc (1 : ℝ) 10, |f v| ≤ 11) →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) ∧
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) <
          reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t (r + 1)) →
      boundaryAbsolute f N δ Δ V s t r ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let α := η / 20
  let K := 2 + (m : ℝ)
  let B := 2 * K / α + 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T0,h0⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T1,hT14,h1⟩ := scale m hη hδ
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ)))
  obtain ⟨T3,h3⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop (44 * B / ε)))
  refine ⟨max T1 (max T0 (max T2 T3)),hT14.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb f hfb s t hs hst ht ht5 r hr
  obtain ⟨hΔ,hL,hqlo,hq,_,hmesh⟩ := h1 N (by omega) i Δ V hb
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let Y := reboxingAlpha q Δ t r
  let Z := fun d : ℕ => (Q / d) ^ (1 / s)
  let g := fun d p : ℕ => f (omega2ParameterTransform t (log (Q / d) / log p - 1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqpos : 0 < q := by dsimp [q,Q]; linarith
  have hΔpos : 0 < Δ := by linarith
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNpos η).trans_le (hb.endpoint_lower l)
  have hD := fun d hd => reboxing_support_level_bounds (rpow_nonneg hNpos.le (1 / 2 - δ))
    hΔpos hV (N := N) (d := d) hd
  have hend := terminal_geometry hb (by omega) hη hL hqlo hs hst (by linarith) hr
  have hYlo : q ^ (1 / t) ≤ Y := by
    simpa only [reboxingAlpha_zero] using
      (reboxingAlpha_strictMono (t := t) hqpos hΔ).monotone (show (0 : ℝ) ≤ r by positivity)
  have hheight := h2 N (by omega)
  simp only [Function.comp_apply] at hheight
  have hprime (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (∑ p ∈ primeWindow N Y (Z d),
        |g d p / (((p : ℝ) - 2) * (1 - log p / log (Q / d)))|) ≤
        44 * B / log (N : ℝ) ^ (5 : ℕ) := by
    have hsp := hb.support_geometry (by omega) hη hδ hd
    have hmass := h0 N (by omega) Y (Z d) hend.1 (hend.2 d hd).1 (hend.2 d hd).2
    have hZ : Z d ≤ (Q / d) ^ (1 / 2 : ℝ) :=
      (window_geometry hb (by omega) hη hδ hd hs hst (by linarith)).2
    calc
      _ ≤ 4 * 11 * ∑ p ∈ primeWindow N Y (Z d), (1 : ℝ) / p := by
        apply reboxing_prime_absolute_term_sum_le (g d) hsp.2.2.1
          (hheight.trans hend.1) hZ (by norm_num)
        intro p hp
        have hh := mem_primeWindow.mp hp
        have hu := reboxingLowerNormalization_parameter_mem hq hΔ hs hst (by linarith : t ≤ 10)
          (hD d hd).1 (hD d hd).2 hmesh (hYlo.trans hh.2.2.1) hh.2.2.2
        exact hfb _ (omega2ParameterTransform_domain ht ht5 hu.1)
      _ ≤ 4 * 11 * (B / log (N : ℝ) ^ (5 : ℕ)) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = _ := by ring
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower (by omega)))
  have hfinite : boundaryAbsolute f N δ Δ V s t r ≤
      (44 * B / log (N : ℝ) ^ (5 : ℕ)) * boxTheta N Q W := by
    unfold boundaryAbsolute boxTheta
    rw [mul_left_comm (44 * B / log (N : ℝ) ^ (5 : ℕ))]
    apply mul_le_mul_of_nonneg_left _ hli
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    simpa only [g,Y,Z,Q,W,mul_comm] using
      mul_le_mul_of_nonneg_left (hprime d hd) (roughBox_theta_weight hb (by omega) hη hδ hd)
  have hpay : 44 * B / log (N : ℝ) ^ (5 : ℕ) ≤ ε := by
    have hL0 : 0 < log (N : ℝ) := by linarith
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_le_iff₀ he).mp (h3 N (by omega))
    simp only [Function.comp_apply] at hh
    nlinarith only [hh]
  exact hfinite.trans (mul_le_mul_of_nonneg_right hpay (theta_nonneg hb (by omega) hη hδ))

theorem window_split (N : ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N a c, f p) =
      (∑ p ∈ primeWindow N a b, f p) + ∑ p ∈ primeWindow N b c, f p := by
  have he : primeWindow N a c = primeWindow N a b ∪ primeWindow N b c := by
    ext p
    simp only [mem_union,mem_primeWindow]
    constructor
    · rintro ⟨hp,hcop,hlo,hhi⟩
      by_cases h : (p : ℝ) < b
      · exact Or.inl ⟨hp,hcop,hlo,h⟩
      · exact Or.inr ⟨hp,hcop,le_of_not_gt h,hhi⟩
    · rintro (⟨hp,hcop,hlo,hhi⟩ | ⟨hp,hcop,hlo,hhi⟩)
      · exact ⟨hp,hcop,hlo,hhi.trans_le hbc⟩
      · exact ⟨hp,hcop,hab.trans hlo,hhi⟩
  rw [he,sum_union]
  exact disjoint_left.mpr (fun p hp hq =>
    (not_lt_of_ge (mem_primeWindow.mp hq).2.2.1) (mem_primeWindow.mp hp).2.2.2)

theorem prime_to_geometric {m i N r : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 4 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (f : ℝ → ℝ) (hs : 2 ≤ s) (hst : s ≤ t)
    (hr : reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
      ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) :
    reboxingPrimeSum false N δ s t (convolutionWuWindows N Δ V)
        (fun d p => f (t * (1 - log p / log ((N : ℝ) ^ (1 / 2 - δ) / d)))) ≤
      geometricPrime f N δ Δ V t r +
        boundaryAbsolute f N δ Δ V t t 0 + boundaryAbsolute f N δ Δ V s t r := by
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let F := fun d p : ℕ => f (omega2ParameterTransform t (log (Q / d) / log p - 1)) /
    (((p : ℝ) - 2) * (1 - log (p : ℝ) / log (Q / d)))
  let w := fun d : ℕ => (convolutionCoeff W d : ℝ) * wuSingularSeries (d * N) /
    ((Nat.totient d : ℝ) * log (Q / d))
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hQpos : 0 < Q := rpow_pos_of_pos (by linarith) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) η).trans_le (hb.endpoint_lower l)
  have hΔ : 1 < Δ := by
    have hh := rpow_pos_of_pos (log_pos hNr) (-4 : ℝ)
    linarith [hb.ratio_lower]
  have hΔ0 : 0 < Δ := by linarith
  have hq0 : 0 < q := div_pos hQpos (prod_pos (fun l _ => hV l))
  have hw := fun d hd => roughBox_theta_weight hb hN hη hδ (d := d) hd
  have hli : 0 ≤ 4 * logarithmicIntegral N :=
    mul_nonneg (by norm_num) ((by positivity : (0 : ℝ) ≤ N / (2 * log N)).trans
      (box_trueLi_lower hN))
  have hfibre (d : ℕ) (hd : d ∈ boxConvolutionSupport W) :
      (∑ p ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s), F d p) ≤
        (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), F d p) +
        (∑ p ∈ primeWindow N (q ^ (1 / t)) (wuLocalCutoff N δ d t), |F d p|) +
        (∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s), |F d p|) := by
    have hA : reboxingAlpha q Δ t 0 ≤ reboxingAlpha q Δ t r :=
      (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone (by positivity)
    have hBD : reboxingAlpha q Δ t r ≤ wuLocalCutoff N δ d s :=
      hr.trans ((reboxing_support_cutoff_bounds hQpos.le hΔ0 hV (show 0 < s by linarith) hd).1)
    have hAC : reboxingAlpha q Δ t 0 ≤ wuLocalCutoff N δ d t := by
      rw [reboxingAlpha_zero]
      exact (reboxing_support_cutoff_bounds hQpos.le hΔ0 hV (show 0 < t by linarith) hd).1
    have hCD := hb.cutoff_antitone (by omega) hη hδ hd (show 0 < s by linarith) hst
    have hsplit1 := window_split N hA hBD (F d)
    have hsplit2 := window_split N hAC hCD (F d)
    have hleft := (neg_le_abs
      (∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (wuLocalCutoff N δ d t), F d p)).trans
      (abs_sum_le_sum_abs _ _)
    have hright : (∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s),
        F d p) ≤ ∑ p ∈ primeWindow N (reboxingAlpha q Δ t r) (wuLocalCutoff N δ d s),
        |F d p| := sum_le_sum (fun _ _ => le_abs_self _)
    simp only [reboxingAlpha_zero] at hsplit1 hsplit2 hleft ⊢
    linarith only [hsplit1,hsplit2,hleft,hright]
  unfold reboxingPrimeSum geometricPrime boundaryAbsolute
  simp only [Bool.false_eq_true,if_false,Nat.cast_zero,reboxingAlpha_zero]
  rw [← mul_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hli
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  simpa only [w,F,W,q,Q,mul_add,wuLocalCutoff,omega2ParameterTransform,sub_add_cancel,
    one_div_div,reboxingAlpha_zero] using mul_le_mul_of_nonneg_left (hfibre d hd) (hw d hd)

end Wu18938Campaign.M1.Confirmed.Rebox
