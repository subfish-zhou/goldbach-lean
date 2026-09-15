import Wu18938Campaign.M1.Confirmed.Omega2Errors

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter MathlibNt.SieveTheory.SingularSeries
open scoped Classical Topology

theorem buchstab_cutoff_atom (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      ∀ j : ℕ, 1 ≤ j → j ≤ r →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t ((j : ℝ) - 1))
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j),
      let a := reboxingS1 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j
      0 ≤ (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) a) : ℝ) ∧
      (sourceSieveCount N (d * p) ((d * p) * N) p : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) a) : ℝ) ≤
        ((N : ℝ) / ((d : ℝ) * p)) * (B / log (N : ℝ) ^ (5 : ℕ)) := by
  let α := η / 20
  let K := (400 + 40 * (m : ℝ)) / η
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T0,h0⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T1,hT14,h1⟩ := scale m hη hδ
  refine ⟨2 * K / α + 2,by positivity,max T1 T0,hT14.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht r hr j hj hjr d hd p hp
  dsimp only
  obtain ⟨hΔ,hL,hqlo,hq,hqN,hmesh⟩ := h1 N (by omega) i Δ V hb
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let D := Q / d
  let a := reboxingS1 q Δ t j
  let b := reboxingS2 q Δ t i j
  have hL0 : 0 < log (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq0 : 0 < q := by dsimp [q,Q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hNpos η).trans_le (hb.endpoint_lower l)
  have hD := reboxing_support_level_bounds (rpow_nonneg hNpos.le (1 / 2 - δ)) hΔ0 hV hd
  have hD0 : 0 < D := hq0.trans_le hD.1
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have htop := (hm (show (j : ℝ) ≤ r by exact_mod_cast hjr)).trans hr
  have hdom := reboxing_parameter_domain hq hΔ hs hst ht hj1 htop hmesh
  have ht0 : 0 < t := by linarith
  have hprev : q ^ (1 / t) ≤ reboxingAlpha q Δ t ((j : ℝ) - 1) := by
    simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j - 1 by linarith)
  have hprev1 := (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hprev
  have hp' := mem_primeWindow.mp hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hpar := reboxing_parameter_bounds hq hΔ hD.1 hD.2 hprev1 hp'.2.2.1 hp'.2.2.2
  have hwindow := reboxing_replacement_window_bounds hD0 hp1 hdom.1 hpar.1 hpar.2
  have hwidth := parameter_width hb (by omega) hη hL hqlo ht0 ht hj1
  have hheight : (N : ℝ) ^ α ≤ p := by
    calc
      _ = ((N : ℝ) ^ (η / 2)) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hNpos.le]
        dsimp [α]
        congr 1
        ring
      _ ≤ q ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) hqlo (by norm_num)
      _ ≤ q ^ (1 / t) := rpow_le_rpow_of_exponent_le hq.le (one_div_le_one_div_of_le ht0 ht)
      _ ≤ _ := hprev.trans hp'.2.2.1
  have hpN : (p : ℝ) ≤ N := hp'.2.2.2.le.trans (htop.trans ((show q ^ (1 / s) ≤ q by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hq.le
      ((div_le_iff₀ (by linarith : 0 < s)).mpr (by linarith) : 1 / s ≤ 1)).trans hqN))
  have hlogwidth : log (((D / p) ^ (1 / a)) / p) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    calc
      _ ≤ (b - a) * log (p : ℝ) := hwindow.2
      _ ≤ (K / log (N : ℝ) ^ (5 : ℕ)) * log (N : ℝ) :=
        mul_le_mul hwidth.2 (log_le_log (by linarith : (0 : ℝ) < p) hpN)
          (log_pos hp1).le (by positivity)
      _ = _ := by field_simp
  have hmass := h0 N (by omega) (p : ℝ) ((D / p) ^ (1 / a)) hheight hwindow.1 hlogwidth
  have hcut : wuLocalCutoff N δ (d * p) a = (D / p) ^ (1 / a) := by
    simp only [wuLocalCutoff,Nat.cast_mul,div_div,D,Q]
  have hf := reboxing_source_difference_le_prime_mass (by omega : 4 ≤ N) heven
    (Nat.mul_pos (hb.support_pos hd) hp'.1.pos) hwindow.1
  rw [hcut]
  refine ⟨hf.1,hf.2.trans ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (N : ℝ) / (d * p : ℕ) by positivity)

theorem buchstab_cutoff_relative (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      reboxingR2 N δ Δ V t r ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨B,hB,T0,hT04,h0⟩ := buchstab_cutoff_atom m hη hδ
  obtain ⟨T1,_,h1⟩ := scale m hη hδ
  have hU := liuUniversalProduct_pos
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop (B / (liuUniversalProduct * ε))))
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht r hr
  obtain ⟨hΔ,hL,_,hq,hqN,_⟩ := h1 N (by omega) i Δ V hb
  let q := (N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)
  let W := convolutionWuWindows N Δ V
  let L := log (N : ℝ)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hatom := h0 N (by omega) heven i Δ V hb s t hs hst ht r hr
  have hsum : reboxingR2 N δ Δ V t r ≤
      (N : ℝ) * (B / L ^ (5 : ℕ)) * boxConvolutionReciprocalMass W *
        ∑ p ∈ primeWindow N (reboxingAlpha q Δ t 0) (reboxingAlpha q Δ t r), (1 : ℝ) / p := by
    calc
      _ ≤ ∑ j ∈ range r, ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ primeWindow N (reboxingAlpha q Δ t j) (reboxingAlpha q Δ t (j + 1)),
            ((N : ℝ) / ((d : ℝ) * p)) * (B / L ^ (5 : ℕ)) := by
        unfold reboxingR2
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
  have hmass : 0 ≤ boxConvolutionReciprocalMass W := by unfold boxConvolutionReciprocalMass; positivity
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
  apply hsum.trans
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

end Wu18938Campaign.M1.Confirmed.Rebox
