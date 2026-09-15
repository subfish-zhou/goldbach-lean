import MathlibNt.Wu2008DoubleSieve.MotherPairMassQuadrature

namespace Wu2008DoubleSieve.MotherPair
open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

theorem rectLabels_empty_left {i : ℕ} (N : ℕ) (δ A C D : ℝ) (W : Fin i → Finset ℕ) :
    rectLabels N δ W A A C D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_,_,_,_,_,hlo,hhi,_⟩ := mem_filter.mp hx
  exact (not_lt_of_ge hlo) hhi

theorem rectLabels_empty_right {i : ℕ} (N : ℕ) (δ A B C : ℝ) (W : Fin i → Finset ℕ) :
    rectLabels N δ W A B C C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨_,_,_,_,_,_,_,hlo,hhi,_⟩ := mem_filter.mp hx
  exact (not_lt_of_ge hlo) hhi

theorem rect_mass_empty {i : ℕ} (N : ℕ) (δ A B C D : ℝ) (W : Fin i → Finset ℕ)
    (h : A=B ∨ C=D) :
    gamma5ClassicalMainMass N δ W (rectLabels N δ W A B C D) = 0 ∧
      rectIntegral A B C D = 0 := by
  rcases h with h | h
  · subst B
    simp [rectLabels_empty_left, gamma5ClassicalMainMass, rectIntegral]
  · subst D
    simp [rectLabels_empty_right, gamma5ClassicalMainMass, rectIntegral]

theorem rect_mem_iff {i k N : ℕ} {δ Δ U A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hU : U < 1/2) (hB : B ≤ U) (hD : D ≤ U)
    (x : Gamma5ClassicalLabel) :
    x ∈ rectLabels N δ (convolutionWuWindows N Δ V) A B C D ↔
    x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V) ∧
    x.2 ∈ primePairs N ((N:ℝ)^(1/2-δ)/x.1) A B C D := by
  have hpowers (hd : x.1 ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
      (E : ℝ) (hE : E ≤ U) : ((N:ℝ)^(1/2-δ)/x.1)^E ≤ N := by
    have hg := gamma5Mass_support_geometry hN hδ hδhi hb hd
    have hQ : 0 ≤ (N:ℝ)^(1/2-δ) := rpow_nonneg (Nat.cast_nonneg _) _
    calc
      _ ≤ ((N:ℝ)^(1/2-δ)/x.1)^1 := rpow_le_rpow_of_exponent_le hg.2.2.1.le (by linarith)
      _ = (N:ℝ)^(1/2-δ)/x.1 := rpow_one _
      _ ≤ (N:ℝ)^(1/2-δ) := div_le_self hQ (by exact_mod_cast hg.1)
      _ ≤ (N:ℝ)^1 := rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
      _ = N := rpow_one _
  constructor
  · intro hx
    obtain ⟨hx,hp,hq,hpN,hqN,hpa,hpb,hqc,hqd,hpq⟩ := mem_filter.mp hx
    have hd := (mem_product.mp hx).1
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    refine ⟨hd,mem_filter.mpr ⟨mem_product.mpr ⟨?_,?_⟩,hpq,hqd,hpN,hqN,hpb⟩⟩
    · exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N:ℝ)^(1/2-δ)/x.1) B)).mpr ⟨hp,hpa,hpb.le⟩
    · exact (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N:ℝ)^(1/2-δ)/x.1) D)).mpr ⟨hq,hqc,hqd.le⟩
  · rintro ⟨hd,hx⟩
    obtain ⟨hpair,hpq,hqd,hpN,hqN,hpb⟩ := mem_filter.mp hx
    obtain ⟨hpm,hqm⟩ := mem_product.mp hpair
    have hR := (gamma5Mass_support_geometry hN hδ hδhi hb hd).2.2.1
    obtain ⟨hp,hpa,_⟩ := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N:ℝ)^(1/2-δ)/x.1) B)).mp hpm
    obtain ⟨hq,hqc,_⟩ := (mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ (N:ℝ)^(1/2-δ)/x.1) D)).mp hqm
    have hpN' : x.2.1 ≤ N := by exact_mod_cast (hpb.le.trans (hpowers hd B hB))
    have hqN' : x.2.2 ≤ N := by exact_mod_cast (hqd.le.trans (hpowers hd D hD))
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hd,mem_product.mpr
      ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩⟩,
      hp,hq,hpN,hqN,hpa,hpb,hqc,hqd,hpq⟩

theorem sum_rect {i k N : ℕ} {δ Δ U A B C D : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hU : U < 1/2) (hB : B ≤ U) (hD : D ≤ U)
    (f : Gamma5ClassicalLabel → ℝ) :
    (∑ x ∈ rectLabels N δ (convolutionWuWindows N Δ V) A B C D, f x) =
    ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∑ pq ∈ primePairs N ((N:ℝ)^(1/2-δ)/d) A B C D, f (d,pq) := by
  let P := fun d => primePairs N ((N:ℝ)^(1/2-δ)/d) A B C D
  have he : rectLabels N δ (convolutionWuWindows N Δ V) A B C D =
      (boxConvolutionSupport (convolutionWuWindows N Δ V)).biUnion
        (fun d => (P d).image (fun pq => (d,pq))) := by
    ext x
    rw [rect_mem_iff hN hδ hδhi hb hU hB hD, Finset.mem_biUnion]
    constructor
    · rintro ⟨hd,hx⟩
      exact ⟨x.1,hd,mem_image.mpr ⟨x.2,hx,Prod.eta x⟩⟩
    · rintro ⟨d,hd,hx⟩
      obtain ⟨pq,hpq,heq⟩ := mem_image.mp hx
      cases heq
      exact ⟨hd,hpq⟩
  have hdis : ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ e ∈ boxConvolutionSupport (convolutionWuWindows N Δ V), d ≠ e →
      Disjoint ((P d).image (fun pq => (d,pq))) ((P e).image (fun pq => (e,pq))) := by
    intro d _ e _ hde
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨pq,_,heq⟩ := mem_image.mp hx
    obtain ⟨rs,_,heq'⟩ := mem_image.mp hy
    exact hde (congrArg Prod.fst (heq.trans heq'.symm))
  rw [he,sum_biUnion hdis]
  apply sum_congr rfl
  intro d _
  exact sum_image (fun pq _ rs _ heq => congrArg Prod.snd heq)

theorem main_rect_identity_eventually {a U : ℝ} (ha : 1/10 ≤ a) (hU : U < 1/2)
    (k : ℕ) {δ : ℝ} (hδ : 0<δ) (hδhi : δ<1/2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V → ∀ A B C D : ℝ,
      a ≤ A → B ≤ U → a ≤ C → D ≤ U →
      gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
        (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) =
      4*logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
        (convolutionCoeff (convolutionWuWindows N Δ V) d:ℝ)*
          gamma5MassOldWeight N d ((N:ℝ)^(1/2-δ))*
          arithmeticPairs U N d ((N:ℝ)^(1/2-δ)/d) A B C D := by
  have ha0 : 0<a := by linarith
  have hα : 0<wuLocalExponent k δ*a := mul_pos (wuLocalExponent_pos k hδ hδhi) ha0
  filter_upwards [eventually_ge_atTop (2:ℕ),
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4:ℝ))] with N hN hfour
  intro i Δ V hb A B C D hA hB hC hD
  unfold gamma5ClassicalMainMass
  rw [sum_rect hN hδ hδhi hb hU hB hD]
  congr 1
  apply sum_congr rfl
  intro d hd
  have hg := gamma5Mass_support_geometry hN hδ hδhi hb hd
  have hZ : (N:ℝ)^(wuLocalExponent k δ*a) ≤ ((N:ℝ)^(1/2-δ)/d)^a := by
    rw [rpow_mul (Nat.cast_nonneg _)]
    exact rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hg.2.1 ha0.le
  rw [arithmeticPairs,mul_sum]
  apply sum_congr rfl
  intro pq hpq
  obtain ⟨hpair,_hpq,_hqd,hpN,hqN,_hpb⟩ := mem_filter.mp hpq
  obtain ⟨hp,hq⟩ := mem_product.mp hpair
  have hpc := (gamma5Mass_coordinate_mem_iff hg.2.2.1 pq.1).mp hp
  have hqc := (gamma5Mass_coordinate_mem_iff hg.2.2.1 pq.2).mp hq
  have hp4 := hfour.trans (prime_lower hg.2.2.1 hA hZ pq.1 hp).2
  have hq4 := hfour.trans (prime_lower hg.2.2.1 hC hZ pq.2 hq).2
  have hp2 : 2<pq.1 := by exact_mod_cast (show (2:ℝ)<pq.1 by linarith)
  have hq2 : 2<pq.2 := by exact_mod_cast (show (2:ℝ)<pq.2 by linarith)
  have hid := gamma5Mass_two_insertions (by omega : 0<N) hg.1 hpc.1 hqc.1 hp2 hq2 hpN hqN hg.2.2.1
  have hH := clipH_eq (hpc.2.2.trans hB) (hqc.2.2.trans hD)
  dsimp only [gamma5ClassicalProduct]
  simp only [Nat.cast_mul]
  rw [mul_div_assoc,hid,hH]
  ring

/-- Uniform bilateral mass for every moving half-open physical rectangle intersected with
the strict ordered-prime triangle; the original arithmetic weight is unchanged. Evenness is unnecessary for this mass theorem. -/
theorem rectangle_mass {a U : ℝ} (ha : 1/10 ≤ a) (_haU : a ≤ U) (hU : U < 1/2) (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ, wuSourceBox k δ N i Δ V →
      ∀ A B C D : ℝ,
      a ≤ A → A ≤ B → B ≤ U →
      a ≤ C → C ≤ D → D ≤ U →
      |gamma5ClassicalMainMass N δ (convolutionWuWindows N Δ V)
          (rectLabels N δ (convolutionWuWindows N Δ V) A B C D) -
        rectIntegral A B C D *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V)| ≤
        ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have hβ := wuLocalExponent_pos k hδ hδhalf
  have hα : 0 < wuLocalExponent k δ*a := mul_pos hβ (by linarith)
  have hαβ : wuLocalExponent k δ*a ≤ wuLocalExponent k δ*a := le_rfl
  obtain ⟨T1, hmass⟩ := eventually_atTop.mp
    (arithmetic_pair_uniform ha hU hα hβ hαβ hε)
  obtain ⟨T2, hid⟩ := eventually_atTop.mp (main_rect_identity_eventually ha hU k hδ hδhalf)
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hNT i Δ V hb A B C D hA hAB hB hC hCD hD
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNT
  have hN : 2 ≤ N := by omega
  have hT1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hT2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
  let W := convolutionWuWindows N Δ V
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let w := fun d => (convolutionCoeff W d : ℝ) * gamma5MassOldWeight N d Q
  let J := rectIntegral A B C D
  let P := fun d => arithmeticPairs U N d (Q / d) A B C D
  have hw : ∀ d ∈ boxConvolutionSupport W, 0 ≤ w d := by
    intro d hd
    exact mul_nonneg (Nat.cast_nonneg _) (gamma5Mass_support_geometry hN hδ hδhalf hb hd).2.2.2.le
  have hp : ∀ d ∈ boxConvolutionSupport W, |P d - J| ≤ ε := by
    intro d hd
    exact (hmass N hT1 (Q / d) (gamma5Mass_support_geometry hN hδ hδhalf hb hd).2.1
      d A B C D hA hAB hB hC hCD hD).le
  have hsum :
      |(∑ d ∈ boxConvolutionSupport W, w d * P d) - J * ∑ d ∈ boxConvolutionSupport W, w d| ≤
        ε * ∑ d ∈ boxConvolutionSupport W, w d := by
    rw [mul_sum, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro d hd
    rw [show w d * P d - J * w d = w d * (P d - J) by ring,
      abs_mul, abs_of_nonneg (hw d hd)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hp d hd) (hw d hd)
  have hli : 0 ≤ 4 * logarithmicIntegral N := by
    have h := MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 (by norm_num)
      (by exact_mod_cast hN : (2 : ℝ) ≤ N)
    change 0 ≤ 4 * logarithmicIntegral N
    exact mul_nonneg (by norm_num) h
  rw [hid N hT2 i Δ V hb A B C D hA hB hC hD, gamma5Mass_theta_eq]
  change |4 * logarithmicIntegral N * (∑ d ∈ boxConvolutionSupport W, w d * P d) -
    J * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)| ≤
    ε * (4 * logarithmicIntegral N * ∑ d ∈ boxConvolutionSupport W, w d)
  have hh := mul_le_mul_of_nonneg_left hsum hli
  rw [← abs_of_nonneg hli, ← abs_mul] at hh
  rw [abs_of_nonneg hli] at hh
  calc
    _ = |4 * logarithmicIntegral N *
        ((∑ d ∈ boxConvolutionSupport W, w d * P d) -
          J * ∑ d ∈ boxConvolutionSupport W, w d)| := by
      congr 1
      ring
    _ ≤ 4 * logarithmicIntegral N * (ε * ∑ d ∈ boxConvolutionSupport W, w d) := hh
    _ = _ := mul_left_comm _ _ _


end Wu2008DoubleSieve.MotherPair
