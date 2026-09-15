import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron
import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVCharacterOrthogonality

open Set Function Filter Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]
local notation "λχ" => AnalyticNumberTheory.LargeSieve.lambdaCharacterPrefix

omit [NeZero q] in
/-- A termwise (hence twist-safe) version of the transition-band estimate. -/
theorem twistedSmoothedPsiClose_aux
    (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ n : ℕ, 0 < n → Smooth1 SmoothingF ε (n / X) ≤ 1)
    (smooth1BddBelow : ∀ n : ℕ, 0 < n → 0 ≤ Smooth1 SmoothingF ε (n / X))
    (smoothIs1 : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (n / X) = 1)
    (smoothIs0 : ∀ n : ℕ, 1 + c₂ * ε ≤ (n : ℝ) / X →
      Smooth1 SmoothingF ε (n / X) = 0)
    (χ : DirichletCharacter ℂ q) :
    ‖twistedSmoothedPsi χ SmoothingF ε X - λχ ⌊X⌋₊ q χ‖ ≤
      2 * C * ε * X * Real.log X := by
  let Lower : (ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun ν e x => if x ≤ 1 then Smooth1 ν e x else 0
  let Upper : (ℝ → ℝ) → ℝ → ℝ → ℝ :=
    fun ν e x => if x ≤ 1 then 1 else Smooth1 ν e x

  have h_outer_gt_one : 1 < 1 + c₂ * ε := by nlinarith [mul_pos c₂_pos ε_pos]
  have h_inner_le_one : 1 - c₁ * ε ≤ 1 := by nlinarith [mul_pos c₁_pos ε_pos]

  have hLowerZero (e x : ℝ) (he : e ∈ Ioo 0 1) (hx : 1 + c₂ * e ≤ x) :
      Lower SmoothingF e x = 0 := by
    have hx1 : ¬ x ≤ 1 := by nlinarith [mul_pos c₂_pos he.1]
    simp [Lower, hx1]
  have hUpperZero (e x : ℝ) (he : e ∈ Ioo 0 1) (hx : 1 + c₂ * e ≤ x) :
      Upper SmoothingF e x = 0 := by
    have hx1 : ¬ x ≤ 1 := by nlinarith [mul_pos c₂_pos he.1]
    simp [Upper, hx1, hc₂ e x he hx]

  have hLowerAbove (n : ℕ) (hn : 0 < n) : Lower SmoothingF ε (n / X) ≤ 1 := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simpa [Lower, h] using smooth1BddAbove n hn
    · simp [Lower, h]
  have hLowerBelow (n : ℕ) (hn : 0 < n) : 0 ≤ Lower SmoothingF ε (n / X) := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simpa [Lower, h] using smooth1BddBelow n hn
    · simp [Lower, h]
  have hUpperAbove (n : ℕ) (hn : 0 < n) : Upper SmoothingF ε (n / X) ≤ 1 := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simp [Upper, h]
    · simpa [Upper, h] using smooth1BddAbove n hn
  have hUpperBelow (n : ℕ) (hn : 0 < n) : 0 ≤ Upper SmoothingF ε (n / X) := by
    by_cases h : (n : ℝ) / X ≤ 1
    · simp [Upper, h]
    · simpa [Upper, h] using smooth1BddBelow n hn

  have hInnerCutoff (n : ℕ) (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      (n : ℝ) / X ≤ 1 := by
    rw [div_le_one X_pos]
    exact hnin.trans (mul_le_of_le_one_right X_pos.le h_inner_le_one)
  have hLowerOne (n : ℕ) (hn : 0 < n)
      (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) : Lower SmoothingF ε (n / X) = 1 := by
    have hnx := hInnerCutoff n hnin
    simp [Lower, hnx, smoothIs1 n hn hnin]
  have hUpperOne (n : ℕ) (_hn : 0 < n)
      (hnin : (n : ℝ) ≤ X * (1 - c₁ * ε)) : Upper SmoothingF ε (n / X) = 1 := by
    have hnx := hInnerCutoff n hnin
    simp [Upper, hnx]
  have hLowerOuter (n : ℕ) (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Lower SmoothingF ε (n / X) = 0 := by
    have hnx : ¬ (n : ℝ) / X ≤ 1 := by linarith
    simp [Lower, hnx]
  have hUpperOuter (n : ℕ) (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Upper SmoothingF ε (n / X) = 0 := by
    have hnx : ¬ (n : ℝ) / X ≤ 1 := by linarith
    simp [Upper, hnx, smoothIs0 n hn]

  have hL := SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt
    hLowerZero C C_eq ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    hLowerAbove hLowerBelow hLowerOne hLowerOuter
  have hU := SmoothedChebyshevClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt
    hUpperZero C C_eq ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    hUpperAbove hUpperBelow hUpperOne hUpperOuter

  let Y := ⌊X⌋₊
  let N := ⌊X * (1 + c₂ * ε)⌋₊ + 1
  have hXN : X < (N : ℝ) := by
    have ho : X < X * (1 + c₂ * ε) := by nlinarith
    exact ho.trans (by simpa [N] using Nat.lt_floor_add_one (X * (1 + c₂ * ε)))
  have hYN : Y + 1 ≤ N := by
    have hYlt : Y < N := by
      change ⌊X⌋₊ < N
      exact (Nat.floor_lt X_pos.le).2 hXN
    omega

  have hFzero (n : ℕ) (hn : n ∉ Finset.range N) :
      Smooth1 SmoothingF ε ((n : ℝ) / X) = 0 := by
    have hnN : N ≤ n := by simpa [Finset.mem_range] using hn
    apply smoothIs0
    rw [le_div_iff₀ X_pos]
    have houtN : X * (1 + c₂ * ε) < (N : ℝ) := by
      simpa [N] using Nat.lt_floor_add_one (X * (1 + c₂ * ε))
    have hnNr : (N : ℝ) ≤ n := by exact_mod_cast hnN
    simpa [mul_comm] using houtN.le.trans hnNr
  have hfilt : (Finset.range N).filter (fun n => n ≤ Y) = Finset.range (Y + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hOutsideCutoff (n : ℕ) (hn : n ∉ Finset.range N) : ¬ (n : ℝ) / X ≤ 1 := by
    rw [not_le, one_lt_div X_pos]
    have hnN : N ≤ n := by simpa [Finset.mem_range] using hn
    have hnNr : (N : ℝ) ≤ n := by exact_mod_cast hnN
    exact hXN.trans_le hnNr

  have htwistedFinite : twistedSmoothedPsi χ SmoothingF ε X =
      ∑ n ∈ Finset.range N, twistedVonMangoldtCoeff χ n * Smooth1 SmoothingF ε (n / X) := by
    unfold twistedSmoothedPsi
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    simp [hFzero n hn]
  have hprefixFinite : λχ Y q χ =
      ∑ n ∈ Finset.range N,
        twistedVonMangoldtCoeff χ n * (if n ≤ Y then (1 : ℝ) else 0) := by
    rw [AnalyticNumberTheory.LargeSieve.lambdaCharacterPrefix]
    rw [← hfilt, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs with h
    · simp [twistedVonMangoldtCoeff, AnalyticNumberTheory.LargeSieve.lambdaNatCoeff]
    · simp

  have hLowerFinite : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X)) =
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X) := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnx := hOutsideCutoff n hn
    simp [Lower, hnx]
  have hUpperFinite : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X)) =
      ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) := by
    apply tsum_eq_sum (s := Finset.range N)
    intro n hn
    have hnx := hOutsideCutoff n hn
    simp [Upper, hnx, hFzero n hn]

  have hpsi : Chebyshev.psi X = ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0) := by
    rw [Chebyshev.psi_eq_sum_range]
    rw [← hfilt, Finset.sum_filter]
    simp

  have hfloor (n : ℕ) : n ≤ Y ↔ (n : ℝ) / X ≤ 1 := by
    rw [div_le_one X_pos]
    exact Nat.le_floor_iff X_pos.le

  have hpoint (n : ℕ) (hn : n ∈ Finset.range N) :
      ‖twistedVonMangoldtCoeff χ n *
          (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖ ≤
        ArithmeticFunction.vonMangoldt n * ((if n ≤ Y then (1 : ℝ) else 0) - Lower SmoothingF ε (n / X) +
          (Upper SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))) := by
    by_cases hn0 : n = 0
    · simp [hn0, twistedVonMangoldtCoeff]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hchar : ‖χ n‖ ≤ 1 := norm_le_one χ n
    have hF0 := smooth1BddBelow n hnpos
    have hF1 := smooth1BddAbove n hnpos
    rw [norm_mul]
    rw [twistedVonMangoldtCoeff, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hcoeff : ArithmeticFunction.vonMangoldt n * ‖χ n‖ ≤
        ArithmeticFunction.vonMangoldt n :=
      mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg hchar
    apply (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)).trans
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    by_cases hny : n ≤ Y
    · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
      simp [hny, Lower, Upper, hnx, abs_of_nonpos (sub_nonpos.mpr hF1)]
    · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
      simp [hny, Lower, Upper, hnx, abs_of_nonneg hF0]

  rw [htwistedFinite, hprefixFinite, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    ‖∑ n ∈ Finset.range N, twistedVonMangoldtCoeff χ n *
        (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖
        ≤ ∑ n ∈ Finset.range N, ‖twistedVonMangoldtCoeff χ n *
          (Smooth1 SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n *
        ((if n ≤ Y then (1 : ℝ) else 0) - Lower SmoothingF ε (n / X) +
          (Upper SmoothingF ε (n / X) - (if n ≤ Y then (1 : ℝ) else 0))) :=
      Finset.sum_le_sum hpoint
    _ = ‖((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X) : ℝ) : ℂ) - Chebyshev.psi X‖ +
        ‖((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) : ℝ) : ℂ) - Chebyshev.psi X‖ := by
      rw [hLowerFinite, hUpperFinite, hpsi]
      have hLle : (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Lower SmoothingF ε (n / X)) ≤
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        by_cases hny : n ≤ Y
        · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
          simpa [hny, Lower, hnx] using smooth1BddAbove n hnpos
        · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
          simp [hny, Lower, hnx]
      have hIleU : (∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * (if n ≤ Y then (1 : ℝ) else 0)) ≤
          ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt n * Upper SmoothingF ε (n / X) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hn0 : n = 0
        · simp [hn0, Upper]
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        by_cases hny : n ≤ Y
        · have hnx : (n : ℝ) / X ≤ 1 := (hfloor n).mp hny
          simp [hny, Upper, hnx]
        · have hnx : ¬ (n : ℝ) / X ≤ 1 := fun h => hny ((hfloor n).mpr h)
          simpa [hny, Upper, hnx] using smooth1BddBelow n hnpos
      rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr hLle),
        abs_of_nonneg (sub_nonneg.mpr hIleU)]
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      ring
    _ ≤ C * ε * X * Real.log X + C * ε * X * Real.log X := add_le_add hL hU
    _ = 2 * C * ε * X * Real.log X := by ring

omit [NeZero q] in
/-- The smoothed von Mangoldt sum twisted by an arbitrary Dirichlet character
is close to the genuine finite character prefix through `⌊X⌋₊`.  The proof is
termwise: `‖χ n‖ ≤ 1` is applied before the two nonnegative transition bands
are bounded by `SmoothedChebyshevClose_aux`. -/
theorem twistedSmoothedPsiClose (χ : DirichletCharacter ℂ q) {SmoothingF : ℝ → ℝ}
    (_diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖twistedSmoothedPsi χ SmoothingF ε X - λχ ⌊X⌋₊ q χ‖ ≤
        C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans Real.log_two_lt_d9 (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C₀ : ℝ := 6 * (3 * c₁ + c₂)
  have C₀_pos : 0 < C₀ := by
    dsimp [C₀]
    positivity
  refine ⟨2 * C₀, mul_pos (by norm_num) C₀_pos, ?_⟩
  intro X X_gt_three ε ε_pos ε_lt_one Xε_gt_two
  have X_pos : 0 < X := by linarith
  have n_div_X_pos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by
    positivity
  have smoothAbove (n : ℕ) (hn : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one ε_pos (n_div_X_pos hn)
  have smoothBelow (n : ℕ) (hn : 0 < n) :
      0 ≤ Smooth1 SmoothingF ε (n / X) :=
    Smooth1Nonneg SmoothingFnonneg (n_div_X_pos hn) ε_pos
  have smoothOne (n : ℕ) (hn : 0 < n)
      (hnle : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) ε_pos (n_div_X_pos hn)
    exact (div_le_iff₀' X_pos).mpr hnle
  have smoothZero (n : ℕ) (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨ε_pos, ε_lt_one⟩ hn
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have h : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
        · exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    apply X_bound_1.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg X_pos.le ε_pos.le)
    rw [c₁_eq, c₂_eq]
    linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  exact twistedSmoothedPsiClose_aux SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂
    C₀ rfl ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    smoothAbove smoothBelow smoothOne smoothZero χ

end DirichletCharacter