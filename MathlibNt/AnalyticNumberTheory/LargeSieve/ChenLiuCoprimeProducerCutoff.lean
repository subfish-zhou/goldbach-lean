import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingEquation223Source

/-!
# The real cutoff in Pan--Wang--Ding (2.26)

On printed pp. 600 and 603 the parameters are
`D₁ = log(x)^B`, `D = sqrt(x)/log(x)^B`, and `H = (2^j D₁)^2`.
The integer endpoint of the short polynomial is the floor of the *real*
square, not the square of a rounded conductor. The conductor interval is
open on the left and closed on the right, including at integral endpoints.
-/

noncomputable section
open Classical Complex Finset MeasureTheory Filter
open scoped BigOperators Topology

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

def lowConductor (x : ℕ) (B : ℝ) : ℝ := Real.log x ^ B

def upperConductor (x : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt x / lowConductor x B

def conductorRadius (x : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  2 ^ j * lowConductor x B

def shortCutoff (R : ℝ) : ℕ := ⌊R ^ 2⌋₊

def conductorCell (R : ℝ) : Finset ℕ := Ioc ⌊R⌋₊ ⌊2 * R⌋₊

theorem mem_conductorCell_iff {R : ℝ} (hR : 0 ≤ R) (q : ℕ) :
    q ∈ conductorCell R ↔ R < q ∧ (q : ℝ) ≤ 2 * R := by
  simp only [conductorCell, mem_Ioc, Nat.floor_lt hR,
    Nat.le_floor_iff (by positivity : 0 ≤ 2 * R)]

theorem le_shortCutoff_iff (R : ℝ) (n : ℕ) :
    n ≤ shortCutoff R ↔ (n : ℝ) ≤ R ^ 2 :=
  Nat.le_floor_iff (sq_nonneg R)

theorem mem_shortCutoff_iff (R : ℝ) (n : ℕ) :
    n ∈ Icc 1 (shortCutoff R) ↔ 1 ≤ n ∧ (n : ℝ) ≤ R ^ 2 := by
  simp only [mem_Icc, le_shortCutoff_iff]

theorem shortCutoff_le_square (R : ℝ) : (shortCutoff R : ℝ) ≤ R ^ 2 :=
  Nat.floor_le (sq_nonneg R)

theorem square_lt_shortCutoff_add_one (R : ℝ) :
    R ^ 2 < (shortCutoff R : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem shortCutoff_pos {R : ℝ} (hR : 1 ≤ R) : 1 ≤ shortCutoff R := by
  apply (le_shortCutoff_iff R 1).mpr
  simp only [Nat.cast_one]
  nlinarith

theorem square_le_two_mul_shortCutoff {R : ℝ} (hR : 1 ≤ R) :
    R ^ 2 ≤ 2 * (shortCutoff R : ℝ) := by
  have hH : (1 : ℝ) ≤ shortCutoff R := by exact_mod_cast shortCutoff_pos hR
  linarith [square_lt_shortCutoff_add_one R]

theorem radius_le_two_mul_floor {R : ℝ} (hR : 1 ≤ R) :
    R ≤ 2 * (⌊R⌋₊ : ℝ) := by
  have hfloor : (1 : ℝ) ≤ ⌊R⌋₊ := by
    have hn : 1 ≤ ⌊R⌋₊ :=
      (Nat.le_floor_iff (by linarith : 0 ≤ R)).mpr (by simpa using hR)
    exact_mod_cast hn
  linarith [Nat.lt_floor_add_one R]

theorem lowConductor_ge_one {x : ℕ} {B : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) : 1 ≤ lowConductor x B :=
  Real.one_le_rpow hx hB

theorem conductorRadius_ge_one {x : ℕ} {B : ℝ} (j : ℕ)
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) : 1 ≤ conductorRadius x B j := by
  have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  exact one_le_mul_of_one_le_of_one_le hp (lowConductor_ge_one hx hB)

theorem upperConductor_square (x : ℕ) (B : ℝ) :
    upperConductor x B ^ 2 = (x : ℝ) / lowConductor x B ^ 2 := by
  rw [upperConductor, div_pow, Real.sq_sqrt (Nat.cast_nonneg x)]

theorem upperConductor_le_sqrt {x : ℕ} {B : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) :
    upperConductor x B ≤ Real.sqrt x := by
  exact div_le_self (Real.sqrt_nonneg _) (lowConductor_ge_one hx hB)

/-- The hypothesis required by the proved contour displacement follows from
the actual active-cell inequality, uniformly in the cell index. -/
theorem shortCutoff_le_x {x : ℕ} {B R : ℝ}
    (hx : 1 ≤ Real.log x) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hRD : R ≤ upperConductor x B) : shortCutoff R ≤ x := by
  apply Nat.floor_le_of_le
  have hRs := hRD.trans (upperConductor_le_sqrt hx hB)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg x)]

theorem shortCutoff_lt_height {x : ℕ} {B R : ℝ}
    (hx : 2 ≤ Real.log x) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hRD : R ≤ upperConductor x B) :
    (shortCutoff R : ℝ) < panSourceHeight x := by
  have hx1 : (1 : ℝ) < x := by
    have hn : x ≠ 0 := by
      intro he
      subst x
      norm_num at hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog := Real.log_le_sub_one_of_pos hx0
    linarith
  have hH : (shortCutoff R : ℝ) ≤ x := by
    exact_mod_cast shortCutoff_le_x (by linarith) hB hR hRD
  have hx4 : (x : ℝ) < (x : ℝ) ^ 4 := by nlinarith [sq_nonneg ((x : ℝ) ^ 2 - 1)]
  exact hH.trans_lt (hx4.trans_le (panSourceHeight_ge_fourth hx))

/-- The literal short polynomial is exactly the sum over `n ≤ R²`.
The extra ambient bound is only a finite enumeration device. -/
theorem panShortF₁_eq_real_cutoff {q : ℕ} (m x : ℕ) (R : ℝ)
    (hH : shortCutoff R ≤ x) (χ : PrimitiveCharacter q) (s : ℂ) :
    panShortF₁ m (shortCutoff R) χ s =
      ∑ n ∈ (Icc 1 x).filter (fun n : ℕ => (n : ℝ) ≤ R ^ 2),
        panSourceD m n * χ.1 (n : ZMod q) / (n : ℂ) ^ s := by
  have hsets : (Icc 1 x).filter (fun n : ℕ => (n : ℝ) ≤ R ^ 2) =
      Icc 1 (shortCutoff R) := by
    ext n
    simp only [mem_filter, mem_Icc, ← le_shortCutoff_iff]
    omega
  rw [hsets]
  rfl

/-- The constant and threshold precede the real exponent, conductor cell,
character, all source cutoffs, and bounded coefficients. -/
theorem chosen_short_contour_uniform :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      ∀ (B : ℝ) (j q : ℕ) (χ : PrimitiveCharacter q)
        (m y A₁ A₂ k : ℕ) (f : ℕ → ℂ),
      0 ≤ B → conductorRadius x B j ≤ upperConductor x B →
      (∀ n, ‖f n‖ ≤ 1) → 1 ≤ y → y ≤ x → A₂ ≤ y →
      ‖I * (∫ t in -(panSourceHeight x)..panSourceHeight x,
          chen1973VerticalSection
            (pan223Kernel f m (shortCutoff (conductorRadius x B j)) y A₁ A₂ k χ)
            (panSourceSigma x) t) -
        I * (∫ t in -(panSourceHeight x)..panSourceHeight x,
          chen1973VerticalSection
            (pan223Kernel f m (shortCutoff (conductorRadius x B j)) y A₁ A₂ k χ)
            (1 / 2) t)‖ ≤ C * ((x : ℝ) ^ 2)⁻¹ := by
  have he : ∀ᶠ x : ℕ in atTop, 2 ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨X₀, hX⟩ := Filter.eventually_atTop.mp he
  refine ⟨16 * Real.exp 1, by positivity, X₀, ?_⟩
  intro x hx B j q χ m y A₁ A₂ k f hB hRD hf hy hyx hAy
  have hlog := hX x hx
  exact pan223_source_inverse_square f hf m _ y A₁ A₂ k χ hlog hy hyx hAy
    (shortCutoff_le_x (by linarith) hB
      (by have := conductorRadius_ge_one j (by linarith) hB; linarith) hRD)

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
