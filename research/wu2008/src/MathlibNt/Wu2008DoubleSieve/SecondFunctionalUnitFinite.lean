import MathlibNt.Wu2008DoubleSieve.FourthRowJoinedLimit

/-! # Lossless four-coordinate encoding of the unit slice -/
set_option maxHeartbeats 800000

namespace Wu2008DoubleSieve
open Finset Real
open scoped Classical

/-- The modulus and all four ordered prime labels are retained. -/
def secondFunctionalUnitEncode (x : Sigma fun _ : Gamma16Profile => ℕ) :
    Sigma fun _ : ℕ => ℕ × ℕ × ℕ × ℕ :=
  ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2.1, x.2⟩

theorem secondFunctionalUnitEncode_injOn :
    Set.InjOn secondFunctionalUnitEncode {x | x.1.2.2.2.2 = 1} := by
  rintro ⟨⟨d, p3, p2, p1, n⟩, p4⟩ hn ⟨⟨e, q3, q2, q1, m⟩, q4⟩ hm he
  change n = 1 at hn
  change m = 1 at hm
  have hd := congrArg Sigma.fst he
  have hp := congrArg (fun x : Sigma fun _ : ℕ => ℕ × ℕ × ℕ × ℕ => x.2) he
  change d = e at hd
  simp only [secondFunctionalUnitEncode, Prod.mk.injEq] at hp
  rcases hp with ⟨h3, h2, h1, h4⟩
  subst e; subst q3; subst q2; subst q1; subst q4; subst n; subst m
  rfl

/-- Only coordinate bounds are required; no counting estimate is an input. -/
theorem secondFunctionalUnit_weighted_cube {i : ℕ} (W : Fin i → Finset ℕ)
    (P : Finset Gamma16Profile) (F : Gamma16Profile → Finset ℕ) (H : ℕ → ℝ)
    (hP : ∀ c ∈ P, c.2.2.2.2 = 1 →
      c.1 ∈ boxConvolutionSupport W ∧
      (0 < c.2.1 ∧ (c.2.1 : ℝ) ≤ H c.1) ∧
      (0 < c.2.2.1 ∧ (c.2.2.1 : ℝ) ≤ H c.1) ∧
      (0 < c.2.2.2.1 ∧ (c.2.2.2.1 : ℝ) ≤ H c.1))
    (hF : ∀ c ∈ P, c.2.2.2.2 = 1 → ∀ p ∈ F c, 0 < p ∧ (p : ℝ) ≤ H c.1) :
    (∑ c ∈ P.filter (fun c => c.2.2.2.2 = 1),
      (convolutionCoeff W c.1 : ℝ) * (F c).card) ≤
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) * (⌊H d⌋₊ : ℝ) ^ 4 := by
  let A := (P.filter (fun c => c.2.2.2.2 = 1)).sigma F
  let J := fun d => Icc 1 ⌊H d⌋₊
  let B := (boxConvolutionSupport W).sigma fun d => J d ×ˢ (J d ×ˢ (J d ×ˢ J d))
  have hsub : A.image secondFunctionalUnitEncode ⊆ B := by
    intro y hy
    obtain ⟨⟨c, p⟩, hx, rfl⟩ := mem_image.mp hy
    obtain ⟨hc, hp⟩ := mem_sigma.mp hx
    obtain ⟨hc, hn⟩ := mem_filter.mp hc
    obtain ⟨hd, h3, h2, h1⟩ := hP c hc hn
    have h4 := hF c hc hn p hp
    exact mem_sigma.mpr ⟨hd, mem_product.mpr
      ⟨mem_Icc.mpr ⟨h3.1, Nat.le_floor h3.2⟩, mem_product.mpr
      ⟨mem_Icc.mpr ⟨h2.1, Nat.le_floor h2.2⟩, mem_product.mpr
      ⟨mem_Icc.mpr ⟨h1.1, Nat.le_floor h1.2⟩,
       mem_Icc.mpr ⟨h4.1, Nat.le_floor h4.2⟩⟩⟩⟩⟩
  have hinj : Set.InjOn secondFunctionalUnitEncode A := by
    intro x hx y hy he
    exact secondFunctionalUnitEncode_injOn
      (mem_filter.mp (mem_sigma.mp hx).1).2
      (mem_filter.mp (mem_sigma.mp hy).1).2 he
  calc
    _ = ∑ x ∈ A, (convolutionCoeff W x.1.1 : ℝ) := by
      simp only [A, sum_sigma, sum_const, nsmul_eq_mul]
      apply sum_congr rfl
      intro c _
      ring
    _ = ∑ y ∈ A.image secondFunctionalUnitEncode, (convolutionCoeff W y.1 : ℝ) :=
      by
        rw [sum_image hinj]
        rfl
    _ ≤ ∑ y ∈ B, (convolutionCoeff W y.1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by
      simp only [B, J, sum_sigma, sum_const, nsmul_eq_mul, card_product,
        Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul]
      apply sum_congr rfl
      intro d _
      ring

/-- Conversion of the integral four-cube bound to the same reciprocal mass. -/
theorem secondFunctionalUnit_cube_rpow {Q s : ℝ} (hQ : 0 ≤ Q)
    (hs : 0 < s) (hs4 : s ≤ 4) {d : ℕ} (hd : 0 < d) :
    (⌊(Q / d) ^ (1 / s)⌋₊ : ℝ) ^ 4 ≤ Q ^ (4 / s) / d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : 1 ≤ 4 / s := (le_div_iff₀ hs).mpr (by linarith)
  calc
    _ ≤ ((Q / d) ^ (1 / s)) ^ (4 : ℕ) := by
      gcongr
      exact Nat.floor_le (rpow_nonneg (div_nonneg hQ hd0.le) _)
    _ = (Q / d) ^ (4 / s) := by
      rw [← rpow_natCast, ← rpow_mul (div_nonneg hQ hd0.le)]
      congr 1
      norm_num
      ring
    _ = Q ^ (4 / s) / (d : ℝ) ^ (4 / s) := div_rpow hQ hd0.le _
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (rpow_nonneg hQ _) hd0
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hd1 ha

/-- Reusable four-prime unit bound with unrestricted convolution coefficients. -/
theorem secondFunctionalUnit_mass_le {i : ℕ} (W : Fin i → Finset ℕ)
    (P : Finset Gamma16Profile) (F : Gamma16Profile → Finset ℕ) {Q s : ℝ}
    (hQ : 0 ≤ Q) (hs : 2 < s) (hs3 : s ≤ 3)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d)
    (hP : ∀ c ∈ P, c.2.2.2.2 = 1 →
      c.1 ∈ boxConvolutionSupport W ∧
      (0 < c.2.1 ∧ (c.2.1 : ℝ) ≤ (Q / c.1) ^ (1 / s)) ∧
      (0 < c.2.2.1 ∧ (c.2.2.1 : ℝ) ≤ (Q / c.1) ^ (1 / s)) ∧
      (0 < c.2.2.2.1 ∧ (c.2.2.2.1 : ℝ) ≤ (Q / c.1) ^ (1 / s)))
    (hF : ∀ c ∈ P, c.2.2.2.2 = 1 → ∀ p ∈ F c,
      0 < p ∧ (p : ℝ) ≤ (Q / c.1) ^ (1 / s)) :
    (∑ c ∈ P.filter (fun c => c.2.2.2.2 = 1),
      (convolutionCoeff W c.1 : ℝ) * (F c).card) ≤
      Q ^ (4 / s) * boxConvolutionReciprocalMass W := by
  refine (secondFunctionalUnit_weighted_cube W P F (fun d => (Q / d) ^ (1 / s)) hP hF).trans ?_
  unfold boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hdm
  calc
    _ ≤ (convolutionCoeff W d : ℝ) * (Q ^ (4 / s) / d) :=
      mul_le_mul_of_nonneg_left
        (secondFunctionalUnit_cube_rpow hQ (by linarith) (by linarith) (hd d hdm))
        (Nat.cast_nonneg _)
    _ = _ := by ring

end Wu2008DoubleSieve
