import AnalyticNumberTheory.Sieve.WeightedPan

/-!
# Liu's finite `p₁p₂` weight

This module formalizes the finite characteristic function in Liu (2022),
`eqn-adef`.  The square-root cutoff is stored without rounding as
`p₁ * p₂ ^ 2 ≤ N`; `liuSizeCondition_iff_real_sqrt` identifies it with the
paper's real square-root inequality.

The exact identity below rewrites the non-coprime *majorant* as a finite sum over
the unique admissible pair with `p₁ ∣ d`.  The signed non-coprime sum is only
bounded by that expression.  No outer `d ∣ Q` weighted asymptotic estimate is
asserted here.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Finset

/-- The arithmetic conditions on the ordered prime pair in Liu's `eqn-adef`.
The last condition is the lossless natural-number form of
`p₂ ≤ sqrt (N / p₁)`. -/
def LiuPairConditions (N z y p₁ p₂ : ℕ) : Prop :=
  p₁.Prime ∧ p₂.Prime ∧ z < p₁ ∧ p₁ ≤ y ∧ y < p₂ ∧ p₁ * p₂ ^ 2 ≤ N

instance instDecidableLiuPairConditions (N z y p₁ p₂ : ℕ) :
    Decidable (LiuPairConditions N z y p₁ p₂) := by
  unfold LiuPairConditions
  infer_instance

/-- Each factor in an admissible pair is at most `N`, so `range (N + 1)`
contains every representation. -/
theorem liuPairConditions_factors_le {N z y p₁ p₂ : ℕ}
    (h : LiuPairConditions N z y p₁ p₂) :
    p₁ ≤ N ∧ p₂ ≤ N := by
  have hp₁pos : 0 < p₁ := h.1.pos
  have hp₂pos : 0 < p₂ := h.2.1.pos
  have hprod : 0 < p₁ * p₂ ^ 2 := Nat.mul_pos hp₁pos (pow_pos hp₂pos 2)
  constructor
  · exact (Nat.le_of_dvd hprod (by simp)).trans h.2.2.2.2.2
  · exact (Nat.le_of_dvd hprod (by
      refine ⟨p₁ * p₂, ?_⟩
      simp [pow_two, mul_left_comm])).trans h.2.2.2.2.2

/-- The root-free cutoff is exactly the intended real square-root cutoff when
`p₁` is positive. -/
theorem liuSizeCondition_iff_real_sqrt {N p₁ p₂ : ℕ} (hp₁ : 0 < p₁) :
    p₁ * p₂ ^ 2 ≤ N ↔
      (p₂ : ℝ) ≤ Real.sqrt ((N : ℝ) / (p₁ : ℝ)) := by
  rw [Real.le_sqrt (by positivity) (by positivity),
    (le_div_iff₀ (by exact_mod_cast hp₁ : (0 : ℝ) < (p₁ : ℝ)))]
  norm_cast
  simp [mul_comm]

/-- The finite set of ordered prime pairs occurring in Liu's weight. -/
def liuWeightPairs (N z y : ℕ) : Finset (ℕ × ℕ) :=
  ((range (N + 1)).product (range (N + 1))).filter
    (fun p => LiuPairConditions N z y p.1 p.2)

@[simp]
theorem mem_liuWeightPairs {N z y p₁ p₂ : ℕ} :
    (p₁, p₂) ∈ liuWeightPairs N z y ↔ LiuPairConditions N z y p₁ p₂ := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    rcases liuPairConditions_factors_le h with ⟨hp₁N, hp₂N⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
      mem_range.mpr (by omega)⟩, h⟩

/-- A visible finite witness that `a` has an admissible `p₁p₂` representation. -/
def LiuWeightSupport (N z y a : ℕ) : Prop :=
  ∃ p ∈ liuWeightPairs N z y, p.1 * p.2 = a

instance instDecidableLiuWeightSupport (N z y a : ℕ) :
    Decidable (LiuWeightSupport N z y a) := by
  unfold LiuWeightSupport
  infer_instance

theorem liuWeightSupport_iff {N z y a : ℕ} :
    LiuWeightSupport N z y a ↔
      ∃ p₁ p₂, LiuPairConditions N z y p₁ p₂ ∧ a = p₁ * p₂ := by
  constructor
  · rintro ⟨⟨p₁, p₂⟩, hp, rfl⟩
    exact ⟨p₁, p₂, mem_liuWeightPairs.mp hp, rfl⟩
  · rintro ⟨p₁, p₂, hp, rfl⟩
    exact ⟨(p₁, p₂), mem_liuWeightPairs.mpr hp, rfl⟩

/-- Admissible ordered prime representations are unique.  Thus the
characteristic function below never silently collapses multiplicities. -/
theorem liuPairConditions_unique {N z y p₁ p₂ q₁ q₂ : ℕ}
    (hp : LiuPairConditions N z y p₁ p₂)
    (hq : LiuPairConditions N z y q₁ q₂)
    (heq : p₁ * p₂ = q₁ * q₂) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hp₁dvd : p₁ ∣ q₁ * q₂ := heq ▸ (by simp)
  rcases hp.1.dvd_mul.mp hp₁dvd with hpq₁ | hpq₂
  · have hp₁q₁ : p₁ = q₁ :=
      (Nat.prime_dvd_prime_iff_eq hp.1 hq.1).mp hpq₁
    subst q₁
    exact ⟨rfl, Nat.mul_left_cancel hp.1.pos heq⟩
  · have hp₁q₂ : p₁ = q₂ :=
      (Nat.prime_dvd_prime_iff_eq hp.1 hq.2.1).mp hpq₂
    exact False.elim ((Nat.not_lt_of_ge (hp₁q₂ ▸ hp.2.2.2.1))
      hq.2.2.2.2.1)

/-- Liu's transparent finite characteristic weight: one exactly when the finite
witness set contains an admissible pair whose product is `a`. -/
def liuWeight (N z y a : ℕ) : ℝ :=
  if LiuWeightSupport N z y a then 1 else 0

@[simp]
theorem liuWeight_eq_one_iff {N z y a : ℕ} :
    liuWeight N z y a = 1 ↔ LiuWeightSupport N z y a := by
  simp [liuWeight]

@[simp]
theorem liuWeight_eq_zero_iff {N z y a : ℕ} :
    liuWeight N z y a = 0 ↔ ¬LiuWeightSupport N z y a := by
  simp [liuWeight]

theorem liuWeight_nonneg (N z y a : ℕ) : 0 ≤ liuWeight N z y a := by
  by_cases h : LiuWeightSupport N z y a <;> simp [liuWeight, h]

@[simp]
theorem abs_liuWeight (N z y a : ℕ) :
    |liuWeight N z y a| = liuWeight N z y a :=
  abs_of_nonneg (liuWeight_nonneg N z y a)

/-- Liu's source is a `0/1` indicator, hence satisfies Pan's coefficient bound. -/
theorem abs_liuWeight_le_one (N z y a : ℕ) : |liuWeight N z y a| ≤ 1 := by
  unfold liuWeight
  split <;> norm_num

/-- The number of Liu source pairs obtained from a strict ordered triple by
pairing its medium prime with either large prime. -/
noncomputable def liuOrderedTriplePairMultiplicity
    (N z y p₁ p₂ p₃ : ℕ) : ℝ :=
  liuWeight N z y (p₁ * p₂) + liuWeight N z y (p₁ * p₃)

/-- A strict ordered triple contributes once through its smaller large prime,
and a second time exactly when the larger prime also satisfies Liu's square
cutoff.  Thus the source weight has multiplicity one or two, not uniformly two. -/
theorem liuOrderedTriplePairMultiplicity_eq_one_add_indicator
    {N z y p₁ p₂ p₃ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
    (hzp₁ : z < p₁) (hp₁y : p₁ ≤ y) (hyp₂ : y < p₂)
    (hp₂p₃ : p₂ < p₃) (hprod : p₁ * p₂ * p₃ ≤ N) :
    liuOrderedTriplePairMultiplicity N z y p₁ p₂ p₃ =
      1 + if p₁ * p₃ ^ 2 ≤ N then 1 else 0 := by
  have hsmall : p₁ * p₂ ^ 2 ≤ N := by
    calc
      p₁ * p₂ ^ 2 = p₁ * p₂ * p₂ := by ring
      _ ≤ p₁ * p₂ * p₃ := Nat.mul_le_mul_left (p₁ * p₂) hp₂p₃.le
      _ ≤ N := hprod
  have hpair₂ : LiuPairConditions N z y p₁ p₂ :=
    ⟨hp₁, hp₂, hzp₁, hp₁y, hyp₂, hsmall⟩
  have hw₂ : liuWeight N z y (p₁ * p₂) = 1 :=
    liuWeight_eq_one_iff.mpr
      (liuWeightSupport_iff.mpr ⟨p₁, p₂, hpair₂, rfl⟩)
  by_cases hlarge : p₁ * p₃ ^ 2 ≤ N
  · have hpair₃ : LiuPairConditions N z y p₁ p₃ :=
      ⟨hp₁, hp₃, hzp₁, hp₁y, hyp₂.trans hp₂p₃, hlarge⟩
    have hw₃ : liuWeight N z y (p₁ * p₃) = 1 :=
      liuWeight_eq_one_iff.mpr
        (liuWeightSupport_iff.mpr ⟨p₁, p₃, hpair₃, rfl⟩)
    simp [liuOrderedTriplePairMultiplicity, hw₂, hw₃, hlarge]
  · have hw₃ : liuWeight N z y (p₁ * p₃) = 0 := by
      rw [liuWeight_eq_zero_iff]
      intro hs
      rcases liuWeightSupport_iff.mp hs with ⟨q₁, q₂, hq, heq⟩
      have hq₁dvd : q₁ ∣ p₁ * p₃ := by
        rw [heq]
        exact dvd_mul_right q₁ q₂
      rcases hq.1.dvd_mul.mp hq₁dvd with hq₁p₁ | hq₁p₃
      · have hq₁eq : q₁ = p₁ :=
          (Nat.prime_dvd_prime_iff_eq hq.1 hp₁).mp hq₁p₁
        subst q₁
        have hq₂eq : q₂ = p₃ := Nat.mul_left_cancel hp₁.pos heq.symm
        subst q₂
        exact hlarge hq.2.2.2.2.2
      · have hq₁eq : q₁ = p₃ :=
          (Nat.prime_dvd_prime_iff_eq hq.1 hp₃).mp hq₁p₃
        have : q₁ ≤ y := hq.2.2.2.1
        omega
    simp [liuOrderedTriplePairMultiplicity, hw₂, hw₃, hlarge]

/-- A concrete strict ordered triple for which Liu's source multiplicity is
one.  This is the local obstruction to dividing the source count by two. -/
theorem liuOrderedTriplePairMultiplicity_one_witness :
    liuOrderedTriplePairMultiplicity 1000 1 9 3 11 23 = 1 := by
  have h := liuOrderedTriplePairMultiplicity_eq_one_add_indicator
    (N := 1000) (z := 1) (y := 9) (p₁ := 3) (p₂ := 11) (p₃ := 23)
    (by decide) (by decide) (by decide)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The exact finite size consequence retained in place of an unproved
natural/real `N^(2/3)` floor bridge. -/
theorem liuWeightSupport_le {N z y a : ℕ} (ha : LiuWeightSupport N z y a) :
    a ≤ N := by
  rcases ha with ⟨⟨p₁, p₂⟩, hp, rfl⟩
  have hcond := mem_liuWeightPairs.mp hp
  have hprod : 0 < p₁ * p₂ ^ 2 :=
    Nat.mul_pos hcond.1.pos (pow_pos hcond.2.1.pos 2)
  exact (Nat.le_of_dvd hprod (by
    refine ⟨p₂, ?_⟩
    simp [pow_two, mul_assoc])).trans hcond.2.2.2.2.2

/-- The root-free `N^(2/3)` calculation in its minimal natural-number form.
The two hypotheses say exactly that the smaller factor is first and that the
paper's square-root cutoff holds. -/
theorem product_cube_le_sq {N p₁ p₂ : ℕ} (hp₁p₂ : p₁ ≤ p₂)
    (hsize : p₁ * p₂ ^ 2 ≤ N) :
    (p₁ * p₂) ^ 3 ≤ N ^ 2 := by
  have hsecond : p₁ ^ 2 * p₂ ≤ p₁ * p₂ ^ 2 := by
    calc
      p₁ ^ 2 * p₂ = p₁ * (p₁ * p₂) := by ring
      _ ≤ p₁ * (p₂ * p₂) :=
        Nat.mul_le_mul_left p₁ (Nat.mul_le_mul_right p₂ hp₁p₂)
      _ = p₁ * p₂ ^ 2 := by ring
  calc
    (p₁ * p₂) ^ 3 = (p₁ * p₂ ^ 2) * (p₁ ^ 2 * p₂) := by ring
    _ ≤ N * N := Nat.mul_le_mul hsize (hsecond.trans hsize)
    _ = N ^ 2 := by ring

/-- Every admissible Liu pair satisfies the exact root-free support bound
`(p₁p₂)^3 ≤ N^2`.  No floor or real-power comparison is used. -/
theorem liuPairConditions_product_cube_le_sq {N z y p₁ p₂ : ℕ}
    (h : LiuPairConditions N z y p₁ p₂) :
    (p₁ * p₂) ^ 3 ≤ N ^ 2 :=
  product_cube_le_sq (h.2.2.2.1.trans h.2.2.2.2.1.le) h.2.2.2.2.2

/-- Product-support form of the exact root-free `N^(2/3)` bound. -/
theorem liuWeightSupport_cube_le_sq {N z y a : ℕ}
    (ha : LiuWeightSupport N z y a) :
    a ^ 3 ≤ N ^ 2 := by
  rcases liuWeightSupport_iff.mp ha with ⟨p₁, p₂, hp, rfl⟩
  exact liuPairConditions_product_cube_le_sq hp

/-- The root-free support inequality converts to the intended `N^(2/3)`
real scale.  It belongs to the source weight itself and is reused by both the
Pan source-interval bridge and the deterministic Abel estimate. -/
theorem le_rpow_two_thirds_of_cube_le_sq {N a : ℕ}
    (ha : a ^ 3 ≤ N ^ 2) :
    (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  apply (Real.rpow_le_rpow_iff (Nat.cast_nonneg a)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by norm_num : (0 : ℝ) < 3)).mp
  have hcast : (a : ℝ) ^ 3 ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast ha
  convert hcast using 1 <;>
    norm_num [Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]

/-- Every nonzero Liu source index lies below the exact two-thirds scale. -/
theorem liuWeightSupport_le_rpow_two_thirds {N z y a : ℕ}
    (ha : LiuWeightSupport N z y a) :
    (a : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
  le_rpow_two_thirds_of_cube_le_sq (liuWeightSupport_cube_le_sq ha)


/-- The actual indicator support has the two-thirds cardinality scale forced by
Liu's product-cube condition. -/
theorem liuWeight_support_card_le_ceil_rpow_two_thirds (N z y : ℕ) :
    ((Finset.Icc 1 N).filter (LiuWeightSupport N z y)).card ≤
      Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 := by
  calc
    ((Finset.Icc 1 N).filter (LiuWeightSupport N z y)).card ≤
        (Finset.range (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1)).card := by
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_range]
      apply Nat.lt_succ_iff.mpr
      have hroot := liuWeightSupport_le_rpow_two_thirds ha.2
      have hceil : (N : ℝ) ^ (2 / 3 : ℝ) ≤
          (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) : ℝ) := Nat.le_ceil _
      exact_mod_cast hroot.trans hceil
    _ = Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 := Finset.card_range _

/-- Since `liuWeight` is an indicator, its supported source mass is the support
cardinality. -/
theorem sum_liuWeight_Icc_eq_support_card (N z y : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, liuWeight N z y a =
      ((((Finset.Icc 1 N).filter (LiuWeightSupport N z y)).card : ℕ) : ℝ) := by
  unfold liuWeight
  rw [← Finset.sum_filter]
  simp

/-- Explicit `O(N^(2/3))` mass bound for the actual Liu indicator. -/
theorem sum_liuWeight_Icc_le_ceil_rpow_two_thirds (N z y : ℕ) :
    ∑ a ∈ Finset.Icc 1 N, liuWeight N z y a ≤
      (Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) + 1 : ℕ) := by
  rw [sum_liuWeight_Icc_eq_support_card]
  exact_mod_cast liuWeight_support_card_le_ceil_rpow_two_thirds N z y

/-- A convenient real form of the source mass estimate. -/
theorem sum_liuWeight_Icc_le_three_mul_rpow_two_thirds
    (N z y : ℕ) (hN : 1 ≤ N) :
    ∑ a ∈ Finset.Icc 1 N, liuWeight N z y a ≤
      3 * (N : ℝ) ^ (2 / 3 : ℝ) := by
  let R : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  have hR0 : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hceil : (Nat.ceil R : ℝ) ≤ R + 1 := by
    have hc := Nat.ceil_le_floor_add_one R
    have hf := Nat.floor_le hR0
    have hcR : (Nat.ceil R : ℝ) ≤ (Nat.floor R : ℝ) + 1 := by
      exact_mod_cast hc
    linarith
  calc
    ∑ a ∈ Finset.Icc 1 N, liuWeight N z y a ≤
        ((Nat.ceil R + 1 : ℕ) : ℝ) := by
      exact_mod_cast sum_liuWeight_Icc_le_ceil_rpow_two_thirds N z y
    _ = (Nat.ceil R : ℝ) + 1 := by norm_num
    _ ≤ (R + 1) + 1 := by linarith
    _ ≤ 3 * R := by linarith

/-- If every prime divisor of `d` is at most `w`, then on an admissible pair the
only possible common prime divisor is `p₁`.  The larger factor `p₂` cannot divide
`d` because `w ≤ y < p₂`.  The modulus cutoff `w` is independent of the lower
weight cutoff `z`, which does not occur in this arithmetic statement. -/
theorem not_coprime_mul_iff_p₁_dvd {w y p₁ p₂ d : ℕ} (hwy : w ≤ y)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hyp₂ : y < p₂)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
    ¬(p₁ * p₂).Coprime d ↔ p₁ ∣ d := by
  constructor
  · rw [Nat.Prime.not_coprime_iff_dvd]
    rintro ⟨r, hr, hra, hrd⟩
    rcases hr.dvd_mul.mp hra with hrp₁ | hrp₂
    · simpa [(Nat.prime_dvd_prime_iff_eq hr hp₁).mp hrp₁] using hrd
    · have hre : r = p₂ :=
        (Nat.prime_dvd_prime_iff_eq hr hp₂).mp hrp₂
      have hrw := hd r hr hrd
      omega
  · intro hp₁d
    exact Nat.not_coprime_of_dvd_of_dvd hp₁.one_lt (by simp) hp₁d

/-- If a factor of `a` divides the modulus but not the residue, then the scaled
prime progression defining `primesInAPBelow` is empty. -/
theorem primesInAPBelow_mul_eq_zero_of_dvd_modulus
    {Y p₁ p₂ d l : ℕ} (hp₁d : p₁ ∣ d) (hp₁l : ¬p₁ ∣ l) :
    AnalyticNumberTheory.Sieve.primesInAPBelow Y (p₁ * p₂) d l = 0 := by
  unfold AnalyticNumberTheory.Sieve.primesInAPBelow
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro p hp
  rintro ⟨_, _, hcong⟩
  apply hp₁l
  exact (hcong.dvd_iff hp₁d).mp ⟨p₂ * p, by ring⟩

/-- The residue-count collapse at `l = N % d`. -/
theorem primesInAPBelow_mul_mod_eq_zero
    {N Y p₁ p₂ d : ℕ} (hp₁d : p₁ ∣ d) (hp₁N : ¬p₁ ∣ N) :
    AnalyticNumberTheory.Sieve.primesInAPBelow
        Y (p₁ * p₂) d (N % d) = 0 := by
  apply primesInAPBelow_mul_eq_zero_of_dvd_modulus hp₁d
  rwa [Nat.dvd_mod_iff hp₁d]

/-! ## Main-term-parametric finite `R₁` seam -/

/-- The source-facing scaled AP error with an arbitrary main-term model:
`π(Y; a, d, l) - main(Y/a)/φ(d)`.

No analytic, sign, or asymptotic property of `main` is assumed. -/
noncomputable def liuScaledAPError
   (main : ℝ → ℝ) (Y a d l : ℕ) : ℝ :=
 (AnalyticNumberTheory.Sieve.primesInAPBelow Y a d l : ℝ) -
   main ((Y : ℝ) / a) / Nat.totient d

/-- The signed non-coprime part for an arbitrary main-term model. -/
noncomputable def liuMainNoncoprimeSum
   (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) : ℝ :=
 ∑ a ∈ range (X + 1),
   if ¬a.Coprime d then f a * liuScaledAPError main Y a d l else 0

/-- The termwise absolute non-coprime majorant for an arbitrary main-term model. -/
noncomputable def liuMainNoncoprimeMajorant
   (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) : ℝ :=
 ∑ a ∈ range (X + 1),
   if ¬a.Coprime d then |f a| * |liuScaledAPError main Y a d l| else 0

/-- ANT's historical Pan error is exactly the specialization to its
`x / log x` compatibility proxy. -/
@[simp] theorem liuScaledAPError_proxy
   (Y a d l : ℕ) :
   liuScaledAPError AnalyticNumberTheory.Sieve.logarithmicIntegral Y a d l =
     AnalyticNumberTheory.Sieve.panDistributionError Y a d l := by
 rfl

/-- The legacy signed non-coprime Pan sum is exactly the proxy specialization. -/
theorem liuMainNoncoprimeSum_proxy
   (Y X d l : ℕ) (f : ℕ → ℝ) :
   liuMainNoncoprimeSum AnalyticNumberTheory.Sieve.logarithmicIntegral
       Y X d l f =
     AnalyticNumberTheory.Sieve.panDistributionNoncoprimeSum Y X d l f := by
 rfl

/-- The legacy non-coprime Pan majorant is exactly the proxy specialization. -/
theorem liuMainNoncoprimeMajorant_proxy
   (Y X d l : ℕ) (f : ℕ → ℝ) :
   liuMainNoncoprimeMajorant AnalyticNumberTheory.Sieve.logarithmicIntegral
       Y X d l f =
     AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant Y X d l f := by
 rfl

/-- The signed non-coprime sum is bounded by its main-parametric majorant. -/
theorem abs_liuMainNoncoprimeSum_le
   (main : ℝ → ℝ) (Y X d l : ℕ) (f : ℕ → ℝ) :
   |liuMainNoncoprimeSum main Y X d l f| ≤
     liuMainNoncoprimeMajorant main Y X d l f := by
 classical
 unfold liuMainNoncoprimeSum liuMainNoncoprimeMajorant
 calc
   |∑ a ∈ range (X + 1),
       (if ¬a.Coprime d then f a * liuScaledAPError main Y a d l else 0)|
       ≤ ∑ a ∈ range (X + 1),
           |if ¬a.Coprime d then f a * liuScaledAPError main Y a d l else 0| :=
     Finset.abs_sum_le_sum_abs _ _
   _ = ∑ a ∈ range (X + 1),
         (if ¬a.Coprime d then
           |f a| * |liuScaledAPError main Y a d l| else 0) := by
     apply Finset.sum_congr rfl
     intro a _
     by_cases hcop : a.Coprime d <;> simp [hcop, abs_mul]

/-- When the progression count vanishes, the arbitrary-model error is exactly
the negative main term. -/
theorem liuScaledAPError_mul_eq_neg_main_div_totient
   (main : ℝ → ℝ) {Y p₁ p₂ d l : ℕ}
   (hp₁d : p₁ ∣ d) (hp₁l : ¬p₁ ∣ l) :
   liuScaledAPError main Y (p₁ * p₂) d l =
     -(main ((Y : ℝ) / (p₁ * p₂)) / Nat.totient d) := by
 simp [liuScaledAPError,
   primesInAPBelow_mul_eq_zero_of_dvd_modulus hp₁d hp₁l]

/-- Absolute-value form of the zero-count reduction, with no sign assumption on
`main`. -/
theorem abs_liuScaledAPError_mul_eq_abs_main_div_totient
   (main : ℝ → ℝ) {Y p₁ p₂ d l : ℕ}
   (hp₁d : p₁ ∣ d) (hp₁l : ¬p₁ ∣ l) :
   |liuScaledAPError main Y (p₁ * p₂) d l| =
     |main ((Y : ℝ) / (p₁ * p₂))| / Nat.totient d := by
 simp [liuScaledAPError,
   primesInAPBelow_mul_eq_zero_of_dvd_modulus hp₁d hp₁l, abs_div]

/-- Zero-count reduction at the canonical residue `N % d`. -/
theorem liuScaledAPError_mul_mod_eq_neg_main_div_totient
   (main : ℝ → ℝ) {N Y p₁ p₂ d : ℕ}
   (hp₁d : p₁ ∣ d) (hp₁N : ¬p₁ ∣ N) :
   liuScaledAPError main Y (p₁ * p₂) d (N % d) =
     -(main ((Y : ℝ) / (p₁ * p₂)) / Nat.totient d) :=
 liuScaledAPError_mul_eq_neg_main_div_totient main hp₁d (by
   rwa [Nat.dvd_mod_iff hp₁d])

/-- Absolute-value zero-count reduction at the canonical residue `N % d`. -/
theorem abs_liuScaledAPError_mul_mod_eq_abs_main_div_totient
   (main : ℝ → ℝ) {N Y p₁ p₂ d : ℕ}
   (hp₁d : p₁ ∣ d) (hp₁N : ¬p₁ ∣ N) :
   |liuScaledAPError main Y (p₁ * p₂) d (N % d)| =
     |main ((Y : ℝ) / (p₁ * p₂))| / Nat.totient d :=
 abs_liuScaledAPError_mul_eq_abs_main_div_totient main hp₁d (by
   rwa [Nat.dvd_mod_iff hp₁d])

/-- The paper-shaped finite pair sum for an arbitrary main-term model. -/
noncomputable def liuP₁DividesMainSum
   (main : ℝ → ℝ) (N z y Y X d l : ℕ) : ℝ :=
 ∑ p ∈ (liuWeightPairs N z y).filter
     (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
   |liuScaledAPError main Y (p.1 * p.2) d l|

/-- The main-parametric majorant is exactly the supported non-coprime sum. -/
theorem liuMainNoncoprimeMajorant_liuWeight_eq_support_sum
   (main : ℝ → ℝ) (N z y Y X d l : ℕ) :
   liuMainNoncoprimeMajorant main Y X d l (liuWeight N z y) =
     ∑ a ∈ (range (X + 1)).filter
         (fun a => LiuWeightSupport N z y a ∧ ¬a.Coprime d),
       |liuScaledAPError main Y a d l| := by
 classical
 unfold liuMainNoncoprimeMajorant
 rw [Finset.sum_filter]
 apply Finset.sum_congr rfl
 intro a _
 by_cases hs : LiuWeightSupport N z y a
 · by_cases hc : a.Coprime d <;> simp [liuWeight, hs, hc]
 · simp [liuWeight, hs]

/-- Reindex the supported non-coprime sum by the unique admissible pair. -/
theorem liuMainSupportNoncoprimeSum_eq_p₁DividesMainSum
   (main : ℝ → ℝ) (N z w y Y X d l : ℕ) (hwy : w ≤ y)
   (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
   (∑ a ∈ (range (X + 1)).filter
       (fun a => LiuWeightSupport N z y a ∧ ¬a.Coprime d),
     |liuScaledAPError main Y a d l|) =
     liuP₁DividesMainSum main N z y Y X d l := by
 classical
 symm
 unfold liuP₁DividesMainSum
 apply Finset.sum_bij (fun p _ => p.1 * p.2)
 · intro p hp
   rw [mem_filter] at hp ⊢
   have hcond := mem_liuWeightPairs.mp hp.1
   refine ⟨mem_range.mpr (by omega), ?_⟩
   refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
   exact (not_coprime_mul_iff_p₁_dvd hwy hcond.1 hcond.2.1
     hcond.2.2.2.2.1 hd).2 hp.2.2
 · rintro ⟨p₁, p₂⟩ hp ⟨q₁, q₂⟩ hq heq
   rw [mem_filter] at hp hq
   have hu := liuPairConditions_unique
     (mem_liuWeightPairs.mp hp.1) (mem_liuWeightPairs.mp hq.1) heq
   exact Prod.ext hu.1 hu.2
 · intro a ha
   rw [mem_filter] at ha
   rcases ha.2.1 with ⟨p, hp, hpa⟩
   have hcond := mem_liuWeightPairs.mp hp
   have hnc : ¬(p.1 * p.2).Coprime d := by simpa [hpa] using ha.2.2
   have hp₁d := (not_coprime_mul_iff_p₁_dvd hwy hcond.1 hcond.2.1
     hcond.2.2.2.2.1 hd).1 hnc
   exact ⟨p, mem_filter.mpr ⟨hp, by
     constructor
     · rw [hpa]
       exact Nat.lt_succ_iff.mp (by
         simpa [Nat.succ_eq_add_one] using mem_range.mp ha.1)
     · exact hp₁d⟩, hpa⟩
 · intro p _
   rfl

/-- Exact finite main-parametric reduction to the `p₁ ∣ d` pair sum. -/
theorem liuMainNoncoprimeMajorant_liuWeight_eq_p₁DividesMainSum
   (main : ℝ → ℝ) (N z w y Y X d l : ℕ) (hwy : w ≤ y)
   (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
   liuMainNoncoprimeMajorant main Y X d l (liuWeight N z y) =
     liuP₁DividesMainSum main N z y Y X d l := by
 rw [liuMainNoncoprimeMajorant_liuWeight_eq_support_sum]
 exact liuMainSupportNoncoprimeSum_eq_p₁DividesMainSum
   main N z w y Y X d l hwy hd

/-- The signed arbitrary-model non-coprime sum is bounded by the same pair sum. -/
theorem abs_liuMainNoncoprimeSum_liuWeight_le_p₁DividesMainSum
   (main : ℝ → ℝ) (N z w y Y X d l : ℕ) (hwy : w ≤ y)
   (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
   |liuMainNoncoprimeSum main Y X d l (liuWeight N z y)| ≤
     liuP₁DividesMainSum main N z y Y X d l := by
 rw [← liuMainNoncoprimeMajorant_liuWeight_eq_p₁DividesMainSum
   main N z w y Y X d l hwy hd]
 exact abs_liuMainNoncoprimeSum_le main Y X d l (liuWeight N z y)

/-- At `N % d`, the arbitrary-model pair sum is exactly the explicit
`|main(Y/(p₁p₂))|/φ(d)` sum. -/
theorem liuP₁DividesMainSum_mod_eq_abs_main_sum
   (main : ℝ → ℝ) (N z y Y X d : ℕ)
   (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
   liuP₁DividesMainSum main N z y Y X d (N % d) =
     ∑ p ∈ (liuWeightPairs N z y).filter
         (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
       |main ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 classical
 unfold liuP₁DividesMainSum
 apply Finset.sum_congr rfl
 intro p hp
 rw [Finset.mem_filter] at hp
 rw [abs_liuScaledAPError_mul_mod_eq_abs_main_div_totient main
   hp.2.2 (havoid p.1 (mem_liuWeightPairs.mp hp.1).1 hp.2.2)]

/-- Exact per-modulus arbitrary-model majorant after the zero-count reduction. -/
theorem liuMainNoncoprimeMajorant_liuWeight_mod_eq_abs_main_sum
   (main : ℝ → ℝ) (N z w y Y X d : ℕ) (hwy : w ≤ y)
   (hd : ∀ r, r.Prime → r ∣ d → r ≤ w)
   (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
   liuMainNoncoprimeMajorant main Y X d (N % d) (liuWeight N z y) =
     ∑ p ∈ (liuWeightPairs N z y).filter
         (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
       |main ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 rw [liuMainNoncoprimeMajorant_liuWeight_eq_p₁DividesMainSum
   main N z w y Y X d (N % d) hwy hd]
 exact liuP₁DividesMainSum_mod_eq_abs_main_sum main N z y Y X d havoid

/-- Signed per-modulus arbitrary-model sum bounded by the explicit main sum. -/
theorem abs_liuMainNoncoprimeSum_liuWeight_mod_le_abs_main_sum
   (main : ℝ → ℝ) (N z w y Y X d : ℕ) (hwy : w ≤ y)
   (hd : ∀ r, r.Prime → r ∣ d → r ≤ w)
   (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
   |liuMainNoncoprimeSum main Y X d (N % d) (liuWeight N z y)| ≤
     ∑ p ∈ (liuWeightPairs N z y).filter
         (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
       |main ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
 rw [← liuP₁DividesMainSum_mod_eq_abs_main_sum main N z y Y X d havoid]
 exact abs_liuMainNoncoprimeSum_liuWeight_le_p₁DividesMainSum
   main N z w y Y X d (N % d) hwy hd

/-! ## Compatibility-proxy specializations -/

/-- **Proxy specialization.** With the progression count zero, ANT's historical
Pan error is the negative `x / log x` main term. -/
theorem panDistributionError_mul_eq_neg_li_div_totient
    {Y p₁ p₂ d l : ℕ} (hp₁d : p₁ ∣ d) (hp₁l : ¬p₁ ∣ l) :
    AnalyticNumberTheory.Sieve.panDistributionError Y (p₁ * p₂) d l =
      -(AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p₁ * p₂)) / Nat.totient d) := by
  simp [AnalyticNumberTheory.Sieve.panDistributionError,
    primesInAPBelow_mul_eq_zero_of_dvd_modulus hp₁d hp₁l]

/-- The sign-free consequence retains `|li|`; no positivity of the logarithmic
integral is assumed. -/
theorem abs_panDistributionError_mul_eq_abs_li_div_totient
    {Y p₁ p₂ d l : ℕ} (hp₁d : p₁ ∣ d) (hp₁l : ¬p₁ ∣ l) :
    |AnalyticNumberTheory.Sieve.panDistributionError Y (p₁ * p₂) d l| =
      |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p₁ * p₂))| / Nat.totient d := by
  simp [AnalyticNumberTheory.Sieve.panDistributionError,
    primesInAPBelow_mul_eq_zero_of_dvd_modulus hp₁d hp₁l, abs_div]

/-- Specialization of the exact signed formula to the residue `N % d`. -/
theorem panDistributionError_mul_mod_eq_neg_li_div_totient
    {N Y p₁ p₂ d : ℕ} (hp₁d : p₁ ∣ d) (hp₁N : ¬p₁ ∣ N) :
    AnalyticNumberTheory.Sieve.panDistributionError
        Y (p₁ * p₂) d (N % d) =
      -(AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p₁ * p₂)) / Nat.totient d) :=
  panDistributionError_mul_eq_neg_li_div_totient hp₁d (by
    rwa [Nat.dvd_mod_iff hp₁d])

/-- Specialization of the absolute-value formula to the residue `N % d`. -/
theorem abs_panDistributionError_mul_mod_eq_abs_li_div_totient
    {N Y p₁ p₂ d : ℕ} (hp₁d : p₁ ∣ d) (hp₁N : ¬p₁ ∣ N) :
    |AnalyticNumberTheory.Sieve.panDistributionError
        Y (p₁ * p₂) d (N % d)| =
      |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p₁ * p₂))| / Nat.totient d :=
  abs_panDistributionError_mul_eq_abs_li_div_totient hp₁d (by
    rwa [Nat.dvd_mod_iff hp₁d])

/-- The paper-shaped finite sum after the `p₂ ∤ d` observation. -/
noncomputable def liuP₁DividesSum
    (N z y Y X d l : ℕ) : ℝ :=
  ∑ p ∈ (liuWeightPairs N z y).filter
      (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
    |AnalyticNumberTheory.Sieve.panDistributionError Y (p.1 * p.2) d l|

/-- The legacy finite pair sum is exactly the `x / log x` proxy specialization. -/
theorem liuP₁DividesMainSum_proxy
    (N z y Y X d l : ℕ) :
    liuP₁DividesMainSum AnalyticNumberTheory.Sieve.logarithmicIntegral
        N z y Y X d l =
      liuP₁DividesSum N z y Y X d l := by
  rfl

/-- The termwise non-coprime majorant is first exactly the sum over supported
products that are not coprime to `d`. -/
theorem panDistributionNoncoprimeMajorant_liuWeight_eq_support_sum
    (N z y Y X d l : ℕ) :
    AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
        Y X d l (liuWeight N z y) =
      ∑ a ∈ (range (X + 1)).filter
          (fun a => LiuWeightSupport N z y a ∧ ¬a.Coprime d),
        |AnalyticNumberTheory.Sieve.panDistributionError Y a d l| := by
  classical
  unfold AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hs : LiuWeightSupport N z y a
  · by_cases hc : a.Coprime d <;> simp [liuWeight, hs, hc]
  · simp [liuWeight, hs]

/-- Exact reindexing of the supported non-coprime sum by the unique admissible
pair. -/
theorem liuSupportNoncoprimeSum_eq_p₁DividesSum
    (N z w y Y X d l : ℕ) (hwy : w ≤ y)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
    (∑ a ∈ (range (X + 1)).filter
        (fun a => LiuWeightSupport N z y a ∧ ¬a.Coprime d),
      |AnalyticNumberTheory.Sieve.panDistributionError Y a d l|) =
      liuP₁DividesSum N z y Y X d l := by
  classical
  symm
  unfold liuP₁DividesSum
  apply Finset.sum_bij (fun p _ => p.1 * p.2)
  · intro p hp
    rw [mem_filter] at hp ⊢
    have hcond := mem_liuWeightPairs.mp hp.1
    refine ⟨mem_range.mpr (by omega), ?_⟩
    refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
    exact (not_coprime_mul_iff_p₁_dvd hwy hcond.1 hcond.2.1
      hcond.2.2.2.2.1 hd).2 hp.2.2
  · rintro ⟨p₁, p₂⟩ hp ⟨q₁, q₂⟩ hq heq
    rw [mem_filter] at hp hq
    have hu := liuPairConditions_unique
      (mem_liuWeightPairs.mp hp.1) (mem_liuWeightPairs.mp hq.1) heq
    exact Prod.ext hu.1 hu.2
  · intro a ha
    rw [mem_filter] at ha
    rcases ha.2.1 with ⟨p, hp, hpa⟩
    have hcond := mem_liuWeightPairs.mp hp
    have hnc : ¬(p.1 * p.2).Coprime d := by simpa [hpa] using ha.2.2
    have hp₁d := (not_coprime_mul_iff_p₁_dvd hwy hcond.1 hcond.2.1
      hcond.2.2.2.2.1 hd).1 hnc
    exact ⟨p, mem_filter.mpr ⟨hp, by
      constructor
      · rw [hpa]
        exact Nat.lt_succ_iff.mp (by
          simpa [Nat.succ_eq_add_one] using mem_range.mp ha.1)
      · exact hp₁d⟩, hpa⟩
  · intro p hp
    rfl

/-- **Exact equality for the majorant.**  On moduli whose prime divisors are at
most the independent cutoff `w ≤ y`, Liu's weight with lower cutoff `z` has
non-coprime majorant precisely equal to the finite `p₁ ∣ d` pair sum. -/
theorem panDistributionNoncoprimeMajorant_liuWeight_eq_p₁DividesSum
    (N z w y Y X d l : ℕ) (hwy : w ≤ y)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
    AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
        Y X d l (liuWeight N z y) =
      liuP₁DividesSum N z y Y X d l := by
  rw [panDistributionNoncoprimeMajorant_liuWeight_eq_support_sum]
  exact liuSupportNoncoprimeSum_eq_p₁DividesSum N z w y Y X d l hwy hd

/-- **Termwise majorant, not an equality for the signed sum.**  This is the
finite `R₁` reduction available before the still-open outer `d ∣ Q` weighted
asymptotic estimate. -/
theorem abs_panDistributionNoncoprimeSum_liuWeight_le_p₁DividesSum
    (N z w y Y X d l : ℕ) (hwy : w ≤ y)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w) :
    |AnalyticNumberTheory.Sieve.panDistributionNoncoprimeSum
        Y X d l (liuWeight N z y)| ≤
      liuP₁DividesSum N z y Y X d l := by
  rw [← panDistributionNoncoprimeMajorant_liuWeight_eq_p₁DividesSum
    N z w y Y X d l hwy hd]
  exact AnalyticNumberTheory.Sieve.abs_panDistributionNoncoprimeSum_le
    Y X d l (liuWeight N z y)

/-- Termwise residue collapse through Liu's finite `p₁ ∣ d` sum.  The explicit
hypothesis is exactly what is needed to pass from `p₁ ∣ d` to `p₁ ∤ N`; in the
corrected Chen application it follows from `d ∣ correctedChenSiftingProduct N`.
-/
theorem liuP₁DividesSum_mod_eq_abs_li_sum
    (N z y Y X d : ℕ)
    (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
    liuP₁DividesSum N z y Y X d (N % d) =
      ∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
        |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
  classical
  unfold liuP₁DividesSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  rw [abs_panDistributionError_mul_mod_eq_abs_li_div_totient
    hp.2.2 (havoid p.1 (mem_liuWeightPairs.mp hp.1).1 hp.2.2)]

/-- Exact non-coprime majorant after every relevant prime divisor of `d` is
known not to divide `N`.  The absolute value on `li` is retained. -/
theorem panDistributionNoncoprimeMajorant_liuWeight_mod_eq_abs_li_sum
    (N z w y Y X d : ℕ) (hwy : w ≤ y)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w)
    (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
    AnalyticNumberTheory.Sieve.panDistributionNoncoprimeMajorant
        Y X d (N % d) (liuWeight N z y) =
      ∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
        |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
  rw [panDistributionNoncoprimeMajorant_liuWeight_eq_p₁DividesSum
    N z w y Y X d (N % d) hwy hd]
  exact liuP₁DividesSum_mod_eq_abs_li_sum N z y Y X d havoid

/-- Signed non-coprime sum bounded by the same exact finite `|li|` expression.
No outer modulus sum, cutoff estimate, or logarithmic estimate is asserted. -/
theorem abs_panDistributionNoncoprimeSum_liuWeight_mod_le_abs_li_sum
    (N z w y Y X d : ℕ) (hwy : w ≤ y)
    (hd : ∀ r, r.Prime → r ∣ d → r ≤ w)
    (havoid : ∀ r, r.Prime → r ∣ d → ¬r ∣ N) :
    |AnalyticNumberTheory.Sieve.panDistributionNoncoprimeSum
        Y X d (N % d) (liuWeight N z y)| ≤
      ∑ p ∈ (liuWeightPairs N z y).filter
          (fun p => p.1 * p.2 ≤ X ∧ p.1 ∣ d),
        |AnalyticNumberTheory.Sieve.logarithmicIntegral
          ((Y : ℝ) / (p.1 * p.2))| / Nat.totient d := by
  rw [← liuP₁DividesSum_mod_eq_abs_li_sum N z y Y X d havoid]
  exact abs_panDistributionNoncoprimeSum_liuWeight_le_p₁DividesSum
    N z w y Y X d (N % d) hwy hd

end MathlibNt.SieveTheory.LiuWeight
