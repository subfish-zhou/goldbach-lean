import MathlibNt.SieveTheory.Switching.IntegralComparison

/-!
# Alternating-pair contraction and geometric iteration

Near-pair estimates combine with far tails to give quadratic contraction.
Relative transitions, Euler products, and logarithmic cocycles yield geometric
bounds for the iterated discrete alternating-pair operator.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- A filtered finite double sum may be transposed after discarding outer
indices that cannot support the relation. -/
theorem sum_filter_swap_of_imp
    {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (A : Finset α) (B : Finset β)
    (rel : α → β → Prop) [DecidableRel rel]
    (keep : β → Prop) [DecidablePred keep]
    (f : α → β → M)
    (hkeep : ∀ a ∈ A, ∀ b ∈ B, rel a b → keep b) :
    (∑ a ∈ A, ∑ b ∈ B.filter (rel a), f a b) =
      ∑ b ∈ B.filter keep, ∑ a ∈ A.filter (fun a => rel a b), f a b := by
  classical
  calc
    (∑ a ∈ A, ∑ b ∈ B.filter (rel a), f a b) =
        ∑ a ∈ A, ∑ b ∈ B, if rel a b then f a b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_filter]
    _ = ∑ b ∈ B, ∑ a ∈ A, if rel a b then f a b else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b ∈ B, if keep b then
          (∑ a ∈ A.filter (fun a => rel a b), f a b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hkb : keep b
      · rw [if_pos hkb, Finset.sum_filter]
      · rw [if_neg hkb]
        have hempty : ∀ a ∈ A, ¬rel a b := by
          intro a ha hab
          exact hkb (hkeep a ha b hb hab)
        apply Finset.sum_eq_zero
        intro a ha
        rw [if_neg (hempty a ha)]
    _ = ∑ b ∈ B.filter keep,
        ∑ a ∈ A.filter (fun a => rel a b), f a b := by
      rw [Finset.sum_filter]

/-- On a fixed logarithmic-ratio window, one discrete reverse Rosser pair has
the same strict contraction as its continuous model, up to an arbitrarily small
uniform error. -/
theorem exists_upperRosserAlternatingPairDiscrete_normalized_near_le
    (K ρ R : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hR : 3 ≤ R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
            Real.log p₀ / Real.log q < R),
          ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserAlternatingPairNormalizedKernel r
                (Real.log p₁ / Real.log q)
                (Real.log p₀ / Real.log q)) ≤
          (4 / 5 : ℝ) + ρ := by
  let C : ℝ := R * (1 + K / Real.log 2)
  let δ : ℝ := ρ / (4 * (C + 1))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hρ (mul_pos (by norm_num) hC1)
  have hquarter : 0 < ρ / 4 := by positivity
  obtain ⟨Qinner, hQinner, hinner⟩ :=
    exists_upperRosserAlternatingPairDiscrete_inner_le_integral_add
      K δ R hK hδ hR
  obtain ⟨Qouter, hQouter, houter⟩ :=
    exists_upperRosserAlternatingPairDiscrete_outer_le_integral_add
      K (ρ / 4) R hK hquarter hR
  refine ⟨max Qinner Qouter, le_max_of_le_left hQinner, ?_⟩
  intro S q r P hqLarge hqPrime hlocal hr hP hqP
  have hqInner : Qinner ≤ q := le_trans (le_max_left _ _) hqLarge
  have hqOuter : Qouter ≤ q := le_trans (le_max_right _ _) hqLarge
  have hqR : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  let c : ℕ → ℝ := fun p => Real.log p / Real.log q
  let w : ℕ → ℝ := fun p => S.nu p / (1 - S.nu p)
  let X : Finset ℕ := P.filter (fun p => c p < R)
  let Y : Finset ℕ := P.filter (fun p => c p < min R r)
  let rel : ℕ → ℕ → Prop := fun p₀ p₁ =>
    p₁ < p₀ ∧ 2 * c p₀ < c p₁ + r
  have hcOne : ∀ p ∈ P, 1 ≤ c p := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (hP hp)
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    apply (le_div_iff₀ hlogq).2
    simpa [c] using Real.strictMonoOn_log.monotoneOn hqpos hpPos
      (by exact_mod_cast (hqP p hp).le)
  have hkeep : ∀ p₀ ∈ X, ∀ p₁ ∈ P, rel p₀ p₁ →
      c p₁ < min R r := by
    intro p₀ hp₀ p₁ hp₁ hrel
    have hp₀P := (Finset.mem_filter.mp hp₀).1
    have hp₀R := (Finset.mem_filter.mp hp₀).2
    have hp₀Prime : p₀.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp₀P)
    have hp₁Prime : p₁.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp₁)
    have hp₀Pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀Prime.pos
    have hp₁Pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
    have hcLt : c p₁ < c p₀ := by
      apply (div_lt_div_iff_of_pos_right hlogq).2
      exact (Real.strictMonoOn_log.lt_iff_lt hp₁Pos hp₀Pos).2
        (by exact_mod_cast hrel.1)
    have hc₀r : c p₀ < r := by linarith [hrel.2]
    exact lt_min (hcLt.trans hp₀R) (hcLt.trans hc₀r)
  have hswap := sum_filter_swap_of_imp X P rel
    (fun p => c p < min R r)
    (fun p₀ p₁ => w p₀ * w p₁ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r
        (c p₁) (c p₀)) hkeep
  have hinnerBound : ∀ p₁ ∈ Y,
      (∑ p₀ ∈ X.filter (fun p₀ => rel p₀ p₁),
        w p₀ * LinearSieve.upperRosserAlternatingPairNormalizedKernel r
          (c p₁) (c p₀)) ≤
        upperRosserAlternatingPairNormalizedInner r (c p₁) + δ := by
    intro p₁ hp₁
    have hp₁P := (Finset.mem_filter.mp hp₁).1
    have hp₁Bound := (Finset.mem_filter.mp hp₁).2
    have hp₁Prime : p₁.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp₁P)
    let v : ℝ := min R ((c p₁ + r) / 2)
    let T : Finset ℕ := X.filter (fun p₀ => rel p₀ p₁)
    have hc₁R : c p₁ ∈ Set.Icc (1 : ℝ) R :=
      ⟨hcOne p₁ hp₁P, (hp₁Bound.trans_le (min_le_left _ _)).le⟩
    have hc₁r : c p₁ < r :=
      hp₁Bound.trans_le (min_le_right _ _)
    have hcv : c p₁ ≤ v := by
      dsimp [v]
      exact le_min hc₁R.2 (by linarith)
    have hvR : v ≤ R := min_le_left _ _
    have hT : T ⊆ S.prodPrimes.primeFactors := by
      intro p hp
      exact hP ((Finset.mem_filter.mp
        (Finset.mem_filter.mp hp).1).1)
    have hcoord : ∀ p ∈ T, c p ∈ Set.Icc (c p₁) v := by
      intro p hp
      have hpX := (Finset.mem_filter.mp hp).1
      have hpRel := (Finset.mem_filter.mp hp).2
      have hpP := (Finset.mem_filter.mp hpX).1
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors (hP hpP)
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hp₁Pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
      have hlower : c p₁ ≤ c p := by
        apply (div_le_div_iff_of_pos_right hlogq).2
        exact Real.strictMonoOn_log.monotoneOn hp₁Pos hpPos
          (by exact_mod_cast hpRel.1.le)
      exact ⟨hlower, le_min
        (Finset.mem_filter.mp hpX).2.le (by linarith [hpRel.2])⟩
    have hdisc := hinner S q r (c p₁) v T hqInner hqPrime hlocal hr
      hc₁R hcv hvR hT hcoord
    have hintLe :=
      integral_upperRosserAlternatingPairNormalizedKernel_Ioo_le_inner
        hr hc₁R.1 hcv (min_le_right _ _)
    change (∑ p₀ ∈ T, w p₀ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r
        (c p₁) (c p₀)) ≤ _ at hdisc
    change (∑ p₀ ∈ T, w p₀ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r
        (c p₁) (c p₀)) ≤ _
    exact hdisc.trans (by linarith)
  have hY : Y ⊆ S.prodPrimes.primeFactors := by
    intro p hp
    exact hP (Finset.mem_filter.mp hp).1
  have hmass : ∑ p ∈ Y, w p ≤ C := by
    have hinterval : ∀ p ∈ Y,
        (q : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ∧
          (p : ℝ) < (q : ℝ) ^ R := by
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpBound := (Finset.mem_filter.mp hp).2
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors (hP hpP)
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hrpow :
          (q : ℝ) ^ c p = (p : ℝ) := by
        dsimp [c]
        simpa [Real.logb] using
          (Real.rpow_logb hqpos (by exact_mod_cast hqPrime.ne_one) hpPos)
      constructor
      · simpa using (show (q : ℝ) ≤ p by
          exact_mod_cast (hqP p hpP).le)
      · calc
          (p : ℝ) = (q : ℝ) ^ c p := hrpow.symm
          _ < (q : ℝ) ^ R :=
            Real.rpow_lt_rpow_of_exponent_lt hqR
              (hpBound.trans_le (min_le_left _ _))
    have hraw := sum_nu_div_one_sub_le_of_rpow_interval hlocal hqR
      (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ R)
      (by simpa using hqPrime.two_le) hY hinterval
    have hlogTwoQ : Real.log 2 ≤ Real.log q :=
      Real.strictMonoOn_log.monotoneOn (by norm_num)
        (lt_trans (by norm_num) hqR)
        (by exact_mod_cast hqPrime.two_le)
    have herror : K / Real.log q ≤ K / Real.log 2 :=
      div_le_div_of_nonneg_left (by linarith : 0 ≤ K) hlogTwo hlogTwoQ
    change ∑ p ∈ Y, S.nu p / (1 - S.nu p) ≤ C
    dsimp [C]
    have hfactor : 0 ≤ R := by linarith
    calc
      (∑ p ∈ Y, S.nu p / (1 - S.nu p)) ≤
          R / 1 * (1 + K / (1 * Real.log q)) - 1 := hraw
      _ ≤ R * (1 + K / Real.log 2) := by
        have := mul_le_mul_of_nonneg_left
          (add_le_add_left herror 1) hfactor
        norm_num at this ⊢
        linarith
  have houterBound :
      (∑ p₁ ∈ Y, w p₁ *
        upperRosserAlternatingPairNormalizedInner r (c p₁)) ≤
        (4 / 5 : ℝ) + ρ / 4 := by
    have hvOne : 1 ≤ min R r := le_min (by linarith) (by linarith)
    have hout := houter S q r 1 (min R r) Y hqOuter hqPrime hlocal hr
      (by norm_num) hvOne (min_le_left _ _) hY
      (fun p hp => ⟨hcOne p (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2.le⟩)
    change (∑ p₁ ∈ Y, w p₁ *
      upperRosserAlternatingPairNormalizedInner r (c p₁)) ≤ _ at hout
    have hcont :=
      integral_inv_mul_upperRosserAlternatingPairNormalizedInner_le
        hr hvOne (min_le_right R r)
    exact hout.trans (by linarith)
  have hδmass : δ * (∑ p ∈ Y, w p) ≤ ρ / 4 := by
    have hδ0 : 0 ≤ δ := hδ.le
    calc
      δ * (∑ p ∈ Y, w p) ≤ δ * C :=
        mul_le_mul_of_nonneg_left hmass hδ0
      _ = (ρ / 4) * (C / (C + 1)) := by
        dsimp [δ]
        field_simp [hC1.ne']
      _ ≤ (ρ / 4) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hquarter.le
        exact (div_le_one hC1).2 (by linarith)
      _ = ρ / 4 := by ring
  have hsumInner :
      (∑ p₁ ∈ Y, w p₁ *
        (∑ p₀ ∈ X.filter (fun p₀ => rel p₀ p₁),
          w p₀ * LinearSieve.upperRosserAlternatingPairNormalizedKernel r
            (c p₁) (c p₀))) ≤
        (4 / 5 : ℝ) + ρ := by
    calc
      (∑ p₁ ∈ Y, w p₁ *
        (∑ p₀ ∈ X.filter (fun p₀ => rel p₀ p₁),
          w p₀ * LinearSieve.upperRosserAlternatingPairNormalizedKernel r
            (c p₁) (c p₀))) ≤
          ∑ p₁ ∈ Y, w p₁ *
            (upperRosserAlternatingPairNormalizedInner r (c p₁) + δ) := by
        apply Finset.sum_le_sum
        intro p₁ hp₁
        exact mul_le_mul_of_nonneg_left (hinnerBound p₁ hp₁)
          (nu_div_one_sub_nonneg_of_mem (hY hp₁))
      _ = (∑ p₁ ∈ Y, w p₁ *
            upperRosserAlternatingPairNormalizedInner r (c p₁)) +
          δ * ∑ p₁ ∈ Y, w p₁ := by
        calc
          (∑ p₁ ∈ Y, w p₁ *
              (upperRosserAlternatingPairNormalizedInner r (c p₁) + δ)) =
              ∑ p₁ ∈ Y, (
                (w p₁ *
                  upperRosserAlternatingPairNormalizedInner r (c p₁)) +
                    δ * w p₁) := by
              apply Finset.sum_congr rfl
              intro p₁ hp₁
              ring
          _ = (∑ p₁ ∈ Y, w p₁ *
                upperRosserAlternatingPairNormalizedInner r (c p₁)) +
              ∑ p₁ ∈ Y, δ * w p₁ := Finset.sum_add_distrib
          _ = (∑ p₁ ∈ Y, w p₁ *
                upperRosserAlternatingPairNormalizedInner r (c p₁)) +
              δ * ∑ p₁ ∈ Y, w p₁ := by rw [Finset.mul_sum]
      _ ≤ ((4 / 5 : ℝ) + ρ / 4) + ρ / 4 :=
        add_le_add houterBound hδmass
      _ ≤ (4 / 5 : ℝ) + ρ := by linarith
  change (∑ p₀ ∈ X, ∑ p₁ ∈ P.filter (rel p₀),
    w p₀ * w p₁ *
      LinearSieve.upperRosserAlternatingPairNormalizedKernel r
        (c p₁) (c p₀)) ≤ _
  rw [hswap]
  convert hsumInner using 1
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  ring

/-- Compact-ratio reverse-pair contraction in the unnormalized quadratic form
used by the Rosser recursion. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_near_le
    (K ρ R : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (hR : 3 ≤ R) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
            Real.log p₀ / Real.log q < R),
          ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) ≤
          ((4 / 5 : ℝ) + ρ) * r ^ 2 := by
  obtain ⟨Q, hQ, hnear⟩ :=
    exists_upperRosserAlternatingPairDiscrete_normalized_near_le
      K ρ R hK hρ hR
  refine ⟨Q, hQ, ?_⟩
  intro S q r P hq hqPrime hlocal hr hP hqP
  have hnormalized := hnear S q r P hq hqPrime hlocal hr hP hqP
  let X : Finset ℕ := P.filter (fun p₀ : ℕ =>
    Real.log p₀ / Real.log q < R)
  let T : ℕ → Finset ℕ := fun p₀ => P.filter (fun p₁ =>
    p₁ < p₀ ∧
      2 * (Real.log p₀ / Real.log q) <
        Real.log p₁ / Real.log q + r)
  have heq :
      (∑ p₀ ∈ X, ∑ p₁ ∈ T p₀,
        (S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁)) *
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q)) ^ 2) =
        r ^ 2 * (∑ p₀ ∈ X, ∑ p₁ ∈ T p₀,
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              LinearSieve.upperRosserAlternatingPairNormalizedKernel r
                (Real.log p₁ / Real.log q)
                (Real.log p₀ / Real.log q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p₀ hp₀
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p₁ hp₁
    unfold LinearSieve.upperRosserAlternatingPairNormalizedKernel
    have hr0 : r ≠ 0 := by linarith
    field_simp [hr0]
  change (∑ p₀ ∈ X, ∑ p₁ ∈ T p₀,
    (S.nu p₀ / (1 - S.nu p₀)) *
      (S.nu p₁ / (1 - S.nu p₁)) *
        ((r + Real.log p₁ / Real.log q +
            Real.log p₀ / Real.log q) /
          (Real.log p₀ / Real.log q)) ^ 2) ≤ _
  rw [heq]
  change (∑ p₀ ∈ X, ∑ p₁ ∈ T p₀,
    (S.nu p₀ / (1 - S.nu p₀)) *
      (S.nu p₁ / (1 - S.nu p₁)) *
        LinearSieve.upperRosserAlternatingPairNormalizedKernel r
          (Real.log p₁ / Real.log q)
          (Real.log p₀ / Real.log q)) ≤
      (4 / 5 : ℝ) + ρ at hnormalized
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left hnormalized (sq_nonneg r)

/-- A full discrete reverse Rosser pair contracts the quadratic suffix envelope
by a fixed factor strictly below one, uniformly in the terminal prime. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_le_nine_tenths
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) ≤
          (9 / 10 : ℝ) * r ^ 2 := by
  let ε : ℝ := 1 / 40
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨m, hfar⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_far_lt_uniform
      K ε (by linarith) hε
  let M : ℕ := m + 2
  let R : ℝ := (2 : ℝ) ^ M
  have hR : 3 ≤ R := by
    have hm : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    dsimp [R, M]
    rw [pow_add]
    norm_num
    linarith
  have hpowm : (2 : ℝ) ^ m ≤ R := by
    dsimp [R, M]
    rw [pow_add]
    norm_num
  obtain ⟨Q, hQ, hnear⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_near_le
      K ε R hK hε hR
  refine ⟨Q, hQ, ?_⟩
  intro S q r P hq hqPrime hlocal hr hP hqP
  let near : ℕ → Prop := fun p =>
    Real.log p / Real.log q < R
  let f : ℕ → ℝ := fun p₀ =>
    ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2
  let T : Finset ℕ := P.filter (fun p => ¬near p)
  have hT : T ⊆ P := Finset.filter_subset _ _
  have hfarCoord : ∀ p ∈ T,
      (2 : ℝ) ^ m ≤ Real.log p / Real.log q := by
    intro p hp
    have hpNot := (Finset.mem_filter.mp hp).2
    exact hpowm.trans (le_of_not_gt hpNot)
  have hfarBound : (∑ p₀ ∈ T, f p₀) < ε * r ^ 2 := by
    exact hfar S q r P T hlocal hr hqPrime hP hqP hT hfarCoord
  have hnearBound :
      (∑ p₀ ∈ P.filter near, f p₀) ≤
        ((4 / 5 : ℝ) + ε) * r ^ 2 := by
    simpa [near, f] using
      hnear S q r P hq hqPrime hlocal hr hP hqP
  have hsplit := Finset.sum_filter_add_sum_filter_not P near f
  change (∑ p₀ ∈ P, f p₀) ≤ (9 / 10 : ℝ) * r ^ 2
  rw [← hsplit]
  apply le_of_lt
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  calc
    (∑ p₀ ∈ P.filter near, f p₀) +
        ∑ p₀ ∈ P.filter (fun p => ¬near p), f p₀ <
      ((4 / 5 : ℝ) + ε) * r ^ 2 + ε * r ^ 2 :=
        add_lt_add_of_le_of_lt hnearBound (by simpa [T] using hfarBound)
    _ < (9 / 10 : ℝ) * r ^ 2 := by
      dsimp [ε]
      nlinarith

/-- The finite discrete reverse-pair iterate.  At each step the larger newly
adjoined prime becomes the terminal scale, so the residual state is renormalized
by its logarithmic ratio and the remaining ambient primes are restricted above
it. -/
noncomputable def upperRosserAlternatingPairDiscreteIterate
    (w : ℕ → ℝ) : ℕ → ℕ → ℝ → Finset ℕ → ℝ
  | 0, _q, r, _P => r ^ 2
  | k + 1, q, r, P =>
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
          p₁ < p₀ ∧
            2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
        w p₀ * w p₁ *
          upperRosserAlternatingPairDiscreteIterate w k p₀
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q))
            (P.filter (fun p => p₀ < p))

/-- The reverse-pair iterate on the relative Euler-product scale.  Unlike the
selected-weight iterate, this state keeps the complete ambient denominator and
therefore retains all primes skipped before the newly selected pair. -/
noncomputable def upperRosserAlternatingPairDiscreteRelativeIterate
    (nu : ℕ → ℝ) (k q : ℕ) (r : ℝ) (P : Finset ℕ) : ℝ :=
  upperRosserAlternatingPairDiscreteIterate nu k q r P /
    ∏ p ∈ P, (1 - nu p)

/-- The exact relative transition for adjoining the two smallest selected
primes in a reverse-built Rosser chain. -/
noncomputable def upperRosserAlternatingPairDiscreteRelativeTransition
    (nu : ℕ → ℝ) (P : Finset ℕ) (p₀ p₁ : ℕ) : ℝ :=
  (nu p₀ * nu p₁ *
      ∏ p ∈ P.filter (fun p => p₀ < p), (1 - nu p)) /
    ∏ p ∈ P, (1 - nu p)

/-- At depth zero the relative adaptive state is the quadratic envelope divided
by the full ambient Euler product. -/
theorem upperRosserAlternatingPairDiscreteRelativeIterate_zero
    (nu : ℕ → ℝ) (q : ℕ) (r : ℝ) (P : Finset ℕ) :
    upperRosserAlternatingPairDiscreteRelativeIterate nu 0 q r P =
      r ^ 2 / ∏ p ∈ P, (1 - nu p) := by
  simp [upperRosserAlternatingPairDiscreteRelativeIterate,
    upperRosserAlternatingPairDiscreteIterate]

/-- Exact successor recursion for the relative adaptive state.  The quotient of
residual and ambient Euler products is part of each transition, so the recursion
does not discard the sieve-product scale. -/
theorem upperRosserAlternatingPairDiscreteRelativeIterate_succ
    (nu : ℕ → ℝ) {k q : ℕ} {r : ℝ} {P : Finset ℕ}
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserAlternatingPairDiscreteRelativeIterate nu (k + 1) q r P =
      ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
          p₁ < p₀ ∧
            2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
        upperRosserAlternatingPairDiscreteRelativeTransition nu P p₀ p₁ *
          upperRosserAlternatingPairDiscreteRelativeIterate nu k p₀
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q))
            (P.filter (fun p => p₀ < p)) := by
  rw [upperRosserAlternatingPairDiscreteRelativeIterate,
    upperRosserAlternatingPairDiscreteIterate, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p₀ hp₀
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  have hres :
      (∏ p ∈ P.filter (fun p => p₀ < p), (1 - nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hfactor p (Finset.mem_filter.mp hp).1
  unfold upperRosserAlternatingPairDiscreteRelativeTransition
    upperRosserAlternatingPairDiscreteRelativeIterate
  field_simp [hres]

/-- Restoring the ambient Euler product cancels one relative reverse-pair
transition exactly. -/
theorem upperRosserAlternatingPairDiscreteRelativeTransition_mul_eulerProduct
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserAlternatingPairDiscreteRelativeTransition nu P p₀ p₁ *
        ∏ p ∈ P, (1 - nu p) =
      nu p₀ * nu p₁ *
        ∏ p ∈ P.filter (fun p => p₀ < p), (1 - nu p) := by
  have hprod : (∏ p ∈ P, (1 - nu p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfactor
  unfold upperRosserAlternatingPairDiscreteRelativeTransition
  field_simp [hprod]

/-- A relative reverse-pair transition is the selected pair divided by the
Euler product through the larger new prime.  This form isolates precisely the
skipped lower-prime mass that the next quantitative contraction must control. -/
theorem upperRosserAlternatingPairDiscreteRelativeTransition_eq_div_lowerProduct
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserAlternatingPairDiscreteRelativeTransition nu P p₀ p₁ =
      (nu p₀ * nu p₁) /
        ∏ p ∈ P.filter (fun p => p ≤ p₀), (1 - nu p) := by
  let L := P.filter (fun p => p ≤ p₀)
  let H := P.filter (fun p => p₀ < p)
  have hP : P = L ∪ H := by
    ext p
    simp only [L, H, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases le_or_gt p p₀ with hp₀ | hp₀
      · exact Or.inl ⟨hp, hp₀⟩
      · exact Or.inr ⟨hp, hp₀⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisjoint : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro p hpL hpH
    exact (not_lt_of_ge (Finset.mem_filter.mp hpL).2)
      (Finset.mem_filter.mp hpH).2
  have hH : (∏ p ∈ H, (1 - nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hfactor p (Finset.mem_filter.mp hp).1
  have hprod :
      (∏ p ∈ P, (1 - nu p)) =
        (∏ p ∈ L, (1 - nu p)) * ∏ p ∈ H, (1 - nu p) := by
    rw [hP, Finset.prod_union hdisjoint]
  unfold upperRosserAlternatingPairDiscreteRelativeTransition
  change
    (nu p₀ * nu p₁ * ∏ p ∈ H, (1 - nu p)) /
        ∏ p ∈ P, (1 - nu p) =
      (nu p₀ * nu p₁) / ∏ p ∈ L, (1 - nu p)
  rw [hprod]
  field_simp [hH]

/-- The Euler product through two ordered selected primes splits into the two
skipped gaps and the factors at the selected primes. -/
theorem prod_one_sub_filter_le_eq_two_gaps
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) (h10 : p₁ < p₀) :
    (∏ p ∈ P.filter (fun p => p ≤ p₀), (1 - nu p)) =
      (1 - nu p₀) * (1 - nu p₁) *
        (∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p)) *
          ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀), (1 - nu p) := by
  classical
  let A := P.filter (fun p => p < p₁)
  let B := P.filter (fun p => p₁ < p ∧ p < p₀)
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have ha := (Finset.mem_filter.mp hpA).2
    have hb := (Finset.mem_filter.mp hpB).2.1
    omega
  have hp₁A : p₁ ∉ A := by simp [A]
  have hp₁B : p₁ ∉ B := by simp [B]
  have hp₀A : p₀ ∉ A := by simp [A, Nat.not_lt_of_ge h10.le]
  have hp₀B : p₀ ∉ B := by simp [B]
  have hcarrier : P.filter (fun p => p ≤ p₀) =
      insert p₀ (insert p₁ (A ∪ B)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union, A, B]
    constructor
    · rintro ⟨hp, hle⟩
      rcases lt_trichotomy p p₁ with hlt | rfl | hgt
      · exact Or.inr (Or.inr (Or.inl ⟨hp, hlt⟩))
      · exact Or.inr (Or.inl rfl)
      · rcases eq_or_lt_of_le hle with rfl | hp₀lt
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr ⟨hp, hgt, hp₀lt⟩))
    · rintro (rfl | rfl | ⟨hp, hlt⟩ | ⟨hp, hgt, hlt⟩)
      · exact ⟨hp₀, le_rfl⟩
      · exact ⟨hp₁, h10.le⟩
      · exact ⟨hp, (hlt.trans h10).le⟩
      · exact ⟨hp, hlt.le⟩
  rw [hcarrier, Finset.prod_insert, Finset.prod_insert,
    Finset.prod_union hdisjoint]
  · simp only [A, B]
    ring
  · simp [hp₁A, hp₁B]
  · simp [hp₀A, hp₀B, h10.ne']

/-- Exact two-gap form of a relative reverse-pair transition.  Every ambient
prime below `p₀` occurs exactly once, either as one of the selected primes or in
one of the two skipped inverse-Euler products. -/
theorem
    upperRosserAlternatingPairDiscreteRelativeTransition_eq_normalized_twoGapProducts
    (nu : ℕ → ℝ) {P : Finset ℕ} {p₀ p₁ : ℕ}
    (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) (h10 : p₁ < p₀)
    (hfactor : ∀ p ∈ P, 1 - nu p ≠ 0) :
    upperRosserAlternatingPairDiscreteRelativeTransition nu P p₀ p₁ =
      (nu p₀ / (1 - nu p₀)) * (nu p₁ / (1 - nu p₁)) *
        (∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p)⁻¹) *
          ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
            (1 - nu p)⁻¹ := by
  rw [upperRosserAlternatingPairDiscreteRelativeTransition_eq_div_lowerProduct
      nu hfactor,
    prod_one_sub_filter_le_eq_two_gaps nu hp₀ hp₁ h10,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  have hA : (∏ p ∈ P.filter (fun p => p < p₁), (1 - nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hfactor p (Finset.mem_filter.mp hp).1
  have hB :
      (∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀), (1 - nu p)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hfactor p (Finset.mem_filter.mp hp).1
  field_simp [hfactor p₀ hp₀, hfactor p₁ hp₁, hA, hB]

/-- The two skipped Euler gaps form a logarithmic cocycle.  Their main
logarithmic ratios telescope from `q` directly to `p₀`; only the local-product
errors at the two successive base scales remain. -/
theorem upperRosserRelativeSkippedGaps_le_logCocycle
    {S : BoundingSieve} {K : ℝ} {q p₀ p₁ : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hK : 0 ≤ K)
    (hq : q.Prime) (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P)
    (h10 : p₁ < p₀) :
    (∏ p ∈ P.filter (fun p => p < p₁), (1 - S.nu p)⁻¹) *
        (∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
          (1 - S.nu p)⁻¹) ≤
      (Real.log p₀ / Real.log ((q : ℝ) + 1)) *
        (1 + K / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((p₁ : ℝ) + 1)) := by
  have hp₁Prime : p₁.Prime := Nat.prime_of_mem_primeFactors (hP hp₁)
  have hp₀Prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
  have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
  have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀Prime.pos
  have hqOne : (1 : ℝ) < (q : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_add_one_iff.mpr hq.pos)
  have hp₁One : (1 : ℝ) < (p₁ : ℝ) + 1 := by
    exact_mod_cast (Nat.lt_add_one_iff.mpr hp₁Prime.pos)
  have hlogq : 0 < Real.log ((q : ℝ) + 1) := Real.log_pos hqOne
  have hlogp₁One : 0 < Real.log ((p₁ : ℝ) + 1) := Real.log_pos hp₁One
  have hA := prod_inv_one_sub_nu_le_of_subset_interval hlocal
    (T := P.filter (fun p => p < p₁))
    (z₁ := (q : ℝ) + 1) (z₂ := (p₁ : ℝ))
    (by exact_mod_cast (hq.two_le.trans (Nat.le_succ q)))
    (by exact_mod_cast (Nat.add_one_le_iff.mpr (hqP p₁ hp₁)))
    (fun p hp => hP (Finset.mem_filter.mp hp).1)
    (fun p hp => by
      rcases Finset.mem_filter.mp hp with ⟨hpP, hpLt⟩
      exact
        ⟨by exact_mod_cast (Nat.add_one_le_iff.mpr (hqP p hpP)),
          by exact_mod_cast hpLt⟩)
  have hB := prod_inv_one_sub_nu_le_of_subset_interval hlocal
    (T := P.filter (fun p => p₁ < p ∧ p < p₀))
    (z₁ := (p₁ : ℝ) + 1) (z₂ := (p₀ : ℝ))
    (by exact_mod_cast (hp₁Prime.two_le.trans (Nat.le_succ p₁)))
    (by exact_mod_cast (Nat.add_one_le_iff.mpr h10))
    (fun p hp => hP (Finset.mem_filter.mp hp).1)
    (fun p hp => by
      rcases Finset.mem_filter.mp hp with ⟨hpP, hp₁p, hpp₀⟩
      exact
        ⟨by exact_mod_cast (Nat.add_one_le_iff.mpr hp₁p),
          by exact_mod_cast hpp₀⟩)
  have hinvNonneg : ∀ p ∈ P, 0 ≤ (1 - S.nu p)⁻¹ := by
    intro p hp
    have hpS := hP hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
    exact inv_nonneg.mpr
      (sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd).le)
  have hBnonneg :
      0 ≤ ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
        (1 - S.nu p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p hp
    exact hinvNonneg p (Finset.mem_filter.mp hp).1
  have hAcoef :
      0 ≤ Real.log p₁ / Real.log ((q : ℝ) + 1) *
        (1 + K / Real.log ((q : ℝ) + 1)) := by
    positivity
  have hBcoef :
      0 ≤ Real.log p₀ / Real.log ((p₁ : ℝ) + 1) *
        (1 + K / Real.log ((p₁ : ℝ) + 1)) := by
    positivity
  have hmul := mul_le_mul hA hB hBnonneg hAcoef
  have hp₁addpos : (0 : ℝ) < (p₁ : ℝ) + 1 := zero_lt_one.trans hp₁One
  have hlogmono : Real.log (p₁ : ℝ) ≤ Real.log ((p₁ : ℝ) + 1) :=
    Real.strictMonoOn_log.monotoneOn hp₁pos hp₁addpos (by norm_num)
  have hratio : Real.log (p₁ : ℝ) / Real.log ((p₁ : ℝ) + 1) ≤ 1 :=
    (div_le_one hlogp₁One).2 hlogmono
  have hmain :
      (Real.log p₁ / Real.log ((q : ℝ) + 1)) *
          (Real.log p₀ / Real.log ((p₁ : ℝ) + 1)) ≤
        Real.log p₀ / Real.log ((q : ℝ) + 1) := by
    calc
      _ = (Real.log p₀ / Real.log ((q : ℝ) + 1)) *
          (Real.log p₁ / Real.log ((p₁ : ℝ) + 1)) := by
            field_simp [hlogq.ne', hlogp₁One.ne']
      _ ≤ (Real.log p₀ / Real.log ((q : ℝ) + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have herr : 0 ≤ (1 + K / Real.log ((q : ℝ) + 1)) *
      (1 + K / Real.log ((p₁ : ℝ) + 1)) := by
    positivity
  calc
    _ ≤ (Real.log p₁ / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) *
        (Real.log p₀ / Real.log ((p₁ : ℝ) + 1) *
          (1 + K / Real.log ((p₁ : ℝ) + 1))) := hmul
    _ = ((Real.log p₁ / Real.log ((q : ℝ) + 1)) *
          (Real.log p₀ / Real.log ((p₁ : ℝ) + 1))) *
        ((1 + K / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((p₁ : ℝ) + 1))) := by ring
    _ ≤ (Real.log p₀ / Real.log ((q : ℝ) + 1)) *
        ((1 + K / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((p₁ : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right hmain herr
    _ = _ := by ring

/-- Quantitative two-gap bound for one relative reverse-pair transition.  This
is the cocycle-preserving replacement for charging the whole lower interval as
an unrelated factor at every recursive step. -/
theorem upperRosserAlternatingPairDiscreteRelativeTransition_le_logCocycle
    {S : BoundingSieve} {K : ℝ} {q p₀ p₁ : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hK : 0 ≤ K)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P)
    (h10 : p₁ < p₀) :
    upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ ≤
      ((S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁))) *
      ((Real.log p₀ / Real.log ((q : ℝ) + 1)) *
        (1 + K / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((p₁ : ℝ) + 1))) := by
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpS := hP hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd))
  rw [
    upperRosserAlternatingPairDiscreteRelativeTransition_eq_normalized_twoGapProducts
      S.nu hp₀ hp₁ h10 hfactor]
  have hweight :
      0 ≤ (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) :=
    mul_nonneg (nu_div_one_sub_nonneg_of_mem (hP hp₀))
      (nu_div_one_sub_nonneg_of_mem (hP hp₁))
  have hgaps := upperRosserRelativeSkippedGaps_le_logCocycle
    hlocal hK (Nat.prime_of_mem_primeFactors hq) hP hqP hp₀ hp₁ h10
  calc
    ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁)) *
        ∏ p ∈ P.filter (fun p => p < p₁), (1 - S.nu p)⁻¹) *
          ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
            (1 - S.nu p)⁻¹ =
      ((S.nu p₀ / (1 - S.nu p₀)) * (S.nu p₁ / (1 - S.nu p₁))) *
        ((∏ p ∈ P.filter (fun p => p < p₁), (1 - S.nu p)⁻¹) *
          ∏ p ∈ P.filter (fun p => p₁ < p ∧ p < p₀),
            (1 - S.nu p)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgaps hweight

/-- Multiplying by the natural terminal-scale ratio cancels the full main
logarithmic growth of a relative transition.  This is the one-step Lyapunov
transfer needed to iterate the completed operator without paying a fresh
Euler-product factor at every pair. -/
theorem
    upperRosserAlternatingPairDiscreteRelativeTransition_mul_logScale_le
    {S : BoundingSieve} {K : ℝ} {q p₀ p₁ : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hK : 0 ≤ K)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P)
    (h10 : p₁ < p₀) :
    upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ *
        (Real.log ((q : ℝ) + 1) / Real.log p₀) ≤
      ((S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁))) *
        ((1 + K / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((p₁ : ℝ) + 1))) := by
  have hp₀Prime : p₀.Prime := Nat.prime_of_mem_primeFactors (hP hp₀)
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hlogq : 0 < Real.log ((q : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (Nat.lt_add_one_iff.mpr hqPrime.pos))
  have hlogp₀ : 0 < Real.log p₀ :=
    Real.log_pos (by exact_mod_cast hp₀Prime.one_lt)
  have htransition :=
    upperRosserAlternatingPairDiscreteRelativeTransition_le_logCocycle
      hlocal hK hq hP hqP hp₀ hp₁ h10
  have hscale : 0 ≤ Real.log ((q : ℝ) + 1) / Real.log p₀ :=
    div_nonneg hlogq.le hlogp₀.le
  calc
    _ ≤ (((S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁))) *
        ((Real.log p₀ / Real.log ((q : ℝ) + 1)) *
          (1 + K / Real.log ((q : ℝ) + 1)) *
            (1 + K / Real.log ((p₁ : ℝ) + 1)))) *
        (Real.log ((q : ℝ) + 1) / Real.log p₀) :=
      mul_le_mul_of_nonneg_right htransition hscale
    _ = _ := by
      field_simp [hlogq.ne', hlogp₀.ne']

/-- The local-product hypothesis gives the first quantitative bound for a
relative reverse-pair transition.  It charges exactly one interval factor from
the previous terminal prime through the larger new prime; retaining this factor
inside the recursive state avoids the invalid absolute-tail cancellation. -/
theorem upperRosserAlternatingPairDiscreteRelativeTransition_le_localProduct
    {S : BoundingSieve} {K : ℝ} {q p₀ p₁ : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hp₀ : p₀ ∈ P) (hp₁ : p₁ ∈ P) :
    upperRosserAlternatingPairDiscreteRelativeTransition S.nu P p₀ p₁ ≤
      (S.nu p₀ * S.nu p₁) *
        (Real.log ((p₀ : ℝ) + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) := by
  let L := P.filter (fun p => p ≤ p₀)
  have hfactor : ∀ p ∈ P, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpS := hP hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
    exact ne_of_gt (sub_pos.mpr (S.nu_lt_one_of_prime p hpPrime hpDvd))
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq₀ : (2 : ℝ) ≤ (q : ℝ) + 1 := by
    exact_mod_cast (hqPrime.two_le.trans (Nat.le_succ q))
  have hqp₀ : (q : ℝ) + 1 ≤ (p₀ : ℝ) + 1 := by
    exact_mod_cast (Nat.add_le_add_right (Nat.le_of_lt (hqP p₀ hp₀)) 1)
  have hLsubset : L ⊆ S.prodPrimes.primeFactors := by
    intro p hp
    exact hP (Finset.mem_filter.mp hp).1
  have hLinterval : ∀ p ∈ L,
      (q : ℝ) + 1 ≤ (p : ℝ) ∧ (p : ℝ) < (p₀ : ℝ) + 1 := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    constructor
    · exact_mod_cast (Nat.add_one_le_iff.mpr (hqP p hp'.1))
    · exact_mod_cast (Nat.lt_add_one_iff.mpr hp'.2)
  have hproduct :=
    prod_inv_one_sub_nu_le_of_subset_interval hlocal hq₀ hqp₀
      hLsubset hLinterval
  rw [upperRosserAlternatingPairDiscreteRelativeTransition_eq_div_lowerProduct
    S.nu hfactor]
  change
    (S.nu p₀ * S.nu p₁) / ∏ p ∈ L, (1 - S.nu p) ≤ _
  rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
  exact mul_le_mul_of_nonneg_left hproduct
    (mul_nonneg
      (by
        have hpS := hP hp₀
        have hpPrime : p₀.Prime := Nat.prime_of_mem_primeFactors hpS
        have hpDvd : p₀ ∣ S.prodPrimes :=
          (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
        exact (S.nu_pos_of_prime p₀ hpPrime hpDvd).le)
      (by
        have hpS := hP hp₁
        have hpPrime : p₁.Prime := Nat.prime_of_mem_primeFactors hpS
        have hpDvd : p₁ ∣ S.prodPrimes :=
          (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hpS |>.2
        exact (S.nu_pos_of_prime p₁ hpPrime hpDvd).le))

/-- The ordered reverse-pair condition keeps the renormalized residual ratio
above three.  Both geometric inductions use this same admissibility step. -/
private lemma upperRosserAlternatingPairDiscrete_nextRatio_ge_three
    {q p₀ p₁ : ℕ} {r : ℝ}
    (hqPrime : q.Prime) (hp₀Prime : p₀.Prime) (hp₁Prime : p₁.Prime)
    (hqp₁ : q < p₁) (h10 : p₁ < p₀)
    (hpair : 2 * (Real.log p₀ / Real.log q) < Real.log p₁ / Real.log q + r) :
    3 ≤ (r + Real.log p₁ / Real.log q + Real.log p₀ / Real.log q) /
      (Real.log p₀ / Real.log q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀Prime.pos
  have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
  have hlogq : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast hqPrime.one_lt)
  have hy :
      Real.log p₁ / Real.log q ∈ Set.Ioo (1 : ℝ) r := by
    have hqy :
        Real.log q < Real.log p₁ :=
      (Real.strictMonoOn_log.lt_iff_lt hqpos hp₁pos).2
        (by exact_mod_cast hqp₁)
    have hyx :
        Real.log p₁ / Real.log q <
          Real.log p₀ / Real.log q := by
      apply (div_lt_div_iff_of_pos_right hlogq).2
      exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
        (by exact_mod_cast h10)
    refine ⟨(lt_div_iff₀ hlogq).2 ?_, ?_⟩
    · simpa using hqy
    · linarith [hpair, hyx]
  have hx :
      Real.log p₀ / Real.log q ∈
        Set.Ioo (Real.log p₁ / Real.log q)
          ((Real.log p₁ / Real.log q + r) / 2) := by
    constructor
    · apply (div_lt_div_iff_of_pos_right hlogq).2
      exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
        (by exact_mod_cast h10)
    · linarith [hpair]
  exact (LinearSieve.upperRosserAlternatingPair_nextRatio_gt_three hy hx).le

/-- Iterating the uniform discrete reverse-pair contraction gives a geometric
depth bound.  This is the quantitative tail estimate for reverse-built Rosser
chains whose terminal prime is above the uniform local-product cutoff. -/
theorem exists_upperRosserAlternatingPairDiscreteIterate_le
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k : ℕ) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        upperRosserAlternatingPairDiscreteIterate
            (fun p => S.nu p / (1 - S.nu p)) k q r P ≤
          (9 / 10 : ℝ) ^ k * r ^ 2 := by
  obtain ⟨Q, hQ, hcontract⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_le_nine_tenths K hK
  refine ⟨Q, hQ, ?_⟩
  intro S k
  induction k with
  | zero =>
      intro q r P hq hqPrime hlocal hr hP hqP
      simp [upperRosserAlternatingPairDiscreteIterate]
  | succ k ih =>
      intro q r P hq hqPrime hlocal hr hP hqP
      rw [upperRosserAlternatingPairDiscreteIterate]
      have hterms :
          (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                upperRosserAlternatingPairDiscreteIterate
                  (fun p => S.nu p / (1 - S.nu p)) k p₀
                  ((r + Real.log p₁ / Real.log q +
                      Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q))
                  (P.filter (fun p => p₀ < p))) ≤
            ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                ((9 / 10 : ℝ) ^ k *
                  (((r + Real.log p₁ / Real.log q +
                      Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q)) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p₀ hp₀
        apply Finset.sum_le_sum
        intro p₁ hp₁
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₀Prime : p₀.Prime :=
          Nat.prime_of_mem_primeFactors (hP hp₀)
        have hnext := upperRosserAlternatingPairDiscrete_nextRatio_ge_three
          hqPrime hp₀Prime (Nat.prime_of_mem_primeFactors (hP hp₁'.1))
          (hqP p₁ hp₁'.1) hp₁'.2.1 hp₁'.2.2
        have hiter := ih p₀
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q))
          (P.filter (fun p => p₀ < p))
          (hq.trans (by exact_mod_cast (hqP p₀ hp₀).le)) hp₀Prime hlocal hnext
          (fun p hp => hP (Finset.mem_filter.mp hp).1)
          (fun p hp => (Finset.mem_filter.mp hp).2)
        exact mul_le_mul_of_nonneg_left hiter
          (mul_nonneg
            (nu_div_one_sub_nonneg_of_mem (hP hp₀))
            (nu_div_one_sub_nonneg_of_mem (hP hp₁'.1)))
      calc
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              upperRosserAlternatingPairDiscreteIterate
                (fun p => S.nu p / (1 - S.nu p)) k p₀
                ((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q))
                (P.filter (fun p => p₀ < p))) ≤
            ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                ((9 / 10 : ℝ) ^ k *
                  (((r + Real.log p₁ / Real.log q +
                      Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q)) ^ 2)) := hterms
        _ = (9 / 10 : ℝ) ^ k *
            (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                (((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          ring
        _ ≤ (9 / 10 : ℝ) ^ k * ((9 / 10 : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_left
            (hcontract S q r P hq hqPrime hlocal hr hP hqP) (by positivity)
        _ = (9 / 10 : ℝ) ^ (k + 1) * r ^ 2 := by
          rw [pow_succ]
          ring

/-- A coarse reverse-pair bound valid at every prime terminal.  Unlike the
contractive estimate, its constant need not be below one; it is used only for
the finitely many steps before the terminal prime reaches the uniform
Stieltjes cutoff. -/
theorem upperRosserAlternatingPairDiscrete_quadratic_le_coarse
    {S : BoundingSieve} {K r : ℝ} {q : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hK : 0 ≤ K)
    (hr : 3 ≤ r) (hq : q.Prime)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) :
    (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
      (18 * (1 + K / Real.log 2) * (1 + 2 * (K / Real.log 2))) * r ^ 2 := by
  let η : ℝ := K / Real.log 2
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hη : 0 ≤ η := div_nonneg hK hlogTwo.le
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlogq : 0 < Real.log q :=
    Real.log_pos (by exact_mod_cast hq.one_lt)
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log q := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hqPos
      (by exact_mod_cast hq.two_le)
  have herror : K / Real.log q ≤ η :=
    div_le_div_of_nonneg_left hK hlogTwo hlogTwoLe
  have hfar : ∀ p ∈ P,
      (2 : ℝ) ^ (0 : ℕ) ≤ Real.log p / Real.log q := by
    intro p hp
    rw [pow_zero]
    apply (le_div_iff₀ hlogq).2
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp)
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hqp : (q : ℝ) ≤ p := by exact_mod_cast (hqP p hp).le
    simpa using Real.strictMonoOn_log.monotoneOn hqPos hpPos hqp
  have hbound :=
    upperRosserAlternatingPairDiscrete_quadratic_far_le
      hlocal hK hη hr hq herror hP hqP (show P ⊆ P from fun _ hp => hp) hfar
  simpa [η] using hbound

/-- After `n` preliminary reverse pairs, the terminal prime is at least `2n`
larger.  Thus only finitely many coarse steps are needed before every remaining
pair contracts geometrically. -/
theorem exists_upperRosserAlternatingPairDiscreteIterate_shifted_le
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k n : ℕ) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        Q ≤ (q : ℝ) + 2 * n → q.Prime →
        HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        upperRosserAlternatingPairDiscreteIterate
            (fun p => S.nu p / (1 - S.nu p)) (k + n) q r P ≤
          (18 * (1 + K / Real.log 2) * (1 + 2 * (K / Real.log 2))) ^ n *
            (9 / 10 : ℝ) ^ k * r ^ 2 := by
  obtain ⟨Q, hQ, hiter⟩ :=
    exists_upperRosserAlternatingPairDiscreteIterate_le K hK
  refine ⟨Q, hQ, ?_⟩
  intro S k n
  induction n with
  | zero =>
      intro q r P hreach hqPrime hlocal hr hP hqP
      simpa using hiter S k q r P (by simpa using hreach)
        hqPrime hlocal hr hP hqP
  | succ n ih =>
      intro q r P hreach hqPrime hlocal hr hP hqP
      rw [show k + (n + 1) = (k + n) + 1 by omega,
        upperRosserAlternatingPairDiscreteIterate]
      have hterms :
          (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                upperRosserAlternatingPairDiscreteIterate
                  (fun p => S.nu p / (1 - S.nu p)) (k + n) p₀
                  ((r + Real.log p₁ / Real.log q +
                      Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q))
                  (P.filter (fun p => p₀ < p))) ≤
            ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                ((18 * (1 + K / Real.log 2) *
                    (1 + 2 * (K / Real.log 2))) ^ n *
                  (9 / 10 : ℝ) ^ k *
                  (((r + Real.log p₁ / Real.log q +
                      Real.log p₀ / Real.log q) /
                    (Real.log p₀ / Real.log q)) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p₀ hp₀
        apply Finset.sum_le_sum
        intro p₁ hp₁
        have hp₁' := Finset.mem_filter.mp hp₁
        have hp₀Prime : p₀.Prime :=
          Nat.prime_of_mem_primeFactors (hP hp₀)
        have hnext := upperRosserAlternatingPairDiscrete_nextRatio_ge_three
          hqPrime hp₀Prime (Nat.prime_of_mem_primeFactors (hP hp₁'.1))
          (hqP p₁ hp₁'.1) hp₁'.2.1 hp₁'.2.2
        have hqp₁ : q < p₁ := hqP p₁ hp₁'.1
        have hp₁p₀ : p₁ < p₀ := hp₁'.2.1
        have hp₀ge : q + 2 ≤ p₀ := by omega
        have hstep :
            (q : ℝ) + 2 * (n + 1) ≤ (p₀ : ℝ) + 2 * n := by
          have hp₀ge' : (q : ℝ) + 2 ≤ p₀ := by exact_mod_cast hp₀ge
          linarith
        have hreach' :
            Q ≤ (q : ℝ) + 2 * ((n : ℝ) + 1) := by
          simpa [Nat.cast_add, Nat.cast_one] using hreach
        have hiter := ih p₀
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q))
          (P.filter (fun p => p₀ < p))
          (hreach'.trans hstep) hp₀Prime hlocal hnext
          (fun p hp => hP (Finset.mem_filter.mp hp).1)
          (fun p hp => (Finset.mem_filter.mp hp).2)
        exact mul_le_mul_of_nonneg_left hiter
          (mul_nonneg
            (nu_div_one_sub_nonneg_of_mem (hP hp₀))
            (nu_div_one_sub_nonneg_of_mem (hP hp₁'.1)))
      let B : ℝ :=
        18 * (1 + K / Real.log 2) * (1 + 2 * (K / Real.log 2))
      let C : ℝ := B ^ n * (9 / 10 : ℝ) ^ k
      have hcoarse :=
        upperRosserAlternatingPairDiscrete_quadratic_le_coarse
          hlocal (zero_le_one.trans hK) hr hqPrime hP hqP
      calc
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              upperRosserAlternatingPairDiscreteIterate
                (fun p => S.nu p / (1 - S.nu p)) (k + n) p₀
                ((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q))
                (P.filter (fun p => p₀ < p))) ≤
            ∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                (C * (((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2)) := by
            simpa [B, C] using hterms
        _ = C * (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
              p₁ < p₀ ∧
                2 * (Real.log p₀ / Real.log q) <
                  Real.log p₁ / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                (((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₀ hp₀
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p₁ hp₁
          ring
        _ ≤ C * (B * r ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · simpa [B] using hcoarse
          · dsimp [C, B]
            positivity
        _ = (18 * (1 + K / Real.log 2) *
              (1 + 2 * (K / Real.log 2))) ^ (n + 1) *
            (9 / 10 : ℝ) ^ k * r ^ 2 := by
          dsimp [C, B]
          rw [pow_succ]
          ring

/-- Uniformly in the initial terminal prime, a fixed number of preliminary
reverse pairs reaches the contractive range.  Every later depth therefore has
one geometric envelope, with a constant depending only on the dimension-one
local-product constant. -/
theorem exists_upperRosserAlternatingPairDiscreteIterate_eventually_geometric
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : BoundingSieve) (k : ℕ) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        upperRosserAlternatingPairDiscreteIterate
            (fun p => S.nu p / (1 - S.nu p)) (k + N) q r P ≤
          C * (9 / 10 : ℝ) ^ k * r ^ 2 := by
  obtain ⟨Q, hQ, hshift⟩ :=
    exists_upperRosserAlternatingPairDiscreteIterate_shifted_le K hK
  let N : ℕ := ⌈Q⌉₊
  let C : ℝ :=
    (18 * (1 + K / Real.log 2) * (1 + 2 * (K / Real.log 2))) ^ N
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨N, C, hC, ?_⟩
  intro S k q r P hqPrime hlocal hr hP hqP
  have hreach : Q ≤ (q : ℝ) + 2 * N := by
    have hQN : Q ≤ (N : ℝ) := by
      simpa [N] using (Nat.le_ceil Q)
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith
  simpa [C] using
    hshift S k N q r P hreach hqPrime hlocal hr hP hqP

end MathlibNt.SieveTheory.SwitchingPrinciple
