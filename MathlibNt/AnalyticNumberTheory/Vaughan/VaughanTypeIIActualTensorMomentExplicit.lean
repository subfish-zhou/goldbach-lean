import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorMoment
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergDenominatorHarmonic

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight

noncomputable section

private def divisorTripleSupport (X t : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 X).product ((Finset.Icc 1 X).product (Finset.Icc 1 X))).filter
    fun guv => guv.1 * guv.2.1 * guv.2.2 ∣ t

private def divisorPairToTriple (ab : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let g := Nat.gcd ab.1 ab.2
  (g, ab.1 / g, ab.2 / g)

private lemma divisorPairToTriple_injective :
    Function.Injective divisorPairToTriple := by
  intro ab₁ ab₂ h
  rcases ab₁ with ⟨a₁, b₁⟩
  rcases ab₂ with ⟨a₂, b₂⟩
  dsimp [divisorPairToTriple] at h ⊢
  have hg : Nat.gcd a₁ b₁ = Nat.gcd a₂ b₂ := by
    simpa using congrArg Prod.fst h
  have hu : a₁ / Nat.gcd a₁ b₁ = a₂ / Nat.gcd a₂ b₂ := by
    simpa [hg] using congrArg (fun x => x.2.1) h
  have hv : b₁ / Nat.gcd a₁ b₁ = b₂ / Nat.gcd a₂ b₂ := by
    simpa [hg] using congrArg (fun x => x.2.2) h
  have ha : a₁ = a₂ := by
    have hmul :
        Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) =
          Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := by
      simpa [hg] using congrArg (fun n => Nat.gcd a₁ b₁ * n) hu
    calc
      a₁ = Nat.gcd a₁ b₁ * (a₁ / Nat.gcd a₁ b₁) := by
        symm
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ b₁)
      _ = Nat.gcd a₂ b₂ * (a₂ / Nat.gcd a₂ b₂) := hmul
      _ = a₂ := by
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a₂ b₂)
  have hb : b₁ = b₂ := by
    have hmul :
        Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) =
          Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := by
      simpa [hg] using congrArg (fun n => Nat.gcd a₁ b₁ * n) hv
    calc
      b₁ = Nat.gcd a₁ b₁ * (b₁ / Nat.gcd a₁ b₁) := by
        symm
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ b₁)
      _ = Nat.gcd a₂ b₂ * (b₂ / Nat.gcd a₂ b₂) := hmul
      _ = b₂ := by
        exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ b₂)
  simp [ha, hb]

private lemma divisorPairToTriple_mem
    {X t a b : ℕ} (ht : 0 < t) (htX : t ≤ X)
    (ha : a ∈ t.divisors) (hb : b ∈ t.divisors) :
    divisorPairToTriple (a, b) ∈ divisorTripleSupport X t := by
  have hadvd : a ∣ t := (Nat.mem_divisors.mp ha).1
  have hbdvd : b ∣ t := (Nat.mem_divisors.mp hb).1
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd ht
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd ht
  let g := Nat.gcd a b
  let u := a / g
  let v := b / g
  have hgpos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_left b hapos
  have hugt : 0 < u := by
    dsimp [u]
    exact Nat.div_pos (Nat.gcd_le_left b hapos) hgpos
  have hvgt : 0 < v := by
    dsimp [v]
    exact Nat.div_pos (Nat.gcd_le_right a hbpos) hgpos
  have hgle : g ≤ t := Nat.le_of_dvd ht (Nat.dvd_trans (Nat.gcd_dvd_left a b) hadvd)
  have hule : u ≤ t := by
    dsimp [u]
    exact (Nat.div_le_self a g).trans (Nat.le_of_dvd ht hadvd)
  have hvle : v ≤ t := by
    dsimp [v]
    exact (Nat.div_le_self b g).trans (Nat.le_of_dvd ht hbdvd)
  have hlcm : Nat.lcm a b = g * u * v := by
    have hmul : g * Nat.lcm a b = g * (g * u * v) := by
      calc
        g * Nat.lcm a b = a * b := by
          dsimp [g]
          exact Nat.gcd_mul_lcm a b
        _ = (g * u) * (g * v) := by
          dsimp [g, u, v]
          rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),
            Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
        _ = g * (g * u * v) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  change (g, u, v) ∈ divisorTripleSupport X t
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hgpos, hgle.trans htX⟩,
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hugt, hule.trans htX⟩,
            Finset.mem_Icc.mpr ⟨hvgt, hvle.trans htX⟩⟩⟩
  · change g * u * v ∣ t
    rw [← hlcm]
    exact Nat.lcm_dvd hadvd hbdvd

private lemma divisorSquarePrefix_term_le_tripleCount
    {X t : ℕ} (ht : 0 < t) (htX : t ≤ X) :
    ((t.divisors.card : ℝ) ^ 2) ≤
      ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
        if g * u * v ∣ t then (1 : ℝ) else 0 := by
  let S : Finset (ℕ × ℕ) := t.divisors.product t.divisors
  let T : Finset (ℕ × ℕ × ℕ) := divisorTripleSupport X t
  have himage : S.image divisorPairToTriple ⊆ T := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ab, hab, rfl⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact divisorPairToTriple_mem ht htX ha hb
  have hcard : S.card ≤ T.card := by
    calc
      S.card = (S.image divisorPairToTriple).card := by
        symm
        exact Finset.card_image_of_injective S divisorPairToTriple_injective
      _ ≤ T.card := Finset.card_le_card himage
  have hsum :
      ((T.card : ℕ) : ℝ) =
        ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          if g * u * v ∣ t then (1 : ℝ) else 0 := by
    dsimp [T, divisorTripleSupport]
    simp only [Finset.card_filter, Finset.sum_product, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  calc
    ((t.divisors.card : ℝ) ^ 2) = (S.card : ℝ) := by
      simp [S, Finset.card_product, pow_two]
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          if g * u * v ∣ t then (1 : ℝ) else 0 := hsum

theorem liuHarmonic_le_three_log_add_one (X : ℕ) :
    liuHarmonic X ≤ 3 * Real.log (X + 1 : ℕ) := by
  cases X with
  | zero => simp [liuHarmonic_zero]
  | succ n =>
      have h1 : liuHarmonic (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) :=
        liuHarmonic_le_one_add_log (n + 1)
      have hlog : Real.log (n + 1 : ℕ) ≤ Real.log (n + 2 : ℕ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.succ_le_succ (Nat.le_succ n)
      have htwoThird : (2 / 3 : ℝ) ≤ Real.log (n + 2 : ℕ) := by
        have hbase : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
          have : (2 * (1 : ℝ) / (1 + 2)) ≤ Real.log (1 + (1 : ℝ)) :=
            Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
          norm_num at this
          simpa using this
        have hmono : Real.log (2 : ℝ) ≤ Real.log (n + 2 : ℕ) := by
          apply Real.log_le_log
          · norm_num
          · exact_mod_cast (show (2 : ℕ) ≤ n + 2 by omega)
        exact hbase.trans hmono
      have hone : (1 : ℝ) ≤ (3 / 2 : ℝ) * Real.log (n + 2 : ℕ) := by
        nlinarith
      have hmain : 1 + Real.log (n + 1 : ℕ) ≤ 3 * Real.log (n + 2 : ℕ) := by
        have : 1 + Real.log (n + 1 : ℕ) ≤
            (3 / 2 : ℝ) * Real.log (n + 2 : ℕ) + Real.log (n + 2 : ℕ) := by
          linarith
        linarith
      exact h1.trans hmain

private theorem sum_dvd_indicator_Icc'
    (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0) = (R / e : ℕ) := by
  rw [← Finset.sum_filter]
  rw [sum_multiples_Icc_reindex (R := ℝ) (F := fun _ => (1 : ℝ))
    (k := e) (y := R) he]
  simp

theorem sum_Icc_int_toNat_eq_sum_Icc
    {F : ℕ → ℝ} (X : ℕ) :
    (∑ t ∈ Finset.Icc (1 : ℤ) X, F t.toNat) =
      ∑ n ∈ Finset.Icc 1 X, F n := by
  refine Finset.sum_bij (fun t _ => t.toNat) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_Icc]
    constructor
    · have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      have : (1 : ℤ) ≤ (t.toNat : ℤ) := by
        simpa [htcast] using (Finset.mem_Icc.mp ht).1
      exact_mod_cast this
    · have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      exact_mod_cast htcast.trans_le (Finset.mem_Icc.mp ht).2
  · intro t₁ ht₁ t₂ ht₂ h
    have ht₁pos : 0 < t₁ := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht₁).1
    have ht₂pos : 0 < t₂ := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht₂).1
    exact Int.toNat_of_nonneg ht₁pos.le ▸ Int.toNat_of_nonneg ht₂pos.le ▸ by
      exact_mod_cast h
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simpa [Finset.mem_Icc] using hn
  · intro t ht
    simp

private theorem divisorSquarePrefix_eq_nat (X : ℕ) :
    divisorSquarePrefix X =
      ∑ t ∈ Finset.Icc 1 X, ((t.divisors.card : ℝ) ^ 2) := by
  unfold divisorSquarePrefix
  simpa using sum_Icc_int_toNat_eq_sum_Icc
    (F := fun t => ((t.divisors.card : ℝ) ^ 2)) X

private theorem divisorSquarePrefix_le_cube_harmonic (X : ℕ) :
    divisorSquarePrefix X ≤ (X : ℝ) * liuHarmonic X ^ 3 := by
  rw [divisorSquarePrefix_eq_nat]
  calc
    (∑ t ∈ Finset.Icc 1 X, ((t.divisors.card : ℝ) ^ 2)) ≤
        ∑ t ∈ Finset.Icc 1 X,
          ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
            if g * u * v ∣ t then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      exact divisorSquarePrefix_term_le_tripleCount
        (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          ∑ t ∈ Finset.Icc 1 X, if g * u * v ∣ t then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          ((X / (g * u * v) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have hgpos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1
      have hupos : 0 < u := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hu).1
      have hvpos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hv).1
      exact sum_dvd_indicator_Icc' X (g * u * v)
        (Nat.mul_pos (Nat.mul_pos hgpos hupos) hvpos)
    _ ≤ ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X, ∑ v ∈ Finset.Icc 1 X,
          (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hgR : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      have huR : (0 : ℝ) < u := by exact_mod_cast (Finset.mem_Icc.mp hu).1
      have hvR : (0 : ℝ) < v := by exact_mod_cast (Finset.mem_Icc.mp hv).1
      have hdiv : ((X / (g * u * v) : ℕ) : ℝ) ≤ (X : ℝ) / (g * u * v) := by
        simpa [Nat.cast_mul, mul_assoc] using
          (Nat.cast_div_le (α := ℝ) (m := X) (n := g * u * v))
      have hfac :
          (X : ℝ) / (g * u * v) =
            (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := by
        field_simp [hgR.ne', huR.ne', hvR.ne']
      calc
        ((X / (g * u * v) : ℕ) : ℝ) ≤ (X : ℝ) / (g * u * v) := hdiv
        _ = (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹ := hfac
    _ = (X : ℝ) * liuHarmonic X ^ 3 := by
      let S : Finset ℕ := Finset.Icc 1 X
      let H : ℝ := ∑ n ∈ S, (n : ℝ)⁻¹
      have hinner :
          ∀ g ∈ S,
            (∑ u ∈ S, ∑ v ∈ S,
              (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹) =
              (X : ℝ) * (g : ℝ)⁻¹ * H * H := by
        intro g hg
        calc
          (∑ u ∈ S, ∑ v ∈ S,
              (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹) =
              ∑ u ∈ S, ((X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹) * H := by
                apply Finset.sum_congr rfl
                intro u hu
                simpa [H, mul_assoc] using
                  (show
                    (∑ v ∈ S,
                      (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹) =
                      ((X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹) *
                        ∑ v ∈ S, (v : ℝ)⁻¹ by
                    rw [← Finset.mul_sum])
          _ = (∑ u ∈ S, (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹) * H := by
                rw [← Finset.sum_mul]
          _ = (((X : ℝ) * (g : ℝ)⁻¹) * ∑ u ∈ S, (u : ℝ)⁻¹) * H := by
                simpa [mul_assoc] using congrArg (fun z : ℝ => z * H) <|
                  (show
                    (∑ u ∈ S, (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹) =
                      ((X : ℝ) * (g : ℝ)⁻¹) * ∑ u ∈ S, (u : ℝ)⁻¹ by
                    rw [← Finset.mul_sum])
          _ = (X : ℝ) * (g : ℝ)⁻¹ * H * H := by
                simp [H, mul_assoc]
      calc
        (∑ g ∈ S, ∑ u ∈ S, ∑ v ∈ S,
            (X : ℝ) * (g : ℝ)⁻¹ * (u : ℝ)⁻¹ * (v : ℝ)⁻¹) =
            ∑ g ∈ S, (X : ℝ) * (g : ℝ)⁻¹ * H * H := by
              apply Finset.sum_congr rfl
              intro g hg
              exact hinner g hg
        _ = ∑ g ∈ S, ((X : ℝ) * (g : ℝ)⁻¹) * (H * H) := by
              apply Finset.sum_congr rfl
              intro g hg
              ring
        _ = (∑ g ∈ S, (X : ℝ) * (g : ℝ)⁻¹) * (H * H) := by
              rw [← Finset.sum_mul]
        _ = ((X : ℝ) * ∑ g ∈ S, (g : ℝ)⁻¹) * (H * H) := by
              rw [← Finset.mul_sum]
        _ = (X : ℝ) * H ^ 3 := by
              rw [pow_succ, pow_two]
              ring
        _ = (X : ℝ) * liuHarmonic X ^ 3 := by
              simp [S, H, liuHarmonic]

/-- Weighted divisor-square energy in the form used in Chen's Lemma 3.
The elementary four-harmonic proof keeps the endpoint `X = 0` harmless. -/
theorem divisorSquareWeightedPrefix_le_fourth_harmonic (X : ℕ) :
    (∑ t ∈ Finset.Icc 1 X,
      ((t.divisors.card : ℝ) ^ 2) * (t : ℝ)⁻¹) ≤ liuHarmonic X ^ 4 := by
  calc
    (∑ t ∈ Finset.Icc 1 X,
        ((t.divisors.card : ℝ) ^ 2) * (t : ℝ)⁻¹) ≤
      ∑ t ∈ Finset.Icc 1 X,
        (∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X,
          ∑ v ∈ Finset.Icc 1 X,
            if g * u * v ∣ t then (1 : ℝ) else 0) * (t : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_right
      · exact divisorSquarePrefix_term_le_tripleCount
          (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
      · positivity
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X,
        ∑ v ∈ Finset.Icc 1 X, ∑ t ∈ Finset.Icc 1 X,
          if g * u * v ∣ t then (t : ℝ)⁻¹ else 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
      simp only [ite_mul, one_mul, zero_mul]
    _ ≤ ∑ g ∈ Finset.Icc 1 X, ∑ u ∈ Finset.Icc 1 X,
        ∑ v ∈ Finset.Icc 1 X,
          ((g * u * v : ℕ) : ℝ)⁻¹ * liuHarmonic X := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have hgpos : 0 < g := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1
      have hupos : 0 < u := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hu).1
      have hvpos : 0 < v := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hv).1
      have hepos : 0 < g * u * v := Nat.mul_pos (Nat.mul_pos hgpos hupos) hvpos
      rw [← Finset.sum_filter]
      rw [sum_multiples_Icc_reindex (R := ℝ)
        (F := fun t => ((t : ℝ)⁻¹)) (k := g * u * v) (y := X) hepos]
      calc
        (∑ r ∈ Finset.Icc 1 (X / (g * u * v)),
            (((g * u * v) * r : ℕ) : ℝ)⁻¹) =
          ∑ r ∈ Finset.Icc 1 (X / (g * u * v)),
            ((g * u * v : ℕ) : ℝ)⁻¹ * (r : ℝ)⁻¹ := by
              apply Finset.sum_congr rfl
              intro r hr
              simp only [Nat.cast_mul, mul_inv_rev]
              ring
        _ ≤ ∑ r ∈ Finset.Icc 1 X,
            ((g * u * v : ℕ) : ℝ)⁻¹ * (r : ℝ)⁻¹ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro r hr
                exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
                  (Finset.mem_Icc.mp hr).2.trans
                    (Nat.div_le_self X (g * u * v))⟩
              · intro r hrX hrsmall
                positivity
        _ = ((g * u * v : ℕ) : ℝ)⁻¹ * liuHarmonic X := by
              rw [← Finset.mul_sum]
              rfl
    _ = liuHarmonic X ^ 4 := by
      let S : Finset ℕ := Finset.Icc 1 X
      let H : ℝ := liuHarmonic X
      change (∑ g ∈ S, ∑ u ∈ S, ∑ v ∈ S,
        ((g * u * v : ℕ) : ℝ)⁻¹ * H) = H ^ 4
      simp only [Nat.cast_mul, mul_inv_rev]
      have hS : (∑ n ∈ S, (n : ℝ)⁻¹) = H := by rfl
      simp_rw [mul_assoc]
      calc
        (∑ g ∈ S, ∑ u ∈ S, ∑ v ∈ S,
            (v : ℝ)⁻¹ * ((u : ℝ)⁻¹ * ((g : ℝ)⁻¹ * H))) =
          ∑ g ∈ S, ∑ u ∈ S,
            H * ((u : ℝ)⁻¹ * ((g : ℝ)⁻¹ * H)) := by
              apply Finset.sum_congr rfl
              intro g hg
              apply Finset.sum_congr rfl
              intro u hu
              rw [← Finset.sum_mul, hS]
        _ = ∑ g ∈ S, H * (H * ((g : ℝ)⁻¹ * H)) := by
              apply Finset.sum_congr rfl
              intro g hg
              calc
                (∑ u ∈ S, H * ((u : ℝ)⁻¹ * ((g : ℝ)⁻¹ * H))) =
                    H * (∑ u ∈ S, (u : ℝ)⁻¹ * ((g : ℝ)⁻¹ * H)) := by
                      rw [Finset.mul_sum]
                _ = H * (H * ((g : ℝ)⁻¹ * H)) := by
                      rw [← Finset.sum_mul, hS]
        _ = H * (H * (H * H)) := by
              calc
                (∑ g ∈ S, H * (H * ((g : ℝ)⁻¹ * H))) =
                    ∑ g ∈ S, H * H * ((g : ℝ)⁻¹ * H) := by
                      apply Finset.sum_congr rfl
                      intro g hg
                      ring
                _ = H * H * (∑ g ∈ S, (g : ℝ)⁻¹ * H) := by
                      rw [Finset.mul_sum]
                _ = H * H * (H * H) := by rw [← Finset.sum_mul, hS]
                _ = H * (H * (H * H)) := by ring
        _ = H ^ 4 := by ring

theorem divisorSquareMomentBound_27 :
    DivisorSquareMomentBound 27 := by
  intro X
  have hH : liuHarmonic X ≤ 3 * Real.log (X + 1 : ℕ) :=
    liuHarmonic_le_three_log_add_one X
  have hH0 : 0 ≤ liuHarmonic X := by
    unfold liuHarmonic
    positivity
  have hpow : liuHarmonic X ^ 3 ≤ (3 * Real.log (X + 1 : ℕ)) ^ 3 :=
    pow_le_pow_left₀ hH0 hH 3
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  calc
    divisorSquarePrefix X ≤ (X : ℝ) * liuHarmonic X ^ 3 :=
      divisorSquarePrefix_le_cube_harmonic X
    _ ≤ (X : ℝ) * (3 * Real.log (X + 1 : ℕ)) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow hX0
    _ = 27 * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3 := by ring

theorem vaughanActualTensorCoeffEnergy_canonical_le_BVScale_unconditional
    (b : ℕ → ℂ) (y N u v k l : ℕ) (B : ℝ)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B) :
    vaughanActualTensorCoeffEnergy b y
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalDyadicBlock N v l) ≤
      27 * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 5 := by
  simpa using
    (vaughanActualTensorCoeffEnergy_canonical_le_BVScale
      b y N u v k l B 27 hB divisorSquareMomentBound_27 (by positivity))

theorem vaughanBilinearTensorEnergy_canonical_le_BVScale_unconditional
    (b : ℕ → ℂ) (y N u v k l : ℕ) (B : ℝ)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B) :
    vaughanBilinearTensorEnergy vaughanMangoldtCoeff b y
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalDyadicBlock N v l) ≤
      27 * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 5 := by
  simpa using
    (vaughanBilinearTensorEnergy_canonical_le_BVScale
      b y N u v k l B 27 hB divisorSquareMomentBound_27 (by positivity))

end

end AnalyticNumberTheory.LargeSieve
