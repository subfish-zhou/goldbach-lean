import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdMean
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighDeltaWeights

/-!
# Primitive coordinates for the joint main-term gcd

Only the reduced coordinates are coprime. The original two summation
variables are unrestricted positive integers, and all coefficients are signed.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def mainJointNumerator (a U V : ℤ) (s t : ℕ) : ℤ :=
  a * (U * t - V * s)

theorem mainJointNumerator_scale (a U V : ℤ) (g u v : ℕ) :
    mainJointNumerator a U V (g * u) (g * v) =
      (g : ℤ) * mainJointNumerator a U V u v := by
  simp only [mainJointNumerator, Nat.cast_mul]
  ring

theorem mainJointNumerator_natAbs_le (a U V : ℤ) {s t S : ℕ}
    (hs : s ≤ S) (ht : t ≤ S) :
    (mainJointNumerator a U V s t).natAbs ≤
      a.natAbs * (U.natAbs + V.natAbs) * S := by
  rw [mainJointNumerator, Int.natAbs_mul]
  calc
    _ ≤ a.natAbs * ((U * (t : ℤ)).natAbs + (V * (s : ℤ)).natAbs) :=
      Nat.mul_le_mul_left _ (Int.natAbs_sub_le _ _)
    _ = a.natAbs * (U.natAbs * t + V.natAbs * s) := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ a.natAbs * (U.natAbs * S + V.natAbs * S) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ ht)
        (Nat.mul_le_mul_left _ hs))
    _ = _ := by ring

theorem mainJoint_gcd_primitive_left (a U V : ℤ) {u v : ℕ}
    (huv : u.Coprime v) :
    u.gcd (mainJointNumerator a U V u v).natAbs = u.gcd (a * U).natAbs := by
  have h := Int.gcd_sub_mul_right_right (u : ℤ) (a * U * v) (a * V)
  have he : a * U * (v : ℤ) - a * V * u = mainJointNumerator a U V u v := by
    unfold mainJointNumerator
    ring
  rw [he] at h
  simp only [Int.gcd, Int.natAbs_natCast, Int.natAbs_mul] at h
  rw [h]
  simpa only [Int.natAbs_mul] using huv.symm.gcd_mul_right_cancel_right (a * U).natAbs

theorem mainJoint_gcd_primitive_right (a U V : ℤ) {u v : ℕ}
    (huv : u.Coprime v) :
    v.gcd (mainJointNumerator a U V u v).natAbs = v.gcd (a * V).natAbs := by
  have he : mainJointNumerator a V U v u = -mainJointNumerator a U V u v := by
    unfold mainJointNumerator
    ring
  have h := mainJoint_gcd_primitive_left a V U huv.symm
  simpa only [he, Int.natAbs_neg] using h

/-- The common factor is paid by a one-dimensional gcd mean, rather than
discarded at its worst possible size. -/
theorem mainJoint_gcd_normalized (a U V : ℤ) {g u v : ℕ}
    (huv : u.Coprime v) (hD : mainJointNumerator a U V u v ≠ 0) :
    ((g * u) * (g * v)).gcd
        (mainJointNumerator a U V (g * u) (g * v)).natAbs ≤
      g * g.gcd (mainJointNumerator a U V u v).natAbs *
        u.gcd (a * U).natAbs * v.gcd (a * V).natAbs := by
  have hpos := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hD)
  rw [mainJointNumerator_scale, Int.natAbs_mul, Int.natAbs_natCast,
    show g * u * (g * v) = g * (g * (u * v)) by ring, Nat.gcd_mul_left]
  calc
    _ ≤ g * ((u * v).gcd (mainJointNumerator a U V u v).natAbs *
        g.gcd (mainJointNumerator a U V u v).natAbs) :=
      Nat.mul_le_mul_left _ (gcd_mul_le_gcd_mul_gcd hpos g (u * v))
    _ ≤ g * ((v.gcd (mainJointNumerator a U V u v).natAbs *
        u.gcd (mainJointNumerator a U V u v).natAbs) *
        g.gcd (mainJointNumerator a U V u v).natAbs) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
        (gcd_mul_le_gcd_mul_gcd hpos u v))
    _ = _ := by
      rw [mainJoint_gcd_primitive_left a U V huv, mainJoint_gcd_primitive_right a U V huv]
      ring

/-- A complete radial mean, with the divisor envelope explicit. -/
theorem mainJoint_radial_mean (a U V : ℤ) {u v G L : ℕ} {T : ℝ}
    (huv : u.Coprime v) (hD : mainJointNumerator a U V u v ≠ 0)
    (hDle : (mainJointNumerator a U V u v).natAbs ≤ L)
    (hscale : ∀ g ∈ Ioc 0 G, (mainJointNumerator a U V (g * u) (g * v)).natAbs ≤ L)
    (hT : 0 ≤ T)
    (henv : ∀ n : ℕ, 0 < n → n ≤ L → (fouvryTau 2 n : ℝ) ≤ T) :
    (∑ g ∈ Ioc 0 G,
      (((g * u) * (g * v)).gcd
        (mainJointNumerator a U V (g * u) (g * v)).natAbs : ℝ) *
      fouvryTau 2 (mainJointNumerator a U V (g * u) (g * v)).natAbs) ≤
      (G : ℝ) ^ 2 * T ^ 2 * (u.gcd (a * U).natAbs : ℝ) *
        v.gcd (a * V).natAbs := by
  let D := (mainJointNumerator a U V u v).natAbs
  have hDpos : 0 < D := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hD)
  have hsum : (∑ g ∈ Ioc 0 G, (g.gcd D : ℝ)) ≤ (G : ℝ) * T := by
    calc
      _ ≤ (G : ℝ) * fouvryTau 2 D := by
        exact_mod_cast (show (∑ g ∈ Ioc 0 G, g.gcd D) ≤ G * fouvryTau 2 D by
          simpa only [Nat.gcd_comm, fouvryTau_two] using sum_gcd_le hDpos.ne' G)
      _ ≤ _ := mul_le_mul_of_nonneg_left (henv D hDpos hDle) (by positivity)
  calc
    _ ≤ ∑ g ∈ Ioc 0 G, (G : ℝ) * (g.gcd D : ℝ) *
        (u.gcd (a * U).natAbs : ℝ) * v.gcd (a * V).natAbs * T := by
      apply sum_le_sum
      intro g hg
      have hgG : (g : ℝ) ≤ G := by exact_mod_cast (mem_Ioc.mp hg).2
      have hnpos : 0 < (mainJointNumerator a U V (g * u) (g * v)).natAbs := by
        rw [mainJointNumerator_scale, Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.mul_pos (mem_Ioc.mp hg).1 hDpos
      have hb :
          (((g * u) * (g * v)).gcd
            (mainJointNumerator a U V (g * u) (g * v)).natAbs : ℝ) ≤
          (g : ℝ) * (g.gcd D : ℝ) * (u.gcd (a * U).natAbs : ℝ) *
            v.gcd (a * V).natAbs := by
        exact_mod_cast mainJoint_gcd_normalized a U V huv hD
      exact mul_le_mul
        (hb.trans (by gcongr)) (henv _ hnpos (hscale g hg)) (by positivity) (by positivity)
    _ = ((G : ℝ) * (u.gcd (a * U).natAbs : ℝ) *
        v.gcd (a * V).natAbs * T) * ∑ g ∈ Ioc 0 G, (g.gcd D : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro g _
      ring
    _ ≤ ((G : ℝ) * (u.gcd (a * U).natAbs : ℝ) *
        v.gcd (a * V).natAbs * T) * ((G : ℝ) * T) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
