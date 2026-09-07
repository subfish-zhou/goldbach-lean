import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainJointNormalization

/-!
# A logarithmic joint gcd mean

The angular sum is split into its two triangles. The ordinary gcd mean
on the shorter side and the existing reciprocal gcd mean on the longer
side replace a dyadic-shell argument.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem joint_triangle_mean {A B S : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hS : 0 < S) :
    (∑ v ∈ Ioc 0 S, ∑ u ∈ Ioc 0 S,
      if u ≤ v then (u.gcd A : ℝ) * v.gcd B / (v : ℝ) ^ 2 else 0) ≤
      (fouvryTau 2 A : ℝ) * fouvryTau 2 B * (1 + Real.log S) := by
  have hrow (v : ℕ) (hv : v ∈ Ioc 0 S) :
      (∑ u ∈ Ioc 0 S,
        if u ≤ v then (u.gcd A : ℝ) * v.gcd B / (v : ℝ) ^ 2 else 0) ≤
      (fouvryTau 2 A : ℝ) * ((v.gcd B : ℝ) / v) := by
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    have hfilter : (Ioc 0 S).filter (fun u => u ≤ v) = Ioc 0 v := by
      ext u
      simp only [mem_filter, mem_Ioc]
      have := (mem_Ioc.mp hv).2
      omega
    rw [← sum_filter, hfilter, ← sum_div, ← sum_mul]
    have hmean : (∑ u ∈ Ioc 0 v, (u.gcd A : ℝ)) ≤
        (v : ℝ) * fouvryTau 2 A := by
      exact_mod_cast (show (∑ u ∈ Ioc 0 v, u.gcd A) ≤ v * fouvryTau 2 A by
        simpa only [Nat.gcd_comm, fouvryTau_two] using sum_gcd_le hA.ne' v)
    calc
      _ ≤ ((v : ℝ) * fouvryTau 2 A) * v.gcd B / (v : ℝ) ^ 2 := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ ∑ v ∈ Ioc 0 S, (fouvryTau 2 A : ℝ) * ((v.gcd B : ℝ) / v) :=
      sum_le_sum hrow
    _ = (fouvryTau 2 A : ℝ) * ∑ v ∈ Ioc 0 S, (v.gcd B : ℝ) / v :=
      (mul_sum _ _ _).symm
    _ ≤ (fouvryTau 2 A : ℝ) *
        ((fouvryTau 2 B : ℝ) * (1 + Real.log S)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.floor_natCast, Nat.gcd_comm] using
        sum_gcd_div_le_tau_log (by exact_mod_cast hS : (1 : ℝ) ≤ S)
          (Ioc 0 S) (by simp) hB
    _ = _ := by ring

/-- The angular weight has only one logarithm, with no coprimality
condition on the enlarged summation domain. -/
theorem mainJoint_angular_mean {A B S : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hS : 0 < S) :
    (∑ u ∈ Ioc 0 S, ∑ v ∈ Ioc 0 S,
      (u.gcd A : ℝ) * v.gcd B / ((max u v : ℕ) : ℝ) ^ 2) ≤
      2 * (fouvryTau 2 A : ℝ) * fouvryTau 2 B * (1 + Real.log S) := by
  calc
    _ ≤ ∑ u ∈ Ioc 0 S, ∑ v ∈ Ioc 0 S,
        ((if u ≤ v then (u.gcd A : ℝ) * v.gcd B / (v : ℝ) ^ 2 else 0) +
         (if v ≤ u then (v.gcd B : ℝ) * u.gcd A / (u : ℝ) ^ 2 else 0)) := by
      apply sum_le_sum
      intro u _
      apply sum_le_sum
      intro v _
      rcases le_total u v with huv | hvu
      · rw [max_eq_right huv, if_pos huv]
        exact le_add_of_nonneg_right (by split_ifs <;> positivity)
      · rw [max_eq_left hvu, if_pos hvu, mul_comm (v.gcd B : ℝ)]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
    _ = (∑ v ∈ Ioc 0 S, ∑ u ∈ Ioc 0 S,
        if u ≤ v then (u.gcd A : ℝ) * v.gcd B / (v : ℝ) ^ 2 else 0) +
        (∑ u ∈ Ioc 0 S, ∑ v ∈ Ioc 0 S,
        if v ≤ u then (v.gcd B : ℝ) * u.gcd A / (u : ℝ) ^ 2 else 0) := by
      simp only [sum_add_distrib]
      rw [sum_comm]
    _ ≤ (fouvryTau 2 A : ℝ) * fouvryTau 2 B * (1 + Real.log S) +
        (fouvryTau 2 B : ℝ) * fouvryTau 2 A * (1 + Real.log S) :=
      add_le_add (joint_triangle_mean hA hB hS) (joint_triangle_mean hB hA hS)
    _ = _ := by ring

/-- A genuine rectangular joint mean on any finite positive support with
nonzero numerator. The envelope is discharged uniformly in the next module. -/
theorem mainJoint_mean_envelope {a U V : ℤ} (ha : a ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    {S : ℕ} (hS : 0 < S) {T : ℝ} (hT : 0 ≤ T)
    (henv : ∀ n : ℕ, 0 < n → n ≤ a.natAbs * (U.natAbs + V.natAbs) * S →
      (fouvryTau 2 n : ℝ) ≤ T)
    (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, (0 < p.1 ∧ p.1 ≤ S) ∧ (0 < p.2 ∧ p.2 ≤ S) ∧
      mainJointNumerator a U V p.1 p.2 ≠ 0) :
    (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
      fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs) ≤
      2 * (S : ℝ) ^ 2 * (fouvryTau 2 (a * U).natAbs : ℝ) *
        fouvryTau 2 (a * V).natAbs * T ^ 2 * (1 + Real.log S) := by
  let C := ((Ioc 0 S) ×ˢ (Ioc 0 S)).filter
    (fun p : ℕ × ℕ => p.1.Coprime p.2 ∧ mainJointNumerator a U V p.1 p.2 ≠ 0)
  let Q := C.sigma (fun p => Ioc 0 (S / max p.1 p.2))
  let F := fun z : (p : ℕ × ℕ) × ℕ =>
    ((((z.2 * z.1.1) * (z.2 * z.1.2)).gcd
      (mainJointNumerator a U V (z.2 * z.1.1) (z.2 * z.1.2)).natAbs : ℝ) *
      fouvryTau 2 (mainJointNumerator a U V (z.2 * z.1.1) (z.2 * z.1.2)).natAbs)
  let e := fun p : ℕ × ℕ =>
    (⟨(p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2), p.1.gcd p.2⟩ :
      (p : ℕ × ℕ) × ℕ)
  have hrecon (p : ℕ × ℕ) :
      (e p).2 * (e p).1.1 = p.1 ∧ (e p).2 * (e p).1.2 = p.2 :=
    ⟨Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)⟩
  have hinj : Set.InjOn e (↑P : Set (ℕ × ℕ)) := by
    intro p _ q _ he
    apply Prod.ext
    · calc
        p.1 = (e p).2 * (e p).1.1 := (hrecon p).1.symm
        _ = (e q).2 * (e q).1.1 := by rw [he]
        _ = q.1 := (hrecon q).1
    · calc
        p.2 = (e p).2 * (e p).1.2 := (hrecon p).2.symm
        _ = (e q).2 * (e q).1.2 := by rw [he]
        _ = q.2 := (hrecon q).2
  have hmem (p : ℕ × ℕ) (hp : p ∈ P) : e p ∈ Q := by
    obtain ⟨hs, ht, hn⟩ := hP p hp
    have hg : 0 < p.1.gcd p.2 := Nat.gcd_pos_of_pos_left _ hs.1
    have hu : 0 < p.1 / p.1.gcd p.2 :=
      Nat.div_pos (Nat.le_of_dvd hs.1 (Nat.gcd_dvd_left _ _)) hg
    have hv : 0 < p.2 / p.1.gcd p.2 :=
      Nat.div_pos (Nat.le_of_dvd ht.1 (Nat.gcd_dvd_right _ _)) hg
    have huS := (Nat.div_le_self p.1 (p.1.gcd p.2)).trans hs.2
    have hvS := (Nat.div_le_self p.2 (p.1.gcd p.2)).trans ht.2
    have hD : mainJointNumerator a U V (e p).1.1 (e p).1.2 ≠ 0 := by
      intro hz
      have hh := mainJointNumerator_scale a U V (e p).2 (e p).1.1 (e p).1.2
      rw [(hrecon p).1, (hrecon p).2, hz, mul_zero] at hh
      exact hn hh
    have hbound : (e p).2 * max (e p).1.1 (e p).1.2 ≤ S := by
      rcases le_total (e p).1.1 (e p).1.2 with h | h
      · rw [max_eq_right h, (hrecon p).2]
        exact ht.2
      · rw [max_eq_left h, (hrecon p).1]
        exact hs.2
    apply mem_sigma.mpr
    refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨hu, huS⟩,
      mem_Ioc.mpr ⟨hv, hvS⟩⟩,
        Nat.gcd_div_gcd_div_gcd_of_pos_left hs.1, hD⟩, ?_⟩
    exact mem_Ioc.mpr ⟨hg, (Nat.le_div_iff_mul_le (lt_of_lt_of_le hu (le_max_left _ _))).mpr
      (by simpa only [Nat.mul_comm] using hbound)⟩
  have hfirst :
      (∑ p ∈ P, ((p.1 * p.2).gcd (mainJointNumerator a U V p.1 p.2).natAbs : ℝ) *
        fouvryTau 2 (mainJointNumerator a U V p.1 p.2).natAbs) ≤ ∑ z ∈ Q, F z := by
    calc
      _ = ∑ p ∈ P, F (e p) := sum_congr rfl (fun p _ => by
        dsimp only [F]
        rw [(hrecon p).1, (hrecon p).2])
      _ = ∑ z ∈ P.image e, F z := (sum_image hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (by intro z hz; obtain ⟨p, hp, rfl⟩ := mem_image.mp hz; exact hmem p hp)
        (fun z _ _ => by dsimp only [F]; positivity)
  have hrad (p : ℕ × ℕ) (hp : p ∈ C) :
      (∑ g ∈ Ioc 0 (S / max p.1 p.2), F ⟨p, g⟩) ≤
        (S : ℝ) ^ 2 * T ^ 2 *
          ((p.1.gcd (a * U).natAbs : ℝ) * p.2.gcd (a * V).natAbs /
            ((max p.1 p.2 : ℕ) : ℝ) ^ 2) := by
    obtain ⟨hpbox, hcop, hn⟩ := mem_filter.mp hp
    obtain ⟨hs, ht⟩ := mem_product.mp hpbox
    have hmax : 0 < max p.1 p.2 := lt_of_lt_of_le (mem_Ioc.mp hs).1 (le_max_left _ _)
    have hscaled (g : ℕ) (hg : g ∈ Ioc 0 (S / max p.1 p.2)) :
        g * p.1 ≤ S ∧ g * p.2 ≤ S := by
      have hm : g * max p.1 p.2 ≤ S :=
        (Nat.le_div_iff_mul_le hmax).mp (mem_Ioc.mp hg).2
      exact ⟨(Nat.mul_le_mul_left g (le_max_left _ _)).trans hm,
        (Nat.mul_le_mul_left g (le_max_right _ _)).trans hm⟩
    have hh := mainJoint_radial_mean a U V hcop hn
      (mainJointNumerator_natAbs_le a U V (mem_Ioc.mp hs).2 (mem_Ioc.mp ht).2)
      (fun g hg => mainJointNumerator_natAbs_le a U V (hscaled g hg).1 (hscaled g hg).2)
      hT henv
    change (∑ g ∈ Ioc 0 (S / max p.1 p.2), F ⟨p, g⟩) ≤ _ at hh
    refine hh.trans ?_
    calc
      _ ≤ ((S : ℝ) / max p.1 p.2) ^ 2 * T ^ 2 *
          (p.1.gcd (a * U).natAbs : ℝ) * p.2.gcd (a * V).natAbs := by
        gcongr
        exact Nat.cast_div_le
      _ = _ := by ring
  calc
    _ ≤ ∑ z ∈ Q, F z := hfirst
    _ = ∑ p ∈ C, ∑ g ∈ Ioc 0 (S / max p.1 p.2), F ⟨p, g⟩ := sum_sigma _ _ _
    _ ≤ ∑ p ∈ C, (S : ℝ) ^ 2 * T ^ 2 *
        ((p.1.gcd (a * U).natAbs : ℝ) * p.2.gcd (a * V).natAbs /
          ((max p.1 p.2 : ℕ) : ℝ) ^ 2) := sum_le_sum hrad
    _ ≤ ∑ p ∈ (Ioc 0 S) ×ˢ (Ioc 0 S), (S : ℝ) ^ 2 * T ^ 2 *
        ((p.1.gcd (a * U).natAbs : ℝ) * p.2.gcd (a * V).natAbs /
          ((max p.1 p.2 : ℕ) : ℝ) ^ 2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (S : ℝ) ^ 2 * T ^ 2 * ∑ u ∈ Ioc 0 S, ∑ v ∈ Ioc 0 S,
        (u.gcd (a * U).natAbs : ℝ) * v.gcd (a * V).natAbs /
          ((max u v : ℕ) : ℝ) ^ 2 := by rw [sum_product]; simp only [mul_sum]
    _ ≤ (S : ℝ) ^ 2 * T ^ 2 *
        (2 * (fouvryTau 2 (a * U).natAbs : ℝ) * fouvryTau 2 (a * V).natAbs *
          (1 + Real.log S)) :=
      mul_le_mul_of_nonneg_left
        (mainJoint_angular_mean
          (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (mul_ne_zero ha hU)))
          (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (mul_ne_zero ha hV))) hS)
        (by positivity)
    _ = _ := by ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
