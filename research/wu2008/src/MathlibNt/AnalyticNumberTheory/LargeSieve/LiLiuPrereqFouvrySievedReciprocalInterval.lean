import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryProgressionWeil

/-!
# Reciprocal sums on genuine residue-class intervals

The interval is a natural-number interval, not an arbitrary mask on a
progression. Choosing its first admissible point retains multiplicities and
gives a parameter interval whose length is bounded by the original span
divided by the step.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def reciprocalResidueInterval (q : ℕ) [NeZero q] (d : ℤ) (b v L U : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc L U, if k % v = b % v then reciprocalPhase q d k else 0

theorem reciprocalProgression_nat_Icc (q : ℕ) [NeZero q] (d : ℤ) (b v N : ℕ) :
    (∑ t ∈ Finset.Icc 0 N, reciprocalPhase q d ((b + v * t : ℕ) : ZMod q)) =
      reciprocalProgression q d b v (-1) N := by
  unfold reciprocalProgression
  apply Finset.sum_bij (fun (t : ℕ) _ ↦ (t : ℤ))
  · intro t ht
    simp only [Finset.mem_Icc] at ht
    simp only [Finset.mem_Ioc]
    omega
  · intro t _ u _ he
    exact_mod_cast he
  · intro t ht
    simp only [Finset.mem_Ioc] at ht
    refine ⟨t.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro t _
    simp only [Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- Nonempty residue sections are actual progressions, with a length certificate. -/
theorem reciprocalResidueInterval_eq_progression
    (q : ℕ) [NeZero q] (d : ℤ) (b v L U : ℕ) (hv : 0 < v)
    (hne : ((Finset.Icc L U).filter (fun k ↦ k % v = b % v)).Nonempty) :
    ∃ c N : ℕ, L ≤ c ∧ c ≤ U ∧ c % v = b % v ∧ N * v ≤ U - L ∧
      reciprocalResidueInterval q d b v L U =
        reciprocalProgression q d c v (-1) N := by
  let S := (Finset.Icc L U).filter (fun k ↦ k % v = b % v)
  let c := S.min' hne
  have hc : c ∈ S := Finset.min'_mem S hne
  have hc' := Finset.mem_filter.mp hc
  have hcLU := Finset.mem_Icc.mp hc'.1
  let N := (U - c) / v
  have hNv : N * v ≤ U - c := Nat.div_mul_le_self _ _
  refine ⟨c, N, hcLU.1, hcLU.2, hc'.2, hNv.trans (Nat.sub_le_sub_left hcLU.1 U), ?_⟩
  rw [← reciprocalProgression_nat_Icc]
  unfold reciprocalResidueInterval
  rw [← Finset.sum_filter]
  change (∑ k ∈ S, reciprocalPhase q d k) = _
  have hk (k : ℕ) (hkS : k ∈ S) : c + v * ((k - c) / v) = k := by
    have hck : c ≤ k := Finset.min'_le S k hkS
    have hmod : Nat.ModEq v c k := hc'.2.trans (Finset.mem_filter.mp hkS).2.symm
    have hdvd : v ∣ k - c := (Nat.modEq_iff_dvd' hck).mp hmod
    rw [Nat.mul_div_cancel' hdvd]
    omega
  apply Finset.sum_bij (fun k _ ↦ (k - c) / v)
  · intro k hkS
    have hkU := (Finset.mem_Icc.mp (Finset.mem_filter.mp hkS).1).2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right (Nat.sub_le_sub_right hkU c)⟩
  · intro k hkS l hlS he
    have hk' := hk k hkS
    have hl' := hk l hlS
    rw [he] at hk'
    exact hk'.symm.trans hl'
  · intro t ht
    have htN := (Finset.mem_Icc.mp ht).2
    have htv : v * t ≤ U - c := by
      calc
        v * t ≤ v * N := Nat.mul_le_mul_left _ htN
        _ ≤ U - c := by simpa [Nat.mul_comm] using hNv
    refine ⟨c + v * t, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        omega
      · simpa using hc'.2
    · simp [hv]
  · intro k hkS
    rw [hk k hkS]

/-- A uniform interval bound with the original span divided by the step.
The constant absorbs at most a factor two from the first point of the AP. -/
theorem reciprocalResidueInterval_fouvry {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_ : NeZero q) (d : ℤ) (b v L U : ℕ),
      0 < v → v.Coprime q →
      ‖reciprocalResidueInterval q d b v L U‖ ≤
        C * (1 + ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q)) *
          Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalProgression_fouvry hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro q hq d b v L U hv hvq
  have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  by_cases hne : ((Finset.Icc L U).filter (fun k ↦ k % v = b % v)).Nonempty
  · obtain ⟨c, N, _, _, _, hNv, he⟩ :=
      reciprocalResidueInterval_eq_progression q d b v L U hv hne
    rw [he]
    have hb := hbound q hq d c v (-1) N hvq (by omega)
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hNvR : (N : ℝ) * v ≤ (U - L + 1 : ℕ) := by
      exact_mod_cast (hNv.trans (Nat.le_succ _))
    have hfrac : (1 + ((N : ℝ) - (-1 : ℤ)) / q) ≤
        2 * (1 + ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q)) := by
      norm_num
      have hNq : (N : ℝ) / q ≤ ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q) := by
        apply (div_le_div_iff₀ hqr (mul_pos hvr hqr)).mpr
        nlinarith
      have hi : (1 : ℝ) / q ≤ 1 := (div_le_one hqr).mpr hqone
      rw [add_div]
      have hn : 0 ≤ ((U - L + 1 : ℕ) : ℝ) / ((v : ℝ) * q) := by positivity
      push_cast at hNq hn
      linarith
    calc
      _ ≤ C * (1 + ((N : ℝ) - (-1 : ℤ)) / q) *
          Real.sqrt (q.gcd d.natAbs) * (q : ℝ) ^ (1 / 2 + ε : ℝ) := hb
      _ ≤ _ := by
        have hs : 0 ≤ Real.sqrt (q.gcd d.natAbs) := Real.sqrt_nonneg _
        have hp : 0 ≤ (q : ℝ) ^ (1 / 2 + ε : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hC.le) hs) hp]
  · have hz : reciprocalResidueInterval q d b v L U = 0 := by
      unfold reciprocalResidueInterval
      rw [← Finset.sum_filter, Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    rw [hz, norm_zero]
    positivity

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
