import WSrcSingleSevenWindows

noncomputable section
namespace WuSource.SrcSingle
open Wu2008DoubleSieve Real Finset
open scoped Classical BigOperators

theorem high_cutoff_antitone {N p : ℕ} {δ a b : ℝ}
    (hr : 1 ≤ psiRatio N δ p) (ha : 0 < a) (hab : a ≤ b) :
    wuLocalCutoff N δ p b ≤ wuLocalCutoff N δ p a :=
  rpow_le_rpow_of_exponent_le hr (one_div_le_one_div_of_le ha hab)

theorem high_bad_prime_zero {N p : ℕ} {a u : ℝ}
    (hp : p.Prime) (hu : u ≤ (p : ℝ)) :
    fourthRowMotherBadPrime N p a u = 0 := by
  unfold fourthRowMotherBadPrime
  apply sum_eq_zero
  intro q hq
  obtain ⟨hq, hd⟩ := mem_filter.mp hq
  have hprime := (mem_primeWindow.mp hq).1
  have hlt : q < p := by exact_mod_cast (mem_primeWindow.mp hq).2.2.2.trans_le hu
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact False.elim (hprime.ne_one h)
  · exact False.elim (Nat.ne_of_lt hlt h)

theorem coupled_high_point {N p : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ psiPrimes (j.castAdd 4) N) :
    5 * (sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) ≤
      secondFunctionalMotherLocal N p N
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa1)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa2)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa3)
        (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s) := by
  have hgeom := (ActualNineFeedback.coupledRow_geometry j.succ).1
  have hrow : Wu04RemainingCore.row j = ActualNineFeedback.coupledRow j.succ := rfl
  rw [← hrow] at hgeom
  have hmother := hgeom.mother
  have hs : 0 < (Wu04RemainingCore.row j).s := by linarith [hgeom.two_lt_s]
  have h3 := hmother.s_le_kappa3
  have h2 := hmother.kappa3_lt_kappa2.le
  have h1 := hmother.kappa2_lt_kappa1.le
  have hS := hmother.kappa1_le_S
  have hr := (seven_ratio_geometry (j.castAdd 4) hN hd hh hp).1.le
  have hcuts := seven_cutoff_geometry (j.castAdd 4) hN hd hh hp
  rw [(seven_source_rows.1 j).1, (seven_source_rows.1 j).2] at hcuts
  have hab := high_cutoff_antitone hr (hs.trans_le (h3.trans (h2.trans h1))) hS
  have hbc := high_cutoff_antitone hr (hs.trans_le (h3.trans h2)) h1
  have hce := high_cutoff_antitone hr (hs.trans_le h3) h2
  have hef := high_cutoff_antitone hr hs h3
  have hm := secondFunctionalMother_masked N p hab hbc hce hef
  have hrestore := secondFunctionalMother_restore_windows N p
    (wuLocalCutoff N δ p (Wu04RemainingCore.row j).S)
    (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa1)
    (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa2)
    (wuLocalCutoff N δ p (Wu04RemainingCore.row j).kappa3)
    (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s)
  have hprime := (mem_primeWindow.mp hp).1
  have hf : wuLocalCutoff N δ p (Wu04RemainingCore.row j).s ≤ (p : ℝ) :=
    hcuts.2.2.1.trans hcuts.2.2.2.le
  rw [high_bad_prime_zero hprime hf,
    high_bad_prime_zero hprime (hce.trans (hef.trans hf)),
    high_bad_prime_zero hprime (hef.trans hf), add_zero, add_zero, add_zero] at hrestore
  have hc : (sourceSieveCount N p (p * N) ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) ≤
      (sourceSieveCount N p (p * N) (wuLocalCutoff N δ p (Wu04RemainingCore.row j).s) : ℝ) := by
    exact_mod_cast sourceSieveCount_antitone N p (p * N) hcuts.2.2.1
  rw [SingleUpperCounts.source_count hprime hcuts.2.2.2.le] at hc
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans (hm.trans hrestore)

theorem coupled_high_actual_finite {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    5 * psiCount (j.castAdd 4) N ≤
      secondFunctionalMotherRHS (Wu04RemainingCore.row j) N δ
        (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) := by
  rw [← secondFunctionalMother_weighted_identity]
  change _ ≤ ∑ p ∈ Finset.image (fun t : Fin 1 → ℕ => ∏ i, t i)
    (Fintype.piFinset (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N)),
      (convolutionCoeff (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) p : ℝ) * _
  rw [SingleUpperCounts.single_weighted_sum]
  unfold psiCount
  rw [mul_sum]
  exact sum_le_sum (fun p hp => coupled_high_point j hN hd hh hp)

#check @coupled_high_actual_finite
#print axioms coupled_high_point
#print axioms coupled_high_actual_finite
end WuSource.SrcSingle
