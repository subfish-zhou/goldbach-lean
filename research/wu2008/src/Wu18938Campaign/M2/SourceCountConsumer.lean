import Wu18938Campaign.M2.TerminalDebits
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherOriginalWindows
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalParameters
import MathlibNt.Wu2008DoubleSieve.SingleUpperCounts
import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerGeometry

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve Real
open scoped Classical

noncomputable def terminalSignedLocal (N d : ℕ) (a b c e f : ℝ) : ℝ :=
  secondFunctionalMotherGamma N d N a b c e f 1 -
    secondFunctionalMotherGamma N d N a b c e f 2 -
    secondFunctionalMotherGamma N d N a b c e f 3 -
    secondFunctionalMotherGamma N d N a b c e f 4 +
    (∑ i ∈ Icc 5 19, secondFunctionalMotherGamma N d N a b c e f i) +
    (secondFunctionalMotherPrefixTerm N d N a b c e f [2, 3, 3, 3] -
      terminalUpperWord N d a b c e f [2, 3]) +
    (secondFunctionalMotherPrefixTerm N d N a b c e f [3, 3, 3, 3] -
      terminalUpperWord N d a b c e f [3, 3] -
      terminalUpperWord N d a b c e f [3, 3, 3])

theorem terminal_signed_local_eq {N d : ℕ} {a b c e f : ℝ}
    (hcop : ∀ r ∈ primeWindow N a f, r.Coprime d) :
    terminalSignedLocal N d a b c e f = secondFunctionalMotherLocal N d N a b c e f := by
  have h20 : secondFunctionalMotherPrefixTerm N d N a b c e f [2, 3, 3, 3] -
      terminalUpperWord N d a b c e f [2, 3] =
        secondFunctionalMotherGamma N d N a b c e f 20 := by
    have h := terminal_debit_eq_word (b := b) (c := c) (e := e) [2, 3] hcop
    rw [terminal_debit_signed] at h
    simpa only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.cons_append, List.nil_append] using h
  unfold terminalSignedLocal secondFunctionalMotherLocal
  rw [h20, gamma21_two_debits hcop,
    sum_Icc_succ_top (a := 5) (b := 20) (by omega),
    sum_Icc_succ_top (a := 5) (b := 19) (by omega)]
  ring

private theorem bad_prime_zero {N p : ℕ} {a u : ℝ}
    (hp : p.Prime) (hu : u ≤ (p : ℝ)) :
    fourthRowMotherBadPrime N p a u = 0 := by
  unfold fourthRowMotherBadPrime
  apply sum_eq_zero
  intro q hq
  obtain ⟨hq, hdiv⟩ := mem_filter.mp hq
  have hprime := (mem_primeWindow.mp hq).1
  have hqp : q < p := by exact_mod_cast (mem_primeWindow.mp hq).2.2.2.trans_le hu
  exact False.elim ((hprime.coprime_iff_not_dvd.mp
    ((Nat.coprime_primes hprime hp).mpr (ne_of_lt hqp))) hdiv)

theorem terminal_prime_count {N p : ℕ} {a b c e f z : ℝ}
    (hp : p.Prime) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f)
    (hfz : f ≤ z) (hzp : z ≤ (p : ℝ)) :
    5 * (sieveCount N p N z : ℝ) ≤ terminalSignedLocal N p a b c e f := by
  have hf := hfz.trans hzp
  have hm := secondFunctionalMother_original_windows N p hab hbc hce hef
  rw [bad_prime_zero hp hf, bad_prime_zero hp (hce.trans (hef.trans hf)),
    bad_prime_zero hp (hef.trans hf), add_zero, add_zero, add_zero] at hm
  have hc : (sourceSieveCount N p (p * N) z : ℝ) ≤
      (sourceSieveCount N p (p * N) f : ℝ) := by
    exact_mod_cast sourceSieveCount_antitone N p (p * N) hfz
  rw [SingleUpperCounts.source_count hp hzp] at hc
  rw [terminal_signed_local_eq (fun r hr =>
    (Nat.coprime_primes (mem_primeWindow.mp hr).1 hp).mpr
      (ne_of_lt (by exact_mod_cast (mem_primeWindow.mp hr).2.2.2.trans_le hf)))]
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans hm

noncomputable def terminalRow : Fin 3 → SecondFunctionalParameters :=
  ![SecondFunctionalParameters.row2, SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

noncomputable def terminalPsiLeft (j : Fin 3) : ℝ :=
  1 / 2 - truncatedSixthLowerAlpha * (terminalRow j).s

noncomputable def terminalPsiRight (j : Fin 3) : ℝ :=
  if j.val = 0 then 1 / 3
  else 1 / 2 - truncatedSixthLowerAlpha * (2 + (2 + (j.val : ℝ)) / 10)

noncomputable def terminalPsiPrimes (j : Fin 3) (N : ℕ) : Finset ℕ :=
  primeWindow N ((N : ℝ) ^ terminalPsiLeft j) ((N : ℝ) ^ terminalPsiRight j)

theorem terminal_psi_windows (j : Fin 3) (N : ℕ) :
    terminalPsiPrimes j N =
      primeWindow N
        ((N : ℝ) ^ (1 / 2 - truncatedSixthLowerAlpha * (2 + (3 + (j.val : ℝ)) / 10)))
        ((N : ℝ) ^ (if j.val = 0 then 1 / 3
          else 1 / 2 - truncatedSixthLowerAlpha * (2 + (2 + (j.val : ℝ)) / 10))) := by
  fin_cases j <;> norm_num [terminalPsiPrimes, terminalPsiLeft, terminalPsiRight,
    terminalRow, SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
    SecondFunctionalParameters.row4]

theorem terminal_row_geometry (j : Fin 3) :
    (terminalRow j).MotherAdmissible ∧
      truncatedSixthLowerAlpha < terminalPsiLeft j ∧
      terminalPsiRight j ≤ 1 / 3 := by
  fin_cases j
  · exact ⟨SecondFunctionalParameters.row2_motherAdmissible,
      by norm_num [terminalPsiLeft, terminalRow, SecondFunctionalParameters.row2,
        truncatedSixthLowerAlpha],
      by norm_num [terminalPsiRight]⟩
  · exact ⟨SecondFunctionalParameters.row3_motherAdmissible,
      by norm_num [terminalPsiLeft, terminalRow, SecondFunctionalParameters.row3,
        truncatedSixthLowerAlpha],
      by norm_num [terminalPsiRight, truncatedSixthLowerAlpha]⟩
  · exact ⟨SecondFunctionalParameters.row4_motherAdmissible,
      by norm_num [terminalPsiLeft, terminalRow, SecondFunctionalParameters.row4,
        truncatedSixthLowerAlpha],
      by norm_num [terminalPsiRight, truncatedSixthLowerAlpha]⟩

theorem terminal_psi_cutoffs {N p : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100)
    (hp : p ∈ terminalPsiPrimes j N) :
    1 ≤ (N : ℝ) ^ (1 / 2 - δ) / p ∧
      wuLocalCutoff N δ p (terminalRow j).s ≤ (N : ℝ) ^ truncatedSixthLowerAlpha ∧
      (N : ℝ) ^ truncatedSixthLowerAlpha ≤ (p : ℝ) := by
  have hg := terminal_row_geometry j
  have hm := mem_primeWindow.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hm.1.pos
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hs : 0 < (terminalRow j).s := by linarith [hg.1.one_le_s]
  have hlow : (N : ℝ) ^ (1 / 2 - δ - terminalPsiRight j) ≤
      (N : ℝ) ^ (1 / 2 - δ) / p := by
    apply (le_div_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 - δ - terminalPsiRight j) *
          (N : ℝ) ^ terminalPsiRight j :=
        mul_le_mul_of_nonneg_left hm.2.2.2.le (by positivity)
      _ = _ := by rw [← rpow_add hN0]; congr 1; ring
  have hratio : (N : ℝ) ^ (1 / 2 - δ) / p ≤
      (N : ℝ) ^ (truncatedSixthLowerAlpha * (terminalRow j).s) := by
    apply (div_le_iff₀ hp0).mpr
    calc
      _ ≤ (N : ℝ) ^ (truncatedSixthLowerAlpha * (terminalRow j).s + terminalPsiLeft j) :=
        rpow_le_rpow_of_exponent_le hN1.le
          (by dsimp [terminalPsiLeft]; linarith)
      _ = _ := rpow_add hN0 _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hm.2.2.1 (by positivity)
  refine ⟨(one_le_rpow hN1.le (by linarith [hg.2.2])).trans hlow,
    ?_, (rpow_le_rpow_of_exponent_le hN1.le hg.2.1.le).trans hm.2.2.1⟩
  calc
    wuLocalCutoff N δ p (terminalRow j).s ≤
        ((N : ℝ) ^ (truncatedSixthLowerAlpha * (terminalRow j).s)) ^
          (1 / (terminalRow j).s) :=
      rpow_le_rpow (by positivity) hratio (one_div_nonneg.mpr hs.le)
    _ = _ := by
      rw [← rpow_mul (Nat.cast_nonneg N)]
      congr 1
      field_simp

theorem terminal_psi_actual_count {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    5 * (∑ p ∈ primeWindow N
      ((N : ℝ) ^ (1 / 2 - truncatedSixthLowerAlpha * (2 + (3 + (j.val : ℝ)) / 10)))
      ((N : ℝ) ^ (if j.val = 0 then 1 / 3
        else 1 / 2 - truncatedSixthLowerAlpha * (2 + (2 + (j.val : ℝ)) / 10))),
      (sieveCount N p N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)) ≤
      ∑ p ∈ terminalPsiPrimes j N,
        terminalSignedLocal N p
          (wuLocalCutoff N δ p (terminalRow j).S)
          (wuLocalCutoff N δ p (terminalRow j).kappa1)
          (wuLocalCutoff N δ p (terminalRow j).kappa2)
          (wuLocalCutoff N δ p (terminalRow j).kappa3)
          (wuLocalCutoff N δ p (terminalRow j).s) := by
  rw [← terminal_psi_windows, mul_sum]
  apply sum_le_sum
  intro p hp
  have hg := (terminal_row_geometry j).1
  have hc := terminal_psi_cutoffs j hN hd hh hp
  have hs : 0 < (terminalRow j).s := by linarith [hg.one_le_s]
  have hanti {s S : ℝ} (hs : 0 < s) (hle : s ≤ S) :
      wuLocalCutoff N δ p S ≤ wuLocalCutoff N δ p s :=
    rpow_le_rpow_of_exponent_le hc.1 (one_div_le_one_div_of_le hs hle)
  exact terminal_prime_count (mem_primeWindow.mp hp).1
    (hanti (hs.trans_le (hg.s_le_kappa3.trans
      (hg.kappa3_lt_kappa2.le.trans hg.kappa2_lt_kappa1.le))) hg.kappa1_le_S)
    (hanti (hs.trans_le (hg.s_le_kappa3.trans hg.kappa3_lt_kappa2.le))
      hg.kappa2_lt_kappa1.le)
    (hanti (hs.trans_le hg.s_le_kappa3) hg.kappa3_lt_kappa2.le)
    (hanti hs hg.s_le_kappa3) hc.2.1 hc.2.2

end Wu18938Campaign.M2
