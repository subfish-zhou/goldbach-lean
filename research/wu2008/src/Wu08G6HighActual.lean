import Wu08G6HighCount
import MathlibNt.Wu2008DoubleSieve.Omega3SourceBounds

/-! Source-level audit for the missing high-prime lower producer.
The ordinary AP bound and actual Theta below do NOT assert an h gain.
No change is made to the sixth count or to its existing same-mother payment. -/
namespace Wu08G6HighActual
open Finset Real Wu2008DoubleSieve
open scoped Classical
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

/-- Total product slack, not squared prefixes, suffices for positive actual Theta.
The coefficient keeps the full labelled convolution and true logarithmic integral. -/
theorem theta_lower_of_product_slack {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 ≤ δ)
    (hprod : (∏ j, V j) < (N : ℝ) ^ (1/2-δ)) :
    2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) ≤
    boxTheta N ((N : ℝ) ^ (1/2-δ)) (convolutionWuWindows N Δ V) := by
  apply boxTheta_lower_of_support _ hN
  · intro d hd
    exact boxConvolutionSupport_pos
      (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  · intro d hd
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast boxConvolutionSupport_pos
        (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
    have hdle := boxConvolutionSupport_le_product
      (fun j p hp => (mem_convolutionWuWindows.mp hp).2.2.2.le) hd
    have hd1 : (1 : ℝ) ≤ d := by
      exact_mod_cast (show 0 < d by exact_mod_cast hdpos)
    refine ⟨(one_lt_div hdpos).mpr (hdle.trans_lt hprod), ?_⟩
    have hQN : (N : ℝ) ^ (1/2-δ) ≤ N := by
      have h := rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
        (show (1/2 : ℝ)-δ ≤ 1 by linarith)
      simpa only [rpow_one] using h
    exact (div_le_self (rpow_nonneg (Nat.cast_nonneg N) _) hd1).trans hQN

/-- One common threshold for unrestricted high-prime boxes: ordinary AP
remainder plus a positive, genuinely normalized mass. No ordering or squared
prefix hypothesis is present. This is a distribution source, not the switching
mu^2*3^omega theorem and not the missing double-sieve lower comparison. -/
theorem unrestricted_AP_and_theta (k : ℕ) {δ A : ℝ} (hδ : 0 < δ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, (∀ j, (N : ℝ) ^ (δ ^ (k+1)) ≤ V j) →
        (∀ j, V j ≤ N) → (∏ j, V j) < (N : ℝ) ^ (1/2-δ) →
        convolutionAPError N (convolutionModulusCutoff N δ)
          (convolutionWuWindows N Δ V) ≤ C * (N : ℝ) / log N ^ A ∧
        2 * liuUniversalProduct * (N : ℝ) / log N ^ 2 *
          ((1/12 : ℝ)^k / log (N : ℝ)^(5*k)) ≤
          boxTheta N ((N : ℝ) ^ (1/2-δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨C,hC,T1,hAP⟩ := wu_convolution_bombieri_vinogradov k hδ hA
  obtain ⟨T2,hmass⟩ := wu_boxConvolution_mass_bounds k (pow_pos hδ (k+1))
  refine ⟨C,hC,max 4 (max T1 T2),le_max_left _ _,?_⟩
  intro N hN i hik Δ hlo hhi V hV hVN hprod
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  refine ⟨hAP N hN1 i hik Δ hlo hhi V hV, ?_⟩
  exact (mul_le_mul_of_nonneg_left (hmass N hN2 i hik Δ hlo hhi V hV hVN).1
    (by have := liuUniversalProduct_pos; positivity)).trans
      (theta_lower_of_product_slack hN4 hδ.le hprod)

/-- Every prime divisor of every U_k convolution product obeys the first-prime
ceiling, independently of tuple length, overlap, and alternative factorization. -/
theorem source_prime_divisor_square_lt {i k N d p : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hp : p.Prime) (hpd : p ∣ d) :
    (p : ℝ)^2 < (N : ℝ) ^ (1/2-δ) := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
  obtain ⟨j,_,hj⟩ := hp.prime.dvd_finsetProd_iff v |>.mp hpd
  have hlabel := mem_convolutionWuWindows.mp (Fintype.mem_piFinset.mp hv j)
  have he : p = v j := (Nat.dvd_prime hlabel.1).mp hj |>.resolve_left hp.ne_one
  have hV1 : ∀ l, 1 ≤ V l := fun l =>
    (one_le_rpow (by exact_mod_cast hN) (pow_nonneg hδ (k+1))).trans (hb.2.2.2.2.1 l)
  have hprefix : 1 ≤ ∏ l ∈ univ.filter (fun l : Fin i => l < j), V l :=
    one_le_prod (fun l _ => hV1 l)
  have hsq : (V j)^2 ≤ (N : ℝ) ^ (1/2-δ) := by
    have h := hb.2.2.2.2.2 j
    nlinarith [sq_nonneg (V j)]
  have hlt : (p : ℝ) < V j := by simpa only [he] using hlabel.2.2.2
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  nlinarith [hV1 j]

/-- High prime divisibility annihilates the actual convolution coefficient.
Thus merely reboxing, relabelling, or increasing k cannot supply the missing weight. -/
theorem source_coefficient_zero {i k N d p : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hb : wuSourceBox k δ N i Δ V)
    (hp : p.Prime) (hpd : p ∣ d)
    (hhigh : (N : ℝ) ^ (1/2-δ) ≤ (p : ℝ)^2) :
    convolutionCoeff (convolutionWuWindows N Δ V) d = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hc
  exact (not_lt_of_ge hhigh) (source_prime_divisor_square_lt hN hδ hb
    (mem_boxConvolutionSupport.mpr hc) hp hpd)

/-- The strict y>1/4 prime range satisfies the annihilation hypothesis for every
fixed nonnegative delta. It is not repaired by increasing N. -/
theorem quarter_high_coefficient_zero {i k N d p : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) (hb : wuSourceBox k δ N i Δ V)
    (hp : p.Prime) (hpd : p ∣ d) (hhigh : (N : ℝ) ^ (1/4 : ℝ) < p) :
    convolutionCoeff (convolutionWuWindows N Δ V) d = 0 := by
  apply source_coefficient_zero hN hδ hb hp hpd
  have hpow : ((N : ℝ) ^ (1/4 : ℝ))^2 = (N : ℝ) ^ (1/2 : ℝ) := by
    rw [← rpow_two, ← rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hbase : (N : ℝ) ^ (1/2-δ) ≤ (N : ℝ) ^ (1/2 : ℝ) :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have hnonneg := rpow_nonneg (Nat.cast_nonneg N) (1/4 : ℝ)
  nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]

/-- Even signed finite combinations of existing source weights vanish at a high
prime multiple. This excludes only coefficientwise same-product replacement,
not a new arithmetic switching/counting argument. -/
theorem finite_source_combination_zero {m N d p : ℕ} {δ : ℝ}
    (k i : Fin m → ℕ) (Δ c : Fin m → ℝ) (V : (r : Fin m) → Fin (i r) → ℝ)
    (hN : 1 ≤ N) (hδ : 0 ≤ δ)
    (hb : ∀ r, wuSourceBox (k r) δ N (i r) (Δ r) (V r))
    (hp : p.Prime) (hpd : p ∣ d) (hhigh : (N : ℝ) ^ (1/4 : ℝ) < p) :
    (∑ r, c r * (convolutionCoeff (convolutionWuWindows N (Δ r) (V r)) d : ℝ)) = 0 := by
  apply sum_eq_zero
  intro r _
  rw [quarter_high_coefficient_zero hN hδ (hb r) hp hpd hhigh]
  simp

#check theta_lower_of_product_slack
#print axioms theta_lower_of_product_slack
#check unrestricted_AP_and_theta
#print axioms unrestricted_AP_and_theta
#check source_prime_divisor_square_lt
#print axioms source_prime_divisor_square_lt
#check source_coefficient_zero
#print axioms source_coefficient_zero
#check quarter_high_coefficient_zero
#print axioms quarter_high_coefficient_zero
#check finite_source_combination_zero
#print axioms finite_source_combination_zero
#check Wu2008DoubleSieve.wuImprovementComparison
#check Wu2008DoubleSieve.wuAdmissibleImprovements
#check Wu08G6High.Qtwo_exact
end
end Wu08G6HighActual
