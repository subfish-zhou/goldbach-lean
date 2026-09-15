import MathlibNt.Wu2008DoubleSieve.FourRoughIteratedRegularity

namespace Wu2008DoubleSieve.FourRoughClosedMass
open Finset Set Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical
noncomputable section

def Q3 (N : ℕ) (e : Bool) (x y z : ℝ) : ℝ :=
  primeOrderedClosedSum N (lower e z) (upper e z) (F x y z)
def Q2 (N : ℕ) (e : Bool) (x y : ℝ) : ℝ :=
  primeOrderedClosedSum N (cap y) beta (Q3 N e x y)
def Q1 (N : ℕ) (e : Bool) (x : ℝ) : ℝ :=
  primeOrderedClosedSum N (cap x) beta (Q2 N e x)
def Q0 (N : ℕ) (e : Bool) : ℝ :=
  primeOrderedClosedSum N alpha beta (Q1 N e)

theorem closed_coord {N p : ℕ} {a b : ℝ} (hN : 1 < N)
    (hp : p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b)) : coord N p ∈ Icc a b := by
  obtain ⟨hpp,hlo,hhi⟩ := (mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) b)).mp hp
  exact coord_bounds hN hpp.pos hlo hhi

theorem subwindow_mass {N : ℕ} {a b : ℝ} (hN : 1 < N)
    (ha : a ∈ low) (hb : b ∈ low) (hm : windowMass N ≤ 5) :
    (∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) ≤ 5 := by
  apply (sum_le_sum_of_subset_of_nonneg (s := primesIcc ((N : ℝ)^a) ((N : ℝ)^b))
    (t := window N) ?_ (by intros; positivity)).trans hm
  intro p hp
  have hc := closed_coord hN hp
  have hprime := ((mem_primesIcc (rpow_nonneg (Nat.cast_nonneg N) b)).mp hp).1
  exact mem_window_of_coord hN hprime ⟨ha.1.trans hc.1,hc.2.trans hb.2⟩

theorem closed_replace {N : ℕ} {a b eta : ℝ} {f g : ℝ → ℝ}
    (hN : 1 < N) (ha : a ∈ low) (hb : b ∈ low) (hm : windowMass N ≤ 5)
    (he : 0 ≤ eta) (hd : ∀ t ∈ low, |f t-g t| ≤ eta) :
    |primeOrderedClosedSum N a b f-primeOrderedClosedSum N a b g| ≤ 5*eta := by
  have hs : |primeOrderedClosedSum N a b f-primeOrderedClosedSum N a b g| ≤
      eta*(∑ p ∈ primesIcc ((N : ℝ)^a) ((N : ℝ)^b), 1/(p : ℝ)) := by
    simp only [primeOrderedClosedSum, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro p hp
    have hc := closed_coord hN hp
    have hpc : coord N p ∈ low := ⟨ha.1.trans hc.1,hc.2.trans hb.2⟩
    rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    exact (div_le_div_of_nonneg_right (hd _ hpc) (Nat.cast_nonneg p)).trans_eq
      (by rw [mul_one_div])
  have hm' := mul_le_mul_of_nonneg_left (subwindow_mass hN ha hb hm) he
  linarith only [hs,hm']

/-- Four genuine closed-prime quadratures, with all errors charged in full. -/
theorem Q0_uniform {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ e : Bool, |Q0 N e-J0 e| < epsilon := by
  let eta := epsilon/157
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨T0,hT0,hmass⟩ := windowMass_uniform
  obtain ⟨T1,hT1,h1⟩ := SeventhEighth.classical_low_weighted_uniform 15 7200 eta
    (by norm_num) (by norm_num) heta
  obtain ⟨T2,hT2,h2⟩ := SeventhEighth.classical_low_weighted_uniform 60 29250 eta
    (by norm_num) (by norm_num) heta
  obtain ⟨T3,hT3,h3⟩ := SeventhEighth.classical_low_weighted_uniform 240 116100 eta
    (by norm_num) (by norm_num) heta
  obtain ⟨T4,hT4,h4⟩ := SeventhEighth.classical_low_weighted_uniform 960 464400 eta
    (by norm_num) (by norm_num) heta
  refine ⟨max T0 (max T1 (max T2 (max T3 T4))), by omega, ?_⟩
  intro N hN e
  have hN1 : 1 < N := by omega
  have hm := hmass N (by omega)
  have hin (x y z : ℝ) (hx : x ∈ low) (hy : y ∈ low) (hz : z ∈ low) :
      |Q3 N e x y z-J3 e x y z| ≤ eta := by
    exact (h1 N (by omega) (F x y z) (lower e z) (upper e z)
      (low_continuous (F_fourth hx hy hz)) (fun t _ => F_bound x y z t)
      (F_fourth hx hy hz) (lower_low e z).1 (lower_le_upper e z) (upper_low e z).2).le
  have hmid (x y : ℝ) (hx : x ∈ low) (hy : y ∈ low) :
      |Q2 N e x y-J2 e x y| ≤ 6*eta := by
    have hr := closed_replace hN1 (cap_low y) beta_low hm heta.le
      (fun z hz => hin x y z hx hy hz)
    have hq := (h2 N (by omega) (J3 e x y) (cap y) beta
      (low_continuous (J3_third e hx hy)) (fun z _ => J3_bound e x y z)
      (J3_third e hx hy) (cap_low y).1 (cap_mem y).2 beta_low.2).le
    have ht := abs_sub_le (Q2 N e x y)
      (primeOrderedClosedSum N (cap y) beta (J3 e x y)) (J2 e x y)
    change |Q2 N e x y-primeOrderedClosedSum N (cap y) beta (J3 e x y)| ≤ _ at hr
    change |primeOrderedClosedSum N (cap y) beta (J3 e x y)-J2 e x y| ≤ _ at hq
    linarith only [hr,hq,ht]
  have hout (x : ℝ) (hx : x ∈ low) : |Q1 N e x-J1 e x| ≤ 31*eta := by
    have hr := closed_replace hN1 (cap_low x) beta_low hm
      (show 0 ≤ 6*eta by positivity) (fun y hy => hmid x y hx hy)
    have hq := (h3 N (by omega) (J2 e x) (cap x) beta
      (low_continuous (J2_second e hx)) (fun y _ => J2_bound e x y)
      (J2_second e hx) (cap_low x).1 (cap_mem x).2 beta_low.2).le
    have ht := abs_sub_le (Q1 N e x)
      (primeOrderedClosedSum N (cap x) beta (J2 e x)) (J1 e x)
    change |Q1 N e x-primeOrderedClosedSum N (cap x) beta (J2 e x)| ≤ _ at hr
    change |primeOrderedClosedSum N (cap x) beta (J2 e x)-J1 e x| ≤ _ at hq
    linarith only [hr,hq,ht]
  have hr := closed_replace hN1 alpha_low beta_low hm
    (show 0 ≤ 31*eta by positivity) hout
  have hq := (h4 N (by omega) (J1 e) alpha beta
    (low_continuous (J1_lip e)) (fun x _ => J1_bound e x)
    (J1_lip e) alpha_low.1 fixed_geometry.2.2.1 beta_low.2).le
  have ht := abs_sub_le (Q0 N e) (primeOrderedClosedSum N alpha beta (J1 e)) (J0 e)
  change |Q0 N e-primeOrderedClosedSum N alpha beta (J1 e)| ≤ _ at hr
  change |primeOrderedClosedSum N alpha beta (J1 e)-J0 e| ≤ _ at hq
  dsimp [eta] at hr hq
  linarith only [hr,hq,ht,he]

end
end Wu2008DoubleSieve.FourRoughClosedMass
