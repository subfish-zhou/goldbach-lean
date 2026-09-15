import W09ScalarTactics

namespace WuTarget.W09
noncomputable section

def seedQ : Fin 9 → ℚ :=
  ![15826959223/1000000000000, 15255699828/1000000000000,
    13904075181/1000000000000, 11781229047/1000000000000,
    9411030887/1000000000000, 6562045207/1000000000000,
    3537860555/1000000000000, 1056766244/1000000000000, 0]

def seed (i : Fin 9) : ℝ := seedQ i

def increment : Fin 9 → ℝ :=
  ![602223/1000000000000, 7728828/1000000000000,
    5318181/1000000000000, 5170047/1000000000000,
    5819887/1000000000000, 3095207/1000000000000,
    1109555/1000000000000, 115244/1000000000000, 0]

def forcingSlack (i : Fin 9) : ℝ :=
  Fin.addCases (m := 4) (n := 5) (motive := fun _ => ℝ)
    (fun j => Fin.cases (motive := fun _ => ℝ) (Wu04CurvePaid.slack / 5)
      (fun k => Wu04RemainingStrongPublication.slack k / 5) j)
    (fun j => Fin.lastCases (motive := fun _ => ℝ) 0 Wu04FirstPublication.slack j) i

theorem curve_increment_paid :
    (602223/1000000000000 : ℝ) ≤ Wu04CurvePaid.slack / 10 := by
  rw [Wu04CurvePaid.slack_exact]
  norm_num

theorem remaining_increment_zero :
    (7728828/1000000000000 : ℝ) ≤ Wu04RemainingStrongPublication.slack 0 / 10 := by
  w09_remaining_scalar

theorem remaining_increment_one :
    (5318181/1000000000000 : ℝ) ≤ Wu04RemainingStrongPublication.slack 1 / 10 := by
  w09_remaining_scalar

theorem remaining_increment_two :
    (5170047/1000000000000 : ℝ) ≤ Wu04RemainingStrongPublication.slack 2 / 10 := by
  change _ ≤ Wu04RemainingStrongPublication.slack (Fin.succ (Fin.succ (0 : Fin 1))) / 10
  w09_remaining_scalar
  norm_num [Fin.ext_iff]

theorem first_increment_zero :
    (5819887/1000000000000 : ℝ) ≤ Wu04FirstPublication.slack 0 / 2 := by
  w09_first_scalar

theorem first_increment_one :
    (3095207/1000000000000 : ℝ) ≤ Wu04FirstPublication.slack 1 / 2 := by
  w09_first_scalar

theorem first_increment_two :
    (1109555/1000000000000 : ℝ) ≤ Wu04FirstPublication.slack 2 / 2 := by
  change _ ≤ Wu04FirstPublication.slack (Fin.succ (Fin.succ (0 : Fin 2))) / 2
  w09_first_scalar

theorem first_increment_three :
    (115244/1000000000000 : ℝ) ≤ Wu04FirstPublication.slack 3 / 2 := by
  change _ ≤ Wu04FirstPublication.slack (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) / 2
  w09_first_scalar

theorem seed_eq_publication_add_increment (i : Fin 9) :
    seed i = NineFeedbackStrength.publication i + increment i := by
  have hp : NineFeedbackStrength.publication =
      (![15826357/1000000000, 15247971/1000000000, 13898757/1000000000,
        11776059/1000000000, 9405211/1000000000, 6558950/1000000000,
        3536751/1000000000, 1056651/1000000000, 0] : Fin 9 → ℝ) := by
    funext j
    fin_cases j <;> rfl
  rw [hp]
  fin_cases i <;> norm_num [seed, seedQ, increment]

theorem increment_le_half_slack (i : Fin 9) : increment i ≤ forcingSlack i / 2 := by
  fin_cases i
  · change (602223/1000000000000 : ℝ) ≤ (Wu04CurvePaid.slack / 5) / 2
    linarith only [curve_increment_paid]
  · change (7728828/1000000000000 : ℝ) ≤ (Wu04RemainingStrongPublication.slack 0 / 5) / 2
    linarith only [remaining_increment_zero]
  · change (5318181/1000000000000 : ℝ) ≤ (Wu04RemainingStrongPublication.slack 1 / 5) / 2
    linarith only [remaining_increment_one]
  · change (5170047/1000000000000 : ℝ) ≤ (Wu04RemainingStrongPublication.slack 2 / 5) / 2
    linarith only [remaining_increment_two]
  · exact first_increment_zero
  · exact first_increment_one
  · exact first_increment_two
  · exact first_increment_three
  · change (0 : ℝ) ≤ 0 / 2
    norm_num

theorem increment_pos (i : Fin 8) : 0 < increment i.castSucc := by
  fin_cases i <;> norm_num [increment]

theorem forcingSlack_pos (i : Fin 8) : 0 < forcingSlack i.castSucc := by
  linarith only [increment_pos i, increment_le_half_slack i.castSucc]

theorem seed_strictly_stronger (i : Fin 8) :
    NineFeedbackStrength.publication i.castSucc < seed i.castSucc := by
  rw [seed_eq_publication_add_increment]
  exact lt_add_of_pos_right _ (increment_pos i)

theorem seed_nonneg (i : Fin 9) : 0 ≤ seed i := by
  fin_cases i <;> norm_num [seed, seedQ]

theorem terminal_seed : seed 8 = 0 := by
  change ((0 : ℚ) : ℝ) = 0
  norm_num

theorem terminal_slack : forcingSlack 8 = 0 := rfl

end
end WuTarget.W09
