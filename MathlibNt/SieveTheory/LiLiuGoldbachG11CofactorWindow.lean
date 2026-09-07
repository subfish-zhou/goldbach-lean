import MathlibNt.SieveTheory.LiLiuGoldbachG11PositivePrefixGeometry
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount

set_option autoImplicit false

open LiLiuPrereqBuchstab

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_rough_iff_survives (q : ℝ) (m : ℕ) :
    Rough q m ↔ SurvivesSieve 1 q m :=
  (goldbachG11_survives_one_iff q m).symm

/-- The actual positive-natural carrier, with a strict lower and closed upper endpoint. -/
noncomputable def goldbachG11CofactorWindow
    (N : ℕ) (ε : ℝ) (v : GoldbachG11Label) : Finset ℕ :=
  roughNumbers ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 \
    roughNumbers (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2

theorem mem_goldbachG11CofactorWindow_iff
    {N m : ℕ} {ε : ℝ} {v : GoldbachG11Label} :
    m ∈ goldbachG11CofactorWindow N ε v ↔
      0 < m ∧ ε * ((N : ℝ) / goldbachG11LabelProd v) < (m : ℝ) ∧
        (m : ℝ) ≤ (N : ℝ) / goldbachG11LabelProd v ∧
        SurvivesSieve 1 v.2.2.2 m := by
  classical
  simp only [goldbachG11CofactorWindow, Finset.mem_sdiff, mem_roughNumbers]
  constructor
  · rintro ⟨⟨hm, hmx, hr⟩, hl⟩
    exact ⟨hm, lt_of_not_ge (fun hml => hl ⟨hm, hml, hr⟩), hmx,
      (goldbachG11_rough_iff_survives _ _).mp hr⟩
  · rintro ⟨hm, hml, hmx, hr⟩
    exact ⟨⟨hm, hmx, (goldbachG11_rough_iff_survives _ _).mpr hr⟩,
      fun hl => (not_le_of_gt hml) hl.2.1⟩

theorem one_mem_goldbachG11CofactorWindow
    {N : ℕ} {ε : ℝ} {v : GoldbachG11Label} :
    1 ∈ goldbachG11CofactorWindow N ε v ↔
      ε * ((N : ℝ) / goldbachG11LabelProd v) < 1 ∧
        1 ≤ (N : ℝ) / goldbachG11LabelProd v := by
  simp [mem_goldbachG11CofactorWindow_iff, goldbachG11_survives_one]

theorem goldbachG11CofactorWindow_prefix_subset
    (N : ℕ) {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (v : GoldbachG11Label) :
    roughNumbers (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2 ⊆
      roughNumbers ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 := by
  intro m hm
  obtain ⟨hm0, hml, hr⟩ := mem_roughNumbers.mp hm
  have hx : 0 ≤ (N : ℝ) / goldbachG11LabelProd v :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact mem_roughNumbers.mpr
    ⟨hm0, hml.trans (mul_le_of_le_one_left hx hε.2), hr⟩

theorem goldbachG11CofactorWindow_card
    (N : ℕ) {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (v : GoldbachG11Label) :
    (goldbachG11CofactorWindow N ε v).card =
      roughCount ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 -
        roughCount (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2 := by
  exact Finset.card_sdiff_of_subset (goldbachG11CofactorWindow_prefix_subset N hε v)

theorem goldbachG11CofactorWindow_card_real
    (N : ℕ) {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (v : GoldbachG11Label) :
    ((goldbachG11CofactorWindow N ε v).card : ℝ) =
      (roughCount ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 : ℝ) -
        (roughCount (ε * ((N : ℝ) / goldbachG11LabelProd v)) v.2.2.2 : ℝ) := by
  rw [goldbachG11CofactorWindow_card N hε v]
  exact Nat.cast_sub
    (Finset.card_le_card (goldbachG11CofactorWindow_prefix_subset N hε v))

/-- Natural division is exact only after the pair equation supplies divisibility;
the subtraction cast is justified by the original finite range. -/
theorem goldbachG11RoughPairs_cofactor_nat_div_cast
    {N p m : ℕ} {ε z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b)
    (hpm : (p, m) ∈ goldbachG11RoughPairs N ε v) :
    (N - p) / goldbachG11LabelProd v = m ∧
      (((N - p) / goldbachG11LabelProd v : ℕ) : ℝ) =
        ((N - p : ℕ) : ℝ) / goldbachG11LabelProd v ∧
      ((N - p : ℕ) : ℝ) = (N : ℝ) - (p : ℝ) := by
  obtain ⟨hpN, _, _, _, _, heq, _⟩ := mem_goldbachG11RoughPairs_iff.mp hpm
  have hd := goldbachG11LabelProd_pos hv
  have hn : N - p = goldbachG11LabelProd v * m := by
    rw [← heq, Nat.add_sub_cancel_left]
  have hdiv : (N - p) / goldbachG11LabelProd v = m := by
    rw [hn, Nat.mul_div_right _ hd]
  refine ⟨hdiv, ?_, Nat.cast_sub hpN⟩
  rw [hdiv]
  apply (eq_div_iff (show (goldbachG11LabelProd v : ℝ) ≠ 0 by
    exact_mod_cast hd.ne')).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hn.symm)

theorem goldbachG11RoughPairs_mem_window
    {N p m : ℕ} {ε z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b)
    (hpm : (p, m) ∈ goldbachG11RoughPairs N ε v) :
    m ∈ goldbachG11CofactorWindow N ε v := by
  obtain ⟨_, hm, _, _, _, _, hr⟩ := mem_goldbachG11RoughPairs_iff.mp hpm
  have hw := goldbachG11RoughPairs_cofactor_window hv hpm
  exact mem_goldbachG11CofactorWindow_iff.mpr
    ⟨hm, by simpa only [mul_div_assoc] using hw.1, hw.2.le,
      (goldbachG11_survives_one_iff _ _).mpr hr⟩

theorem goldbachG11CofactorWindow_prime_pair
    {N m : ℕ} {ε z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b)
    (hm : m ∈ goldbachG11CofactorWindow N ε v)
    (hp : (N - goldbachG11LabelProd v * m).Prime) :
    (N - goldbachG11LabelProd v * m, m) ∈ goldbachG11RoughPairs N ε v := by
  obtain ⟨hm0, hml, hmx, hr⟩ := mem_goldbachG11CofactorWindow_iff.mp hm
  have hd := goldbachG11LabelProd_pos hv
  have hdR : (0 : ℝ) < goldbachG11LabelProd v := by exact_mod_cast hd
  have hdmR : (goldbachG11LabelProd v : ℝ) * m ≤ N := by
    simpa only [mul_comm] using (le_div_iff₀ hdR).mp hmx
  have hdm : goldbachG11LabelProd v * m ≤ N := by exact_mod_cast hdmR
  have hmN : m ≤ N :=
    (Nat.le_mul_of_pos_left m hd).trans hdm
  have hlow : ε * (N : ℝ) < (goldbachG11LabelProd v : ℝ) * m := by
    rw [← mul_div_assoc] at hml
    simpa only [mul_comm] using (div_lt_iff₀ hdR).mp hml
  refine mem_goldbachG11RoughPairs_iff.mpr
    ⟨Nat.sub_le _ _, hm0, hmN, hp, ?_, Nat.sub_add_cancel hdm,
      (goldbachG11_survives_one_iff _ _).mp hr⟩
  rw [Nat.cast_sub hdm, Nat.cast_mul]
  calc
    _ < (N : ℝ) - ε * N := sub_lt_sub_left hlow _
    _ = (1 - ε) * N := by ring

open Classical in
theorem goldbachG11RoughCount_eq_prime_window
    {N : ℕ} {ε z b : ℝ} {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N z b) :
    goldbachG11RoughCount N ε v =
      (((goldbachG11CofactorWindow N ε v).filter
        (fun m => (N - goldbachG11LabelProd v * m).Prime)).card : ℤ) := by
  unfold goldbachG11RoughCount
  congr 1
  apply Finset.card_bij (fun pm _ => pm.2)
  · rintro ⟨p, m⟩ hpm
    have heq := (mem_goldbachG11RoughPairs_iff.mp hpm).2.2.2.2.2.1
    have hp := (mem_goldbachG11RoughPairs_iff.mp hpm).2.2.2.1
    have hsub : N - goldbachG11LabelProd v * m = p := by
      rw [← heq, Nat.add_sub_cancel]
    exact Finset.mem_filter.mpr ⟨goldbachG11RoughPairs_mem_window hv hpm, hsub ▸ hp⟩
  · rintro ⟨p, m⟩ hpm ⟨p', m'⟩ hpm' hmm
    have h1 := (mem_goldbachG11RoughPairs_iff.mp hpm).2.2.2.2.2.1
    have h2 := (mem_goldbachG11RoughPairs_iff.mp hpm').2.2.2.2.2.1
    dsimp at hmm
    apply Prod.ext
    · dsimp
      rw [hmm] at h1
      exact Nat.add_right_cancel (h1.trans h2.symm)
    · exact hmm
  · intro m hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    exact ⟨(N - goldbachG11LabelProd v * m, m),
      goldbachG11CofactorWindow_prime_pair hv hm hp, rfl⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig