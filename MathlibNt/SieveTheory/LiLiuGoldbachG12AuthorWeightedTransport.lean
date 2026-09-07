import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport

open scoped BigOperators
open Classical Finset LiLiuPrereqBuchstab
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Each individual first-prime coordinate keeps its weight. -/
def goldbachG12WeightedSource (N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    ∑ r ∈ goldbachG11LinkedPrimeWindow N ε m, w r

def goldbachG12WeightedGood (N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    ∑ r ∈ (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N), w r

def goldbachG12WeightedBad (N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, goldbachG12NormalizedCoefficient N m *
    ∑ r ∈ (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => r ∣ N), w r

/-- Full unconditioned rough cofactor mother on the original closed cross. -/
def goldbachG12WeightedRough (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
    w v.2.2.1 * (roughCount ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2 : ℝ)

private def g12WeightedActiveWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  if m ∈ goldbachG12ActiveProductSupport N then
    (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => ¬r ∣ N) else ∅

theorem goldbachG12GoodCross_sum_product_real (N : ℕ) (z b c : ℝ) (f : ℕ → ℝ) :
    (∑ u ∈ goldbachG12GoodCrossBodies N z b c, f (goldbachG11SwitchedBodyProd u)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ)*f m := by
  classical
  have hh : (goldbachG12GoodCrossBodies N z b c).filter
      (fun u => goldbachG11SwitchedBodyProd u ∈ goldbachG12ProductSupport N z b c) =
      goldbachG12GoodCrossBodies N z b c := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hf := Finset.sum_fiberwise_eq_sum_filter (goldbachG12GoodCrossBodies N z b c)
    (goldbachG12ProductSupport N z b c) goldbachG11SwitchedBodyProd
    (fun u => f (goldbachG11SwitchedBodyProd u))
  rw [hh] at hf
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m _
  rw [goldbachG12ProductCoefficient_eq_card]
  calc
    _ = ∑ _u ∈ (goldbachG12GoodCrossBodies N z b c).filter
        (fun u => goldbachG11SwitchedBodyProd u = m), f m := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [(Finset.mem_filter.mp hu).2]
    _ = _ := by simp

theorem goldbachG12WeightedGood_le_fullRough (N : ℕ) (ε : ℝ) (w : ℕ → ℝ)
    (hw : ∀ r, 0 ≤ w r) :
    400 * goldbachG12WeightedGood N ε w ≤ goldbachG12WeightedRough N w := by
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  let b : ℝ := (N : ℝ) ^ (4 / 33 : ℝ)
  let c : ℝ := (N : ℝ) ^ (3/11 : ℝ)
  let W := g12WeightedActiveWindow N ε
  have hgroup :
      (∑ u ∈ goldbachG12GoodCrossBodies N z b c,
        (∑ r ∈ W (goldbachG11SwitchedBodyProd u), w r)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (∑ r ∈ W m, w r) := by
    exact goldbachG12GoodCross_sum_product_real N z b c (fun m => ∑ r ∈ W m, w r)
  have hmass : 400 * goldbachG12WeightedGood N ε w =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (∑ r ∈ W m, w r) := by
    unfold goldbachG12WeightedGood
    rw [mul_sum]
    calc
      _ = ∑ m ∈ goldbachG12ActiveProductSupport N,
          (goldbachG12ProductCoefficient N z b c m : ℝ) * (∑ r ∈ W m, w r) := by
        apply sum_congr rfl
        intro m hm
        simp only [W, g12WeightedActiveWindow, if_pos hm,
          ← mul_assoc, goldbachG12NormalizedCoefficient_mul_four_hundred, z, b, c]
      _ = _ := sum_subset (filter_subset _ _) (by
        intro m _ hm
        simp only [W, g12WeightedActiveWindow, if_neg hm, sum_empty, mul_zero])
  let S := (goldbachG12GoodCrossBodies N z b c).sigma
    (fun u => W (goldbachG11SwitchedBodyProd u))
  let T := (goldbachG12Labels N z b c).sigma
    (fun v => roughNumbers ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _u : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1, a.1.2.1, a.2, a.1.2.2.1⟩, a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨u, r⟩ ha
    obtain ⟨hu, hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd u ∈ goldbachG12ActiveProductSupport N := by
      by_contra hn
      simp only [W, g12WeightedActiveWindow, if_neg hn, notMem_empty] at hr
    have hr' : r ∈ (goldbachG11LinkedPrimeWindow N ε
        (goldbachG11SwitchedBodyProd u)).filter (fun r => ¬r ∣ N) := by
      simpa only [W, g12WeightedActiveWindow, if_pos hm] using hr
    exact mem_sigma.mpr
      (goldbachG12MainMass_good_pair_mem hu hm (mem_filter.mp hr').1 (mem_filter.mp hr').2)
  have hinj : Set.InjOn f S := by
    rintro ⟨⟨t, s, q, k⟩, r⟩ _ ⟨⟨t', s', q', k'⟩, r'⟩ _ he
    have ht := congrArg (fun a => a.1.1) he
    have hs := congrArg (fun a => a.1.2.1) he
    have hr := congrArg (fun a => a.1.2.2.1) he
    have hq := congrArg (fun a => a.1.2.2.2) he
    have hk := congrArg (fun a => a.2) he
    dsimp [f] at ht hs hr hq hk
    subst t'; subst s'; subst r'; subst q'; subst k'
    rfl
  have hc : (∑ a ∈ S, w a.2) ≤ ∑ a ∈ T, w a.1.2.2.1 := by
    calc
      _ = ∑ a ∈ S.image f, w a.1.2.2.1 := by
        rw [sum_image hinj]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (by intro a ha; obtain ⟨b,hb,rfl⟩ := mem_image.mp ha; exact hmap b hb)
        (by intro a _ _; exact hw _)
  rw [hmass, ← hgroup]
  have hS : (∑ a ∈ S, w a.2) =
      ∑ u ∈ goldbachG12GoodCrossBodies N z b c,
        ∑ r ∈ W (goldbachG11SwitchedBodyProd u), w r := by
    simp only [S, sum_sigma]
  have hT : (∑ a ∈ T, w a.1.2.2.1) = goldbachG12WeightedRough N w := by
    simp only [T, sum_sigma, sum_const, nsmul_eq_mul, goldbachG12WeightedRough,
      roughCount, z, b, c]
    apply sum_congr rfl
    intro v _
    ring
  rw [← hS, ← hT]
  exact hc

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
