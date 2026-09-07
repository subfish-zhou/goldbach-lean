import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughElementary

noncomputable section
open Classical Finset LiLiuPrereqBuchstab
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open G12FineGrid

namespace G12RoughBoundary

def nearWindow (N : ℕ) (ε a : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter fun r =>
    ¬r ∣ N ∧ (m.minFac : ℝ) ≤ a*r

def nearWindowMass (N : ℕ) (ε a : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m * ((nearWindow N ε a m).card : ℝ)

/-- All body multiplicities, not merely one minFac witness, are injected. -/
theorem nearWindowMass_le_nearMass {N : ℕ} (ε a : ℝ) :
    400 * nearWindowMass N ε a ≤ nearMass N a := by
  let z : ℝ := (N : ℝ)^(4/53 : ℝ)
  let b : ℝ := (N : ℝ)^(4/33 : ℝ)
  let c : ℝ := (N : ℝ)^(3/11 : ℝ)
  let W : ℕ → Finset ℕ := fun m =>
    if m ∈ goldbachG12ActiveProductSupport N then nearWindow N ε a m else ∅
  have hgroup : (∑ v ∈ goldbachG12GoodCrossBodies N z b c,
      ((W (goldbachG11SwitchedBodyProd v)).card : ℝ)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    exact_mod_cast goldbachG12GoodCross_sum_product N z b c
      (fun m => ((W m).card : ℤ))
  have hmass : 400 * nearWindowMass N ε a =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    unfold nearWindowMass
    rw [mul_sum]
    calc
      _ = ∑ m ∈ goldbachG12ActiveProductSupport N,
          (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
        apply sum_congr rfl
        intro m hm
        simp only [W,if_pos hm,← mul_assoc,
          goldbachG12NormalizedCoefficient_mul_four_hundred,z,b,c]
      _ = _ := sum_subset (filter_subset _ _) (by
        intro m _ hm
        simp only [W,if_neg hm,card_empty,Nat.cast_zero,mul_zero])
  let S := (goldbachG12GoodCrossBodies N z b c).sigma
    (fun v => W (goldbachG11SwitchedBodyProd v))
  let T := (nearLabels N a).sigma (fun v => roughNumbers ((N : ℝ)/goldbachG11LabelProd v) v.2.2.2)
  let f : (Σ _v : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1,a.1.2.1,a.2,a.1.2.2.1⟩,a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨v,r⟩ ha
    obtain ⟨hv,hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd v ∈ goldbachG12ActiveProductSupport N := by
      by_contra hn
      simp only [W,if_neg hn,notMem_empty] at hr
    have hr' : r ∈ nearWindow N ε a (goldbachG11SwitchedBodyProd v) := by
      simpa only [W,if_pos hm] using hr
    obtain ⟨hrW,hrN,hnear⟩ := mem_filter.mp hr'
    obtain ⟨hl,hk⟩ := goldbachG12MainMass_good_pair_mem hv hm hrW hrN
    have hmin := goldbachG11SwitchedBodyProd_minFac
      (mem_goldbachG11GoodSwitchedBodies_iff.mp (goldbachG12GoodCrossBodies_subset _ _ _ _ hv)).1
    rw [hmin] at hnear
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨hl,hnear⟩,hk⟩
  have hinj : Set.InjOn f S := by
    rintro ⟨⟨t,s,q,k⟩,r⟩ _ ⟨⟨t',s',q',k'⟩,r'⟩ _ he
    have ht := congrArg (fun a => a.1.1) he
    have hs := congrArg (fun a => a.1.2.1) he
    have hr := congrArg (fun a => a.1.2.2.1) he
    have hq := congrArg (fun a => a.1.2.2.2) he
    have hk := congrArg (fun a => a.2) he
    dsimp [f] at ht hs hr hq hk
    subst t'; subst s'; subst r'; subst q'; subst k'
    rfl
  have hc : S.card ≤ T.card := card_le_card_of_injOn f hmap hinj
  have hS : (S.card : ℝ) = ∑ v ∈ goldbachG12GoodCrossBodies N z b c,
      ((W (goldbachG11SwitchedBodyProd v)).card : ℝ) := by
    simp only [S,card_sigma,Nat.cast_sum]
  have hT : (T.card : ℝ) = nearMass N a := by
    simp only [T,card_sigma,Nat.cast_sum,nearMass,roughCount]
  rw [hmass,← hgroup,← hS,← hT]
  exact_mod_cast hc

theorem pairMass_le_nearWindowMass (N : ℕ) (ε a : ℝ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 ∈ goldbachG12ActiveProductSupport N ∧
      p.2 ∈ nearWindow N ε a p.1) :
    (∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1) ≤ nearWindowMass N ε a := by
  let B := ((goldbachG12ActiveProductSupport N) ×ˢ range (N+1)).filter
    (fun p => p.2 ∈ nearWindow N ε a p.1)
  have hsub : S ⊆ B := by
    intro p hp
    obtain ⟨hm,hr⟩ := hS p hp
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm,
      (mem_filter.mp (mem_filter.mp hr).1).1⟩,hr⟩
  have heq : (∑ p ∈ B, goldbachG12NormalizedCoefficient N p.1) = nearWindowMass N ε a := by
    rw [show B = _ from rfl, sum_filter, sum_product]
    apply sum_congr rfl
    intro m _
    have he : (range (N+1)).filter (fun r => r ∈ nearWindow N ε a m) =
        nearWindow N ε a m := by
      ext r
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(mem_filter.mp (mem_filter.mp h).1).1,h⟩⟩
    rw [← sum_filter,he]
    simp only [sum_const,nsmul_eq_mul,mul_comm]
  rw [← heq]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    (goldbachG12NormalizedCoefficient_bounds N p.1).1)

/-- The literal failed-roughness branch uses the real body minFac. -/
theorem roughBoundary_in_nearWindow {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 0 < a)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ))
    {p : ℕ × ℕ} (hp : p ∈ roughBoundary ρ N ε) :
    p.1 ∈ goldbachG12ActiveProductSupport N ∧ p.2 ∈ nearWindow N ε a p.1 := by
  obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
  obtain ⟨hp,hfail⟩ := mem_filter.mp hp
  have hm := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  have hw := ((motherCell_window_iff ρ hN ε k hm).mp hp).2
  obtain ⟨hrange,hrp,hrN,hlo,hhi⟩ := mem_filter.mp hw
  obtain ⟨hlo,hTr⟩ := max_lt_iff.mp hlo
  obtain ⟨hhi,_⟩ := le_min_iff.mp hhi
  have hrW : p.2 ∈ goldbachG11LinkedPrimeWindow N ε p.1 :=
    mem_filter.mpr ⟨hrange,hrp,hlo,hhi⟩
  have hfR : (p.1.minFac : ℝ) < shortUpper ρ N k := by exact_mod_cast hfail
  have hnear : (p.1.minFac : ℝ) ≤ a*p.2 :=
    ((hfR.trans_le (hmesh k hk)).trans (mul_lt_mul_of_pos_left hTr ha)).le
  exact ⟨hm,mem_filter.mpr ⟨hrW,hrp.coprime_iff_not_dvd.mp hrN,hnear⟩⟩

/-- The source-level physical rough-boundary mass, with all factor 400 restored. -/
theorem roughBoundary_mass_le_nearMass {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 0 < a)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) :
    400*(∑ p ∈ roughBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤ nearMass N a := by
  exact (mul_le_mul_of_nonneg_left (pairMass_le_nearWindowMass N ε a _
    (fun _ hp => roughBoundary_in_nearWindow hN ha hmesh hp)) (by norm_num : (0 : ℝ) ≤ 400)).trans
      (nearWindowMass_le_nearMass ε a)

end G12RoughBoundary
