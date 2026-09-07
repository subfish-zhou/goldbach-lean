import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundary
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport

noncomputable section
open Classical Finset LiLiuPrereqBuchstab
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace G12FineGrid

/-- The widened open lower endpoint retains even a closed epsilon endpoint. -/
theorem lower_product_band {a ε N T V r m : ℝ}
    (ha : 1 < a) (he : 0 < ε) (hN : 0 < N) (hm : 0 ≤ m)
    (hr : r ≤ V) (hV : V ≤ a*T) (hlo : ε*N ≤ r*m) (hfail : T*m < ε*N) :
    (ε/a)*N < r*m ∧ r*m ≤ (a*ε)*N := by
  have hap : 0 < a := by linarith
  have hediv : ε/a < ε := (div_lt_self he ha)
  refine ⟨(mul_lt_mul_of_pos_right hediv hN).trans_le hlo, ?_⟩
  calc
    r*m ≤ V*m := mul_le_mul_of_nonneg_right hr hm
    _ ≤ (a*T)*m := mul_le_mul_of_nonneg_right hV hm
    _ = a*(T*m) := by ring
    _ ≤ a*(ε*N) := (mul_lt_mul_of_pos_left hfail hap).le
    _ = (a*ε)*N := by ring

/-- The upper-product failure lands above N/a, with its original strict top. -/
theorem upper_product_band {a N T V r m : ℝ}
    (ha : 0 < a) (hm : 0 < m) (hr : T < r) (hV : V ≤ a*T)
    (hfail : N ≤ V*m) (hhi : r*m < N) :
    (1/a)*N < r*m ∧ r*m ≤ N := by
  refine ⟨?_,hhi.le⟩
  have hh : N < a*(r*m) := calc
    N ≤ V*m := hfail
    _ ≤ (a*T)*m := mul_le_mul_of_nonneg_right hV hm.le
    _ < (a*r)*m := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hr ha) hm
    _ = a*(r*m) := by ring
  have := (div_lt_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
  simpa only [one_div, inv_mul_eq_div] using this

/-- Raw original linked-window mass restricted by a product band. -/
def bandWindow (N : ℕ) (ε l u : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter fun r =>
    ¬r ∣ N ∧ l*N < (r : ℝ)*m ∧ (r : ℝ)*m ≤ u*N

def bandMass (N : ℕ) (ε l u : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m * ((bandWindow N ε l u m).card : ℝ)

/-- Both bands use the actual uniform thin-count producer. The quantifier on
all label-dependent endpoints remains after the common large-N threshold. -/
theorem product_bands_integral_budget {a ε : ℝ}
    (ha : 1 < a) (ha2 : a ≤ 2) (he : 0 < ε) (he2 : ε ≤ 2/15)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Real.log (N : ℝ)/(N : ℝ) *
        (goldbachG12ThinSum N (fun _ => ε/a) (fun _ => a*ε) +
          goldbachG12ThinSum N (fun _ => 1/a) (fun _ => 1)) ≤
        (564383/1000000 : ℝ) * (3*(a-1)) *
          goldbachG12PrimeIntegral (fun _ => 1) + δ := by
  have hap : 0 < a := by linarith
  have he1 : ε ≤ 1 := by linarith
  have hbase : 0 < ε/a := div_pos he hap
  have hbase1 : ε/a ≤ 1 := (div_le_iff₀ hap).mpr (by nlinarith)
  have hlo : ε/a ≤ a*ε := (div_le_self he.le ha.le).trans
    (le_mul_of_one_le_left he.le ha.le)
  have hhi : a*ε ≤ 1 := by nlinarith
  have hlwidth : a*ε-ε/a ≤ 2*(a-1) := by
    apply (le_of_mul_le_mul_right _ hap)
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr ha.le)]
  have huwidth : 1-1/a ≤ a-1 := by
    apply (le_of_mul_le_mul_right _ hap)
    field_simp
    nlinarith [sq_nonneg (a-1)]
  obtain ⟨N₁,hN₁,hb₁⟩ := goldbachG12ThinSum_integral_budget (ε/a) hbase hbase1
    (2*(a-1)) (by linarith) (δ/2) (half_pos hδ)
  obtain ⟨N₂,hN₂,hb₂⟩ := goldbachG12ThinSum_integral_budget (ε/a) hbase hbase1
    (a-1) (by linarith) (δ/2) (half_pos hδ)
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  have h₁ := hb₁ N ((le_max_left _ _).trans hN) (fun _ => ε/a) (fun _ => a*ε)
    (fun _ _ => ⟨le_rfl,hlo,hhi,hlwidth⟩)
  have h₂ := hb₂ N ((le_max_right _ _).trans hN) (fun _ => 1/a) (fun _ => 1)
    (fun _ _ => ⟨div_le_div_of_nonneg_right he1 hap.le,
      (div_le_iff₀ hap).mpr (by linarith),le_rfl,huwidth⟩)
  have hh := add_le_add h₁ h₂
  rw [← mul_add] at hh
  nlinarith only [hh]

/-- Injection of actual body/prime pairs into the two real-endpoint rough
counts. The factor 400 restores all original body multiplicities. -/
theorem bandMass_le_thinSum {N : ℕ} (ε l u : ℝ) (hlu : l ≤ u) :
    400 * bandMass N ε l u ≤
      goldbachG12ThinSum N (fun _ => l) (fun _ => u) := by
  let z : ℝ := (N : ℝ)^(4/53 : ℝ)
  let b : ℝ := (N : ℝ)^(4/33 : ℝ)
  let c : ℝ := (N : ℝ)^(3/11 : ℝ)
  let W : ℕ → Finset ℕ := fun m =>
    if m ∈ goldbachG12ActiveProductSupport N then bandWindow N ε l u m else ∅
  have hgroup : (∑ v ∈ goldbachG12GoodCrossBodies N z b c,
      ((W (goldbachG11SwitchedBodyProd v)).card : ℝ)) =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    exact_mod_cast goldbachG12GoodCross_sum_product N z b c
      (fun m => ((W m).card : ℤ))
  have hmass : 400 * bandMass N ε l u =
      ∑ m ∈ goldbachG12ProductSupport N z b c,
        (goldbachG12ProductCoefficient N z b c m : ℝ) * (W m).card := by
    unfold bandMass
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
  let R := fun (v : GoldbachG11Label) (x : ℝ) =>
    roughNumbers (x*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2
  have hsub (v : GoldbachG11Label) : R v l ⊆ R v u := by
    intro k hk
    obtain ⟨hk0,hk,hrough⟩ := mem_roughNumbers.mp hk
    exact mem_roughNumbers.mpr ⟨hk0,hk.trans
      (mul_le_mul_of_nonneg_right hlu (by positivity)),hrough⟩
  let S := (goldbachG12GoodCrossBodies N z b c).sigma
    (fun v => W (goldbachG11SwitchedBodyProd v))
  let T := (goldbachG12Labels N z b c).sigma (fun v => R v u \ R v l)
  let f : (Σ _v : GoldbachG11SwitchedBody, ℕ) → (Σ _v : GoldbachG11Label, ℕ) :=
    fun a => ⟨⟨a.1.1,a.1.2.1,a.2,a.1.2.2.1⟩,a.1.2.2.2⟩
  have hmap : ∀ a ∈ S, f a ∈ T := by
    rintro ⟨v,r⟩ ha
    obtain ⟨hv,hr⟩ := mem_sigma.mp ha
    have hm : goldbachG11SwitchedBodyProd v ∈ goldbachG12ActiveProductSupport N := by
      by_contra hn
      simp only [W,if_neg hn,notMem_empty] at hr
    have hr' : r ∈ bandWindow N ε l u (goldbachG11SwitchedBodyProd v) := by
      simpa only [W,if_pos hm] using hr
    obtain ⟨hrW,hrN,hlo,hhi⟩ := mem_filter.mp hr'
    obtain ⟨hl,hk⟩ := goldbachG12MainMass_good_pair_mem hv hm hrW hrN
    have hp : (0 : ℝ) < goldbachG11LabelProd ⟨v.1,v.2.1,r,v.2.2.1⟩ := by
      exact_mod_cast goldbachG12LabelProd_pos hl
    have hid : (v.2.2.2 : ℝ)*goldbachG11LabelProd ⟨v.1,v.2.1,r,v.2.2.1⟩ =
        (r : ℝ)*goldbachG11SwitchedBodyProd v := by
      simp only [goldbachG11LabelProd,goldbachG11SwitchedBodyProd,Nat.cast_mul]
      ring
    refine mem_sigma.mpr ⟨hl,mem_sdiff.mpr ⟨?_,?_⟩⟩
    · apply mem_roughNumbers.mpr
      obtain ⟨hk0,_,hrough⟩ := mem_roughNumbers.mp hk
      refine ⟨hk0,?_,hrough⟩
      change (v.2.2.2 : ℝ) ≤ u*((N : ℝ)/goldbachG11LabelProd _)
      rw [← mul_div_assoc]
      exact (le_div_iff₀ hp).mpr (hid ▸ hhi)
    · intro hbad
      have hb := (mem_roughNumbers.mp hbad).2.1
      change (v.2.2.2 : ℝ) ≤ l*((N : ℝ)/goldbachG11LabelProd _) at hb
      rw [← mul_div_assoc] at hb
      have hh := (le_div_iff₀ hp).mp hb
      rw [hid] at hh
      exact (not_le_of_gt hlo) hh
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
  have hT : (T.card : ℝ) = goldbachG12ThinSum N (fun _ => l) (fun _ => u) := by
    simp only [T,card_sigma,Nat.cast_sum,goldbachG12ThinSum]
    apply sum_congr rfl
    intro v _
    rw [card_sdiff_of_subset (hsub v),Nat.cast_sub (card_le_card (hsub v))]
    rfl
  rw [hmass,← hgroup,← hS,← hT]
  exact_mod_cast hc

/-- Weighted domination for any literal set of physical pairs. -/
theorem pairMass_le_bandMass (N : ℕ) (ε l u : ℝ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, p.1 ∈ goldbachG12ActiveProductSupport N ∧
      p.2 ∈ bandWindow N ε l u p.1) :
    (∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1) ≤ bandMass N ε l u := by
  let B := ((goldbachG12ActiveProductSupport N) ×ˢ range (N+1)).filter
    (fun p => p.2 ∈ bandWindow N ε l u p.1)
  have hsub : S ⊆ B := by
    intro p hp
    obtain ⟨hm,hr⟩ := hS p hp
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm,
      (mem_filter.mp (mem_filter.mp hr).1).1⟩,hr⟩
  have heq : (∑ p ∈ B, goldbachG12NormalizedCoefficient N p.1) = bandMass N ε l u := by
    rw [show B = _ from rfl, sum_filter, sum_product]
    apply sum_congr rfl
    intro m _
    have he : (range (N+1)).filter (fun r => r ∈ bandWindow N ε l u m) =
        bandWindow N ε l u m := by
      ext r
      simp only [mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(mem_filter.mp (mem_filter.mp h).1).1,h⟩⟩
    rw [← sum_filter,he]
    simp only [sum_const,nsmul_eq_mul,mul_comm]
  rw [← heq]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    (goldbachG12NormalizedCoefficient_bounds N p.1).1)

/-- Only the two product failures; the roughness failure is not paid here. -/
def productBoundary (ρ : ℝ) (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (indices ρ N).biUnion fun k => (motherCell ρ N ε k).filter fun p =>
    (shortLower ρ N k : ℝ)*p.1 < ε*N ∨ N ≤ shortUpper ρ N k*p.1

theorem productBoundary_in_bands {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 1 < a) (he : 0 < ε)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ))
    {p : ℕ × ℕ} (hp : p ∈ productBoundary ρ N ε) :
    p.1 ∈ goldbachG12ActiveProductSupport N ∧
      (p.2 ∈ bandWindow N ε (ε/a) (a*ε) p.1 ∨
        p.2 ∈ bandWindow N ε (1/a) 1 p.1) := by
  obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
  obtain ⟨hp,hfail⟩ := mem_filter.mp hp
  have hm := (mem_product.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
  have hw := ((motherCell_window_iff ρ hN ε k hm).mp hp).2
  obtain ⟨hrange,hrp,hrN,hlo,hhi⟩ := mem_filter.mp hw
  obtain ⟨hlo,hTr⟩ := max_lt_iff.mp hlo
  obtain ⟨hhi,hrV⟩ := le_min_iff.mp hhi
  have hrW : p.2 ∈ goldbachG11LinkedPrimeWindow N ε p.1 :=
    mem_filter.mpr ⟨hrange,hrp,hlo,hhi⟩
  have hrnd : ¬p.2 ∣ N := hrp.coprime_iff_not_dvd.mp hrN
  have hm0 : (0 : ℝ) < p.1 := by exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
  obtain ⟨_,_,_,_,_,heprod,hnprod,_⟩ := mem_filter.mp (mem_filter.mp hp).1
  have hnR : (p.2 : ℝ)*p.1 < N := by exact_mod_cast hnprod
  refine ⟨hm,?_⟩
  rcases hfail with hlow | hupp
  · have hh := lower_product_band ha he (by exact_mod_cast (show 0 < N by omega))
      hm0.le hrV (hmesh k hk) heprod.le hlow
    exact Or.inl (mem_filter.mpr ⟨hrW,hrnd,hh⟩)
  · have huR : (N : ℝ) ≤ (shortUpper ρ N k : ℝ)*p.1 := by exact_mod_cast hupp
    have hh := upper_product_band (show 0 < a by linarith) hm0 hTr (hmesh k hk) huR hnR
    exact Or.inr (mem_filter.mpr ⟨hrW,hrnd,hh.1,by simpa only [one_mul] using hh.2⟩)

/-- No cell-count loss: union first, then pay the two physical bands once. -/
theorem productBoundary_mass_le_bands {ρ a ε : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (ha : 1 < a) (he : 0 < ε)
    (hmesh : ∀ k ∈ indices ρ N,
      (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) :
    (∑ p ∈ productBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
      bandMass N ε (ε/a) (a*ε) + bandMass N ε (1/a) 1 := by
  let S := productBoundary ρ N ε
  let A := fun p : ℕ × ℕ => p.2 ∈ bandWindow N ε (ε/a) (a*ε) p.1
  have h₁ := pairMass_le_bandMass N ε (ε/a) (a*ε) (S.filter A) (by
    intro p hp
    obtain ⟨hp,hA⟩ := mem_filter.mp hp
    exact ⟨(productBoundary_in_bands hN ha he hmesh hp).1,hA⟩)
  have h₂ := pairMass_le_bandMass N ε (1/a) 1 (S.filter (fun p => ¬A p)) (by
    intro p hp
    obtain ⟨hp,hA⟩ := mem_filter.mp hp
    have hh := productBoundary_in_bands hN ha he hmesh hp
    exact ⟨hh.1,hh.2.resolve_left hA⟩)
  have heq : (∑ p ∈ S, goldbachG12NormalizedCoefficient N p.1) =
      (∑ p ∈ S.filter A, goldbachG12NormalizedCoefficient N p.1) +
        ∑ p ∈ S.filter (fun p => ¬A p), goldbachG12NormalizedCoefficient N p.1 := by
    rw [sum_filter,sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hA : A p <;> dsimp only [A] at hA ⊢ <;> simp [hA]
  rw [show productBoundary ρ N ε = S from rfl,heq]
  exact add_le_add h₁ h₂

/-- Actual fine-grid product-boundary payment at raw-mother normalization.
The roughness boundary and the output-prime second logarithm remain separate. -/
theorem productBoundary_integral_budget {a ε : ℝ}
    (ha : 1 < a) (ha2 : a ≤ 2) (he : 0 < ε) (he2 : ε ≤ 2/15)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ρ : ℝ,
      (∀ k ∈ indices ρ N,
        (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ)) →
      Real.log (N : ℝ)/(N : ℝ) *
        (400 * ∑ p ∈ productBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
        (564383/1000000 : ℝ) * (3*(a-1)) *
          goldbachG12PrimeIntegral (fun _ => 1) + δ := by
  obtain ⟨N₀,hN₀,hb⟩ := product_bands_integral_budget ha ha2 he he2 δ hδ
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ρ hmesh
  have hN1 : 1 ≤ N := by omega
  have hlog : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) (Nat.cast_nonneg _)
  have hlo : ε/a ≤ a*ε := (div_le_self he.le ha.le).trans
    (le_mul_of_one_le_left he.le ha.le)
  have hhi : 1/a ≤ (1 : ℝ) := (div_le_iff₀ (show 0 < a by linarith)).mpr (by linarith)
  have hmass := mul_le_mul_of_nonneg_left (productBoundary_mass_le_bands hN1 ha he hmesh)
    (show (0 : ℝ) ≤ 400 by norm_num)
  rw [mul_add] at hmass
  have hthin := hmass.trans (add_le_add (bandMass_le_thinSum ε _ _ hlo)
    (bandMass_le_thinSum ε _ _ hhi))
  exact (mul_le_mul_of_nonneg_left hthin hlog).trans (hb N hN)

/-- The remaining roughness branch, retained as a literal physical set. -/
def roughBoundary (ρ : ℝ) (N : ℕ) (ε : ℝ) : Finset (ℕ × ℕ) :=
  (indices ρ N).biUnion fun k => (motherCell ρ N ε k).filter fun p =>
    p.1.minFac < shortUpper ρ N k

/-- The complete original boundary is exactly the paid product branch union
an explicitly unpaid roughness branch; overlap is harmless. -/
theorem boundary_union_decomposition (ρ : ℝ) (N : ℕ) (ε : ℝ) :
    (indices ρ N).biUnion (boundaryCell ρ N ε) =
      productBoundary ρ N ε ∪ roughBoundary ρ N ε := by
  ext p
  constructor
  · intro hp
    obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
    have hm := (mem_sdiff.mp hp).1
    have hf := (boundaryCell_iff ρ N ε k p.1 p.2 hm).mp hp
    rcases hf with hr | hl | hu
    · exact mem_union_right _ (mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨hm,hr⟩⟩)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨hm,Or.inl hl⟩⟩)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨hm,Or.inr hu⟩⟩)
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
      obtain ⟨hm,hf⟩ := mem_filter.mp hp
      exact mem_biUnion.mpr ⟨k,hk,(boundaryCell_iff ρ N ε k p.1 p.2 hm).mpr
        (Or.inr hf)⟩
    · obtain ⟨k,hk,hp⟩ := mem_biUnion.mp hp
      obtain ⟨hm,hf⟩ := mem_filter.mp hp
      exact mem_biUnion.mpr ⟨k,hk,(boundaryCell_iff ρ N ε k p.1 p.2 hm).mpr
        (Or.inl hf)⟩

/-- The union budget is also exactly the sum over the original disjoint cells. -/
theorem productBoundary_sum_cells {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) (ε : ℝ)
    (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ productBoundary ρ N ε, f p) =
      ∑ k ∈ indices ρ N, ∑ p ∈ (motherCell ρ N ε k).filter
        (fun p => (shortLower ρ N k : ℝ)*p.1 < ε*N ∨ N ≤ shortUpper ρ N k*p.1), f p := by
  apply sum_biUnion
  intro k _ l _ hkl
  exact (cell_disjoint hρ N ε hkl).mono (filter_subset _ _) (filter_subset _ _)

/-- Explicit rounding allowance discharges every clipped short-cell ratio. -/
theorem short_ratio_of_rounding {ρ a : ℝ} (hρ : 1 < ρ) (hρa : ρ ≤ a)
    (N : ℕ) (hscale : ρ ≤ (a-ρ)*(lowCut N : ℝ)) (k : ℕ × ℕ) :
    (shortUpper ρ N k : ℝ) ≤ a*(shortLower ρ N k : ℝ) := by
  have hw : (shortUpper ρ N k : ℝ) ≤ ρ*((shortLower ρ N k : ℝ)+1) := by
    simpa only [shortUpper,shortLower,Nat.cast_min,Nat.cast_max] using
      clipped_width hρ (lowCut N) (highCut N) k.2
  have hlo : (lowCut N : ℝ) ≤ shortLower ρ N k := by
    exact_mod_cast le_max_left (lowCut N) (endpoint ρ k.2)
  have hh := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hρa)
  nlinarith only [hw,hscale,hh]

/-- A source-level body witness identifies minFac; no arbitrary new q is postulated. -/
theorem active_minFac_body_witness {N m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    ∃ v ∈ goldbachG12GoodCrossBodies N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
      goldbachG11SwitchedBodyProd v = m ∧ m.minFac = v.2.2.1 := by
  obtain ⟨v,hv,hvm⟩ := mem_image.mp (mem_filter.mp hm).1
  refine ⟨v,hv,hvm,?_⟩
  rw [← hvm]
  exact goldbachG11SwitchedBodyProd_minFac
    (mem_goldbachG11GoodSwitchedBodies_iff.mp (goldbachG12GoodCrossBodies_subset _ _ _ _ hv)).1

/-- Fully discharged rounded-grid budget for any fixed finer ratio rho<a.
No cellwise analytic hypothesis remains; the cutoff precedes N. -/
theorem fixed_grid_productBoundary_integral_budget {ρ a ε : ℝ}
    (hρ : 1 < ρ) (hρa : ρ < a) (ha2 : a ≤ 2) (he : 0 < ε) (he2 : ε ≤ 2/15)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Real.log (N : ℝ)/(N : ℝ) *
        (400 * ∑ p ∈ productBoundary ρ N ε, goldbachG12NormalizedCoefficient N p.1) ≤
        (564383/1000000 : ℝ) * (3*(a-1)) *
          goldbachG12PrimeIntegral (fun _ => 1) + δ := by
  obtain ⟨N₁,hN₁,hb⟩ := productBoundary_integral_budget (hρ.trans hρa) ha2 he he2 δ hδ
  have hg := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4/53)).comp
    tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop (ρ/(a-ρ)))
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp hg
  refine ⟨max N₁ K,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN
  apply hb N ((le_max_left _ _).trans hN) ρ
  intro k _
  apply short_ratio_of_rounding hρ hρa.le
  have hh : ρ/(a-ρ) ≤ (lowCut N : ℝ) :=
    (hK N ((le_max_right _ _).trans hN)).trans (Nat.le_ceil _)
  have hh' := (div_le_iff₀ (sub_pos.mpr hρa)).mp hh
  simpa only [mul_comm] using hh'

end G12FineGrid
