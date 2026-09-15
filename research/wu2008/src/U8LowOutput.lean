import U8MeshPayment
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace U8Literal.Mesh

def lowRectangle (N : ℕ) (ρ : ℝ) (k : Key) (z : ℝ) : ℝ :=
  ∑ m ∈ OriginalU8.products (OriginalU8.labels N ρ k),
    ∑ n ∈ OriginalU8.primeSupport N ρ k,
      OriginalU8.alpha (OriginalU8.labels N ρ k) m * OriginalU8.beta N n *
        (if (output N n m : ℝ) < z then 1 else 0)

theorem lowRectangle_labels (N : ℕ) (ρ : ℝ) (k : Key) (z : ℝ) :
    lowRectangle N ρ k z =
      ∑ n ∈ shortPrimeSupport N ρ k, ∑ t ∈ longLabels N ρ k,
        rectangleBeta N n * (if (output N n (t.1*t.2) : ℝ) < z then 1 else 0) := by
  classical
  unfold lowRectangle
  simp only [← Join.longProducts_eq, ← Join.wholeInterval_eq, ← Join.longAlpha_eq,
    ← Join.beta_eq]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [long_sum N ρ k (fun m => rectangleBeta N n *
    (if (output N n m : ℝ) < z then 1 else 0))]
  apply sum_congr rfl
  intro m _
  exact mul_assoc _ _ _

theorem labels_le_lowRectangle {N : ℕ} {ρ : ℝ} {k : Key} {z : ℝ}
    (S : Finset Label)
    (hS : ∀ x ∈ S, x.1.1 ∈ shortPrimeSupport N ρ k ∧
      (x.1.2,x.2) ∈ longLabels N ρ k ∧ x.1.1.Prime ∧ x.1.1.Coprime N ∧
      (output N x.1.1 (x.1.2*x.2) : ℝ) < z) :
    (S.card : ℝ) ≤ lowRectangle N ρ k z := by
  classical
  rw [lowRectangle_labels]
  let f : Label → ℕ × (ℕ × ℕ) := fun x => (x.1.1,x.1.2,x.2)
  let W : ℕ × (ℕ × ℕ) → ℝ := fun t => rectangleBeta N t.1 *
    (if (output N t.1 (t.2.1*t.2.2) : ℝ) < z then 1 else 0)
  have hf : Function.Injective f := by
    intro x y h
    obtain ⟨⟨a,b⟩,c⟩ := x
    obtain ⟨⟨d,e⟩,g⟩ := y
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl,rfl⟩
    rfl
  have hsub : S.image f ⊆ shortPrimeSupport N ρ k ×ˢ longLabels N ρ k := by
    intro t ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    exact mem_product.mpr ⟨(hS x hx).1,(hS x hx).2.1⟩
  have hw : ∀ t, 0 ≤ W t := by
    intro t
    dsimp [W, rectangleBeta]
    split_ifs <;> norm_num
  calc
    (S.card : ℝ) = ∑ x ∈ S, W (f x) := by
      calc
        _ = ∑ _x ∈ S, (1 : ℝ) := by simp
        _ = _ := ?_
      apply sum_congr rfl
      intro x hx
      obtain ⟨_,_,hp,hc,hs⟩ := hS x hx
      dsimp only [W,f]
      rw [if_pos hs]
      unfold rectangleBeta
      rw [if_pos hc, if_pos hp]
      norm_num
    _ = ∑ t ∈ S.image f, W t := (sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ ∑ t ∈ shortPrimeSupport N ρ k ×ˢ longLabels N ρ k, W t :=
      sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hw t)
    _ = _ := by rw [sum_product]
theorem lowRectangle_bound {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hfib : ∀ (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (U V : Finset ℕ),
      ∀ r ≤ 4*N, (∑ p ∈ U ×ˢ V,
        if ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs = r then
          OriginalU8.alpha (OriginalU8.labels N ρ k) p.1 * OriginalU8.beta N p.2 else 0)
            ≤ 2*C₀*(5*(N : ℝ))^(1/4 : ℝ))
    {N : ℕ} (hN : 1 ≤ (N : ℝ)) (ρ : ℝ) (k : ℕ × ℕ × ℕ)
    {z : ℝ} (hz : 0 ≤ z) (hzu : z ≤ Real.sqrt (N : ℝ)) :
    lowRectangle N ρ k z ≤
      (4*C₀*(5 : ℝ)^(1/4 : ℝ))*(N : ℝ)^(1-(1/4 : ℝ)) := by
  have hN0 : 0 < (N : ℝ) := by linarith
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hN
  have hsN : Real.sqrt (N : ℝ) ≤ N := by
    rw [Real.sqrt_eq_rpow]
    simpa using Real.rpow_le_rpow_of_exponent_le hN (show (1/2 : ℝ) ≤ 1 by norm_num)
  have hceil : (⌈z⌉₊ : ℝ) ≤ 2*Real.sqrt (N : ℝ) := by
    linarith [Nat.ceil_lt_add_one hz]
  have hf := g9SmallOutput_fibre_sum
    ((OriginalU8.products (OriginalU8.labels N ρ k)) ×ˢ (OriginalU8.primeSupport N ρ k))
    (fun p => ((N : ℤ)-(p.1 : ℤ)*p.2).natAbs)
    (fun p => OriginalU8.alpha (OriginalU8.labels N ρ k) p.1 * OriginalU8.beta N p.2)
    z (2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) (by
      intro r hr
      apply hfib
      have hrz : (r : ℝ) < z := Nat.lt_ceil.mp (mem_range.mp hr)
      have hrN : (r : ℝ) ≤ 4*(N : ℝ) := by linarith
      exact_mod_cast hrN)
  rw [sum_product] at hf
  change lowRectangle N ρ k z ≤ _ at hf
  calc
    _ ≤ (⌈z⌉₊ : ℝ)*(2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) := hf
    _ ≤ (2*Real.sqrt (N : ℝ))*(2*C₀*(5*(N : ℝ))^(1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hceil (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hN0.le]
      calc
        _ = (4*C₀*(5 : ℝ)^(1/4 : ℝ))*((N : ℝ)^(1/2 : ℝ)*(N : ℝ)^(1/4 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hN0]; norm_num

/-- Noncoprimality really means a low prime output on the original atoms. -/
theorem familyBad_output_lt {N : ℕ} {e ρ : ℝ} {P : Key → Finset ℕ} {z : Key → ℝ}
    (hP : ∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime)
    (hcut : ∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k)
    {x : Label} (hx : x ∈ familyBad N e ρ P) :
    (output N x.1.1 (x.1.2*x.2)).Prime ∧
      (output N x.1.1 (x.1.2*x.2) : ℝ) < z (gridKey ρ x) := by
  classical
  obtain ⟨hpre,hbad⟩ := mem_filter.mp hx
  have hs := (mem_filter.mp hpre).1
  have hr : (output N x.1.1 (x.1.2*x.2)).Prime := by
    rw [output_eq_original hs]
    exact (physicalSmall_data hs).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hk : gridKey ρ x ∈ occupied N e ρ := mem_image_of_mem _ hpre
  refine ⟨hr, ?_⟩
  by_contra hz
  apply hbad
  rw [Nat.coprime_prod_right_iff]
  intro p hp
  change (output N x.1.1 (x.1.2*x.2)).Coprime p
  rw [Nat.coprime_comm, (hP _ hk p hp).coprime_iff_not_dvd]
  intro hd
  have he := (hr.dvd_iff_eq (hP _ hk p hp).ne_one).mp hd
  have hpcut := hcut _ hk p hp
  rw [he] at hz
  exact hz hpcut

/-- Per-cell bad labels embed positively; the cut may vary with the cell. -/
theorem familyBad_le_low {N : ℕ} (hN : 1 ≤ N) {e ρ Z : ℝ} (hρ : 1 < ρ)
    {P : Key → Finset ℕ} {z : Key → ℝ}
    (hP : ∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime)
    (hcut : ∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k)
    (hZ : ∀ k ∈ occupied N e ρ, z k ≤ Z) :
    ((familyBad N e ρ P).card : ℝ) ≤ ∑ k ∈ occupied N e ρ, lowRectangle N ρ k Z := by
  classical
  rw [← familyBad_partition N e ρ P]
  apply sum_le_sum
  intro k hk
  apply labels_le_lowRectangle
  intro x hx
  obtain ⟨hb,hkey⟩ := mem_filter.mp hx
  have hpre := (mem_filter.mp hb).1
  have hc : x ∈ cell N e ρ k := mem_filter.mpr ⟨hpre,hkey⟩
  obtain ⟨hn,hl⟩ := cell_rectangle hN hρ hc
  have hd := physicalSmall_data (mem_filter.mp hpre).1
  have hout := (familyBad_output_lt hP hcut hb).2
  rw [hkey] at hout
  exact ⟨hn,hl,hd.1,hd.2.2.2.1,hout.trans_le (hZ k hk)⟩

/-- Actual tau-three fibres pay the full original low-output mesh, uniformly in e and z. -/
theorem lowRectangle_total (A : ℕ) {ρ σ : ℝ} (hρ : 1 < ρ) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e z : ℝ,
      0 ≤ z → z ≤ Real.sqrt (N : ℝ) →
      (∑ k ∈ occupied N e ρ, lowRectangle N ρ k z) ≤ σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C₀,hC₀,hfib⟩ := OriginalU8.original_fibres (by norm_num : (0 : ℝ) < 1/4)
  let G : ℝ := (1/Real.log ρ+1)^3
  let B : ℝ := 4*C₀*(5 : ℝ)^(1/4 : ℝ)
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (g9Transport_eventually_envelope (G*B/σ) A (by norm_num : (0 : ℝ) < 1/4))
  refine ⟨M, ?_⟩
  intro N hN e z hz hzu
  obtain ⟨hN1,hlog,hpay⟩ := hM (N : ℝ) hN
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlogs : Real.log (N : ℝ)^3 ≤ Real.log (N : ℝ)^5 :=
    pow_le_pow_right₀ hlog (by norm_num)
  calc
    _ ≤ ∑ _k ∈ occupied N e ρ, B*(N : ℝ)^(1-(1/4 : ℝ)) := by
      apply sum_le_sum
      intro k _
      exact lowRectangle_bound hC₀ hfib hN1 ρ k hz hzu
    _ = ((occupied N e ρ).card : ℝ)*(B*(N : ℝ)^(1-(1/4 : ℝ))) := by simp
    _ ≤ (G*Real.log (N : ℝ)^3)*(B*(N : ℝ)^(1-(1/4 : ℝ))) :=
      mul_le_mul_of_nonneg_right (occupied_card_log hρ hlog) (by positivity)
    _ = (G*B)*(N : ℝ)^(1-(1/4 : ℝ))*Real.log (N : ℝ)^3 := by ring
    _ ≤ (G*B)*(N : ℝ)^(1-(1/4 : ℝ))*Real.log (N : ℝ)^5 :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = σ*((G*B/σ)*(N : ℝ)^(1-(1/4 : ℝ))*Real.log (N : ℝ)^5) := by
      field_simp [hσ.ne']
    _ ≤ σ*((N : ℝ)/Real.log (N : ℝ)^A) := mul_le_mul_of_nonneg_left hpay hσ.le
    _ = _ := by ring

/-- A legal uniform square-root upper cut pays all cell-dependent bad outputs. -/
theorem familyBad_paid (A : ℕ) {ρ σ : ℝ} (hρ : 1 < ρ) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : ℝ,
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∀ k ∈ occupied N e ρ, z k ≤ Real.sqrt (N : ℝ)) →
      ((familyBad N e ρ P).card : ℝ) ≤ σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨M,hM⟩ := lowRectangle_total A hρ hσ
  refine ⟨max M 1, ?_⟩
  intro N hN e P z hP hcut hZ
  have hn : 1 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  exact (familyBad_le_low hn hρ hP hcut hZ).trans
    (hM N ((le_max_left _ _).trans hN) e (Real.sqrt (N : ℝ)) (Real.sqrt_nonneg _) le_rfl)

/-- The only remaining loss is the original fixed-e smallPrefix. No atoms are removed. -/
theorem physicalSmall_lowPaid (A : ℕ) {e ε δ η ρ σ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∀ k ∈ occupied N e ρ, z k ≤ Real.sqrt (N : ℝ)) →
      ((physicalSmall N).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ, externalCenter N ρ δ η k (P k) (z k)) +
          σ*(N : ℝ)/Real.log (N : ℝ)^A + (smallPrefix N e).card := by
  have hhalf : 0 < σ/2 := by positivity
  obtain ⟨M,hM⟩ := physicalSmall_paid A he he1 hε hεa hεδ hδ hη hηu hρ hρu hhalf
  obtain ⟨B,hB⟩ := familyBad_paid A hρ hhalf
  refine ⟨max M B, ?_⟩
  intro N hN P z hP hPN hcut hZ
  have hs := hM N ((le_max_left _ _).trans hN) P z hP hPN hcut
  have hb := hB N ((le_max_right _ _).trans hN) e P z hP hcut hZ
  calc
    _ ≤ ((∑ k ∈ occupied N e ρ, externalCenter N ρ δ η k (P k) (z k)) +
        (σ/2)*(N : ℝ)/Real.log (N : ℝ)^A) +
          (σ/2)*(N : ℝ)/Real.log (N : ℝ)^A + (smallPrefix N e).card :=
      hs.trans (add_le_add (add_le_add le_rfl hb) le_rfl)
    _ = _ := by ring

end U8Literal.Mesh
