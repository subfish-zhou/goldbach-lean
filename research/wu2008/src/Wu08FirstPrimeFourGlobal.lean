import Wu08FirstPrimeFourGrid
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9ModulusSupport

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour

/-- One global cutoff precedes BOTH original families, the mesh, every occupied
box, and the full signed WF member at N^(5/9-delta)/T^(5/9). -/
theorem global_cell_C2 (j A : ℕ) {ξ ε δ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hε : 0 < ε)
    (hεa : ε < truncatedSixthLowerAlpha) (hεδ : ε < δ) (hδ : δ ≤ 1/2) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool, ∀ ρ : ℝ,
      1 < ρ → ρ ≤ 5/4 → ∀ k ∈ occupied N e ξ ρ, ∀ c : ℕ → ℝ,
      SignedWellFactorable j (level N ρ δ k) c →
      let x := 4*ρ^k.2*((2/3 : ℝ)*ρ^k.1)
      |signedError (products (longCell N e ξ ρ k)) (shortCell ρ k)
        (Ioc 0 ⌊level N ρ δ k⌋₊) (alpha (longCell N e ξ ρ k)) (beta N) c N| ≤ x/log x^A := by
  have hK : 1 ≤ 2/ξ := (le_div_iff₀ hξ).mpr (by linarith)
  have hK0 : 0 < 2/ξ := by positivity
  obtain ⟨Ns,hs⟩ := g9Scale_exists_threshold_local_global_and_level
    (2/ξ) ε truncatedSixthLowerAlpha δ hK hε hεa
    (by norm_num [truncatedSixthLowerAlpha]) hεδ
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  obtain ⟨xc,hc2⟩ := eventually_atTop.mp (rectangle_C2 j A hK hε)
  refine ⟨max (max Ns Nb) (max ((2/ξ)*xc) 1),?_⟩
  intro N hN e ρ hρ hρu k hk c hc
  have hNs := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNb := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNxc := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hM,hNx,hxN,hNT,hTN⟩ := occupied_geometry hξ hρ hρu hk
  let T := (2/3 : ℝ)*ρ^k.1
  let M := ρ^k.2
  let x := 4*M*T
  let ν := log T/log x
  obtain ⟨hx,hT,hid,hεν,hν,hNK,hlevel⟩ := hs N hNs x T hNx hxN hNT hTN
  have h6 : (6 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hNb
  have hbig : 3 ≤ ρ^k.1 := by nlinarith
  let J := cellInterval hρ hρu k hbig
  have hxc : xc ≤ x := le_of_mul_le_mul_left (hNxc.trans hNK) hK0
  have hglobal1 : 1 ≤ level N ρ δ k := g9Scale_global_level_ge_one hN1 hT hTN hδ
  have hlocal := hc.level_mono hglobal1 hlevel
  have hlocal1 : 1 ≤ x^((5-5*ν)/9-ε) := by
    apply Real.one_le_rpow hx.le
    have ha : truncatedSixthLowerAlpha < (1/10 : ℝ) := by norm_num [truncatedSixthLowerAlpha]
    linarith
  have hbound := hc2 x hxc J M ν hM rfl hεν hν hid N
    (by exact_mod_cast (show (0 : ℝ) < N by linarith)) hNK
    (longCell N e ξ ρ k)
    (fun t ht => longLabels_positive (mem_filter.mp ht).1)
    (fun t ht => longCell_bounds hρ hρu ht) c hlocal
  have heq := signedError_levels_eq_of_support (products (longCell N e ξ ρ k))
    (shortCell ρ k) (alpha (longCell N e ξ ρ k)) (beta N) c N
    (hc.factorSupported hglobal1) (hlocal.factorSupported hlocal1)
  dsimp only
  rw [heq]
  exact hbound

/-- A full finite cover of the ACTUAL small-prime family, not just a box API.
All multiplicity resides in the sigma fibre, and the fixed-xi prefix is retained. -/
theorem small_card_le_boxes {N : ℕ} (e : Bool) {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hbig : ∀ k ∈ occupied N e ξ ρ, 3 ≤ ρ^k.1) :
    (small N e).card ≤ (smallPrefix N e ξ).card+
      ∑ k ∈ occupied N e ξ ρ, (box N e (longCell N e ξ ρ k) (shortCell ρ k)).card := by
  let f : Physical → Σ _ : Key, Physical := fun x => ⟨key ρ x,x⟩
  have hf : Set.MapsTo f (positivePart N e ξ)
      ((occupied N e ξ ρ).sigma fun k => box N e (longCell N e ξ ρ k) (shortCell ρ k)) := by
    intro x hx
    have hk : key ρ x ∈ occupied N e ξ ρ := mem_image_of_mem _ hx
    exact mem_sigma.mpr ⟨hk,positive_mem_box hρ hρu hx (hbig _ hk)⟩
  have hi : Set.InjOn f (positivePart N e ξ) := by
    intro x _ y _ he
    exact congrArg (fun p : Σ _ : Key, Physical => p.2) he
  have hcard := card_le_card_of_injOn f hf hi
  rw [card_sigma] at hcard
  have hs := small_card_smallPrefix N e ξ
  omega

/-- Explicit amount, not a hypothesized asymptotic coefficient. -/
def cellAmount (N : ℕ) (e : Bool) (ξ ρ δ η z : ℝ) (A : ℕ)
    (P : Finset ℕ) (k : Key) : ℝ :=
  let L := longCell N e ξ ρ k
  let V := shortCell ρ k
  let Q := level N ρ δ k
  let D := externalInternalLevel Q η
  let S := externalTags true P D η z
  let x := 4*ρ^k.2*((2/3 : ℝ)*ρ^k.1)
  (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
    externalTerm true P D η z t d*g9IntegerFibreCenter (products L) V (alpha L) (beta N) d) +
  (S.card : ℝ)*(x/log x^A) - (∑ t ∈ S, exceptional N L V P Q η z t) + lowRectangle N L V z

/-- Original physical small-prime count at the genuinely improved GLOBAL level.
The unresolved center/exceptional/low/prefix costs are displayed, never zeroed. -/
theorem small_global_level_upper (A : ℕ) {ξ ε δ η : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hε : 0 < ε)
    (hεa : ε < truncatedSixthLowerAlpha) (hεδ : ε < δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool, ∀ ρ : ℝ,
      1 < ρ → ρ ≤ 5/4 → ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ξ ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ occupied N e ξ ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ occupied N e ξ ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      ((small N e).card : ℝ) ≤ (smallPrefix N e ξ).card+
        ∑ k ∈ occupied N e ξ ρ, cellAmount N e ξ ρ δ η (z k) A (P k) k := by
  obtain ⟨Nc,hc⟩ := global_cell_C2 1 A hξ hξ1 hε hεa hεδ hδ.le
  obtain ⟨Ng,hg⟩ := g9WF_exists_internal_level_gate (hε.le.trans hεδ.le) hδ hη 2
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 truncatedSixthLowerAlpha
      (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨max Nc (max Ng Nb),?_⟩
  intro N hN e ρ hρ hρu P z hP hPN hcut
  have hNc := (le_max_left _ _).trans hN
  have hNg := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have h6 : (6 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hNb
  have hgeom : ∀ k ∈ occupied N e ξ ρ, 3 ≤ ρ^k.1 ∧
      1 ≤ level N ρ δ k ∧ 2 ≤ externalInternalLevel (level N ρ δ k) η := by
    intro k hk
    obtain ⟨_,_,_,hNT,hTN⟩ := occupied_geometry hξ hρ hρu hk
    have hbig : 3 ≤ ρ^k.1 := by nlinarith
    have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
    have hh := hg N ((2/3 : ℝ)*ρ^k.1) hNg hT hTN
    exact ⟨hbig,hh.2.1,hh.2.2.2.1⟩
  have hfinite := small_card_le_boxes e hρ hρu (fun k hk => (hgeom k hk).1)
  have hfiniteR : ((small N e).card : ℝ) ≤ (smallPrefix N e ξ).card+
      ∑ k ∈ occupied N e ξ ρ, ((box N e (longCell N e ξ ρ k) (shortCell ρ k)).card : ℝ) := by
    exact_mod_cast hfinite
  apply hfiniteR.trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro k hk
  let L := longCell N e ξ ρ k
  let V := shortCell ρ k
  let Q := level N ρ δ k
  let D := externalInternalLevel Q η
  let S := externalTags true (P k) D η (z k)
  let x := 4*ρ^k.2*((2/3 : ℝ)*ρ^k.1)
  have hQ : 0 ≤ Q := (hgeom k hk).2.1.trans' (by norm_num)
  have hD := (hgeom k hk).2.2
  have hu := box_weighted_upper N e L V (P k) (hP k hk) hD hη hηu (hcut k hk)
  have he : (∑ t ∈ S, ∑ d ∈ ((P k).prod id).divisors,
      externalTerm true (P k) D η (z k) t d*bilinearDiscrepancy (products L) V (alpha L) (beta N) N d) ≤
      (S.card : ℝ)*(x/log x^A) - ∑ t ∈ S, exceptional N L V (P k) Q η (z k) t := by
    calc
      _ = ∑ t ∈ S,
          (signedError (products L) V (Ioc 0 ⌊Q⌋₊) (alpha L) (beta N)
            (fun d => externalTerm true (P k) D η (z k) t d) N - exceptional N L V (P k) Q η (z k) t) := by
        apply sum_congr rfl
        intro t ht
        exact primorial_error_eq N L V (P k) (hP k hk) (hPN k hk) hQ hD hη hηu t ht
      _ ≤ ∑ t ∈ S, (x/log x^A-exceptional N L V (P k) Q η (z k) t) := by
        apply sum_le_sum
        intro t ht
        apply sub_le_sub_right
        exact (le_abs_self _).trans (hc N hNc e ρ hρ hρu k hk _
          (externalTerm_signedWellFactorable true (P k) (z k) t hQ hD hη hηu ht))
      _ = _ := by rw [sum_sub_distrib]; simp only [sum_const,nsmul_eq_mul]
  change ((box N e L V).card : ℝ) ≤ _
  unfold cellAmount
  dsimp only
  linarith only [hu,he]

#print axioms global_cell_C2
#print axioms small_global_level_upper
end Wu08FirstPrimeFour
