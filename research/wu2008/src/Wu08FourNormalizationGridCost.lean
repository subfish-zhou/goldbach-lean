import Wu08FirstPrimeFourGlobal
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour.Normalization

/-- Actual occupied keys, not the physical label count, cost only two logs. -/
theorem occupied_card_nat {N : ℕ} {e : Bool} {ξ ρ : ℝ} (hρ : 1 < ρ) :
    (occupied N e ξ ρ).card ≤ (fouvryG9GridIndex ρ N+1)^2 := by
  let I := range (fouvryG9GridIndex ρ N+1)
  have hsub : occupied N e ξ ρ ⊆ I ×ˢ I := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
    obtain ⟨_,ha,_,_,hm,_,hp⟩ := positive_data hx
    have haN : shortPart x ≤ N := (Nat.le_mul_of_pos_right _ hm).trans (by nlinarith only [hp])
    have hmN : longProduct (longPart x) ≤ N :=
      (Nat.le_mul_of_pos_right _ ha.pos).trans hp.le
    have hi := fouvryG9GridIndex_mono hρ (show (1 : ℝ) ≤ shortPart x by exact_mod_cast ha.one_le)
      (show (shortPart x : ℝ) ≤ N by exact_mod_cast haN)
    have hj := fouvryG9GridIndex_mono hρ (show (1 : ℝ) ≤ longProduct (longPart x) by exact_mod_cast hm)
      (show (longProduct (longPart x) : ℝ) ≤ N by exact_mod_cast hmN)
    simpa only [I,key,mem_product,mem_range,Nat.lt_succ_iff] using And.intro hi hj
  have hc := card_le_card hsub
  simpa only [I,card_product,card_range,pow_two] using hc

/-- Cubic harmless envelope to reuse the established logarithmic-payment algebra. -/
theorem occupied_card {N : ℕ} {e : Bool} {ξ ρ : ℝ}
    (hρ : 1 < ρ) (hl : 1 ≤ log (N : ℝ)) :
    ((occupied N e ξ ρ).card : ℝ) ≤ (1/log ρ+1)^3*log (N : ℝ)^3 := by
  have hr : 0 < log ρ := log_pos hρ
  have hf : (fouvryG9GridIndex ρ N : ℝ) ≤ log (N : ℝ)/log ρ :=
    Nat.floor_le (div_nonneg (by linarith) hr.le)
  have hh : (fouvryG9GridIndex ρ N : ℝ)+1 ≤ (1/log ρ+1)*log (N : ℝ) := by
    calc
      _ ≤ log (N : ℝ)/log ρ+log (N : ℝ) := add_le_add hf hl
      _ = _ := by ring
  have hc : ((occupied N e ξ ρ).card : ℝ) ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := by
    exact_mod_cast occupied_card_nat (N := N) (e := e) (ξ := ξ) hρ
  have hbase : 1 ≤ (fouvryG9GridIndex ρ N : ℝ)+1 := by have hh := Nat.cast_nonneg (α := ℝ) (fouvryG9GridIndex ρ N); linarith
  calc
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^2 := hc
    _ ≤ ((fouvryG9GridIndex ρ N : ℝ)+1)^3 := by
      have hh := mul_le_mul_of_nonneg_left hbase (sq_nonneg ((fouvryG9GridIndex ρ N : ℝ)+1))
      nlinarith only [hh]
    _ ≤ ((1/log ρ+1)*log (N : ℝ))^3 := pow_le_pow_left₀ (by positivity) hh 3
    _ = _ := by ring

/-- The literal tag-count C2 term in cellAmount is now paid over every box.
Threshold precedes both original families, P and z. -/
theorem tag_error_total (A : ℕ) {ξ ρ δ η : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool,
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∑ k ∈ occupied N e ξ ρ,
        ((externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k)).card : ℝ)*
        ((4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))/log (4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))^(A+4))) ≤
      (N : ℝ)/log (N : ℝ)^A := by
  let G : ℝ := (1/log ρ+1)^3
  let H : ℝ := exp (8*(η⁻¹)^3)
  let C : ℝ := H*(4*2^(A+4))
  let K : ℝ := 2/ξ
  have hK : 1 ≤ K := (le_div_iff₀ hξ).mpr (by linarith)
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ hδu hη 0
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp (g9Scale_eventually_const_mul_rpow_le 6 0
    truncatedSixthLowerAlpha (by norm_num [truncatedSixthLowerAlpha]))
  let L : ℝ := max 1 (max (2*log K) (G*C))
  refine ⟨max Nw (max Nb (exp L)),?_⟩
  intro N hN e P z
  have hnw := (le_max_left _ _).trans hN
  have hnb := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hnexp := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hn : 0 < (N : ℝ) := (exp_pos L).trans_le hnexp
  have hL : L ≤ log (N : ℝ) := (le_log_iff_exp_le hn).mpr hnexp
  have hl : 1 ≤ log (N : ℝ) := (le_max_left _ _).trans hL
  have hlarge : 2*log K ≤ log (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hGC : G*C ≤ log (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hsix : (6 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hnb
  have hlocal : ∀ k ∈ occupied N e ξ ρ,
      ((externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k)).card : ℝ)*
      ((4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))/log (4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))^(A+4)) ≤
      C*N/log (N : ℝ)^(A+4) := by
    intro k hk
    obtain ⟨_,hxlo,hxhi,hTlo,hThi⟩ := occupied_geometry hξ hρ hρu hk
    have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
    have hd := (hw N _ hnw hT hThi).2.2.2.1
    have hcard := (externalTags_card_and_wellFactorable true (P k) (z k) hd hη hηu).1.le
    let x := 4*ρ^k.2*((2/3 : ℝ)*ρ^k.1)
    have hx0 : 0 ≤ x/log x^(A+4) := div_nonneg (by dsimp [x]; positivity)
      (pow_nonneg (by have hh := (fouvryG9GridCost_log_window hK hn hlarge hxlo).2; linarith) _)
    have hone := fouvryG9GridCost_one A hK hn hl hlarge hxlo hxhi
      (show |x/log x^(A+4)| ≤ x/log x^(A+4) by rw [abs_of_nonneg hx0])
    rw [abs_of_nonneg hx0] at hone
    calc
      _ ≤ H*(x/log x^(A+4)) := mul_le_mul_of_nonneg_right hcard hx0
      _ ≤ H*((4*2^(A+4))*N/log (N : ℝ)^(A+4)) :=
        mul_le_mul_of_nonneg_left hone (exp_pos _).le
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ ∑ _k ∈ occupied N e ξ ρ, C*N/log (N : ℝ)^(A+4) := sum_le_sum hlocal
    _ = ((occupied N e ξ ρ).card : ℝ)*(C*N/log (N : ℝ)^(A+4)) := by simp
    _ ≤ (G*log (N : ℝ)^3)*(C*N/log (N : ℝ)^(A+4)) :=
      mul_le_mul_of_nonneg_right (occupied_card hρ hl) (by dsimp [C,H]; positivity)
    _ ≤ _ := fouvryG9GridCost_scalar A hn.le (by linarith) hGC

#print axioms occupied_card
#print axioms tag_error_total
end Wu08FirstPrimeFour.Normalization
