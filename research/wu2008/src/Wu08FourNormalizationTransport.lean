import Wu08FourNormalizationFibres
import Wu08FourNormalizationGridCost
import MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization

noncomputable section
open Finset Real Filter
open scoped Classical
open Wu2008DoubleSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace Wu08FirstPrimeFour.Normalization

/-- The actual SAME-member signed nonprimorial error is negligible even after
absolute values, for these new fibres. This is proved, not assumed as a
truncated Mobius-sum interface. The full coprime center is not changed. -/
theorem exceptional_total (A : ℕ) {ξ ρ δ η : ℝ}
    (hξ : 0 < ξ) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool,
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∑ k ∈ occupied N e ξ ρ,
        ∑ t ∈ externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k),
          |exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k)
            (level N ρ δ k) η (z k) t|) ≤ (N : ℝ)/log (N : ℝ)^A := by
  let μ := g9TransportMu δ η
  obtain ⟨C,hC,hrem⟩ := cell_remainder_majorant (g9TransportMu_pos hδu hη)
  let G : ℝ := (1/log ρ+1)^3
  let B : ℝ := 16*exp (8*(η⁻¹)^3)*C
  obtain ⟨Ne,he⟩ := eventually_atTop.mp (g9Transport_eventually_envelope (G*B) A
    (g9TransportMu_pos hδu hη))
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ hδu hη 0
  obtain ⟨Nb,hb⟩ := eventually_atTop.mp (g9Scale_eventually_const_mul_rpow_le 6 0
    truncatedSixthLowerAlpha (by norm_num [truncatedSixthLowerAlpha]))
  refine ⟨max Ne (max Nw Nb),?_⟩
  intro N hN e P z
  obtain ⟨hn,hl,hpay⟩ := he N ((le_max_left _ _).trans hN)
  have hnw := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hnb := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hsix : (6 : ℝ) ≤ (N : ℝ)^truncatedSixthLowerAlpha := by simpa using hb N hnb
  let H := C*(N : ℝ)^(1+μ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hlocal : ∀ k ∈ occupied N e ξ ρ,
      (∑ t ∈ externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k),
        |exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k)
          (level N ρ δ k) η (z k) t|) ≤ B*(N : ℝ)^(1-μ)*log (N : ℝ)^2 := by
    intro k hk
    obtain ⟨_,_,_,hTlo,hThi⟩ := occupied_geometry hξ hρ hρu hk
    have hbig : 3 ≤ ρ^k.1 := by nlinarith
    have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
    obtain ⟨_,hq,_,hd,hqn⟩ := hw N _ hnw hT hThi
    let Q := level N ρ δ k
    let D := externalInternalLevel Q η
    have hq0 : 0 ≤ Q := zero_le_one.trans hq
    have hr : ∀ d ∈ Icc 1 ⌊Q⌋₊,
        |bilinearDiscrepancy (products (longCell N e ξ ρ k)) (shortCell ρ k)
          (alpha (longCell N e ξ ρ k)) (beta N) N d| ≤ H/d.totient := by
      intro d hdmem
      obtain ⟨hd1,hdq⟩ := mem_Icc.mp hdmem
      have hdn : d ≤ N := by exact_mod_cast ((Nat.le_floor_iff hq0).mp hdq).trans hqn
      exact hrem N (by exact_mod_cast hn) e ξ ρ hρ hρu k hbig d (by omega) hdn
    have hex := externalUpperFamily_exceptional_remainder_budget (P k) (z k) hd hη hηu
      ⌊Q⌋₊ (bilinearDiscrepancy (products (longCell N e ξ ρ k)) (shortCell ρ k)
        (alpha (longCell N e ξ ρ k)) (beta N) N) H hH hr
    have hcard := (externalTags_card_and_wellFactorable true (P k) (z k) hd hη hηu).1.le
    change (∑ t ∈ externalTags true (P k) D η (z k),
      |exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k) Q η (z k) t|) ≤ _ at hex
    calc
      _ ≤ _ := hex
      _ ≤ exp (8*(η⁻¹)^3)*H*(4/D^(η^2))*(1+log (⌊Q⌋₊ : ℝ))^2 := by
        gcongr
        exact le_rfl
      _ ≤ _ := g9Transport_one hn hl hT hThi hδ hδu hη hηu hC.le
  calc
    _ ≤ ∑ _k ∈ occupied N e ξ ρ, B*(N : ℝ)^(1-μ)*log (N : ℝ)^2 := sum_le_sum hlocal
    _ = ((occupied N e ξ ρ).card : ℝ)*(B*(N : ℝ)^(1-μ)*log (N : ℝ)^2) := by simp
    _ ≤ (G*log (N : ℝ)^3)*(B*(N : ℝ)^(1-μ)*log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (occupied_card hρ hl) (by dsimp [B]; positivity)
    _ = (G*B)*(N : ℝ)^(1-μ)*log (N : ℝ)^5 := by ring
    _ ≤ _ := hpay

/-- The center is still evaluated at the FULL cofactor m*a. -/
def cellMain (N : ℕ) (e : Bool) (ξ ρ δ η z : ℝ) (P : Finset ℕ) (k : Key) : ℝ :=
  ∑ m ∈ products (longCell N e ξ ρ k), ∑ a ∈ shortCell ρ k,
    alpha (longCell N e ξ ρ k) m*beta N a*
      externalDensity true P (externalInternalLevel (level N ρ δ k) η) η z
        (progressionDensity (m*a))

/-- Same center plus signed complement, jointly bounded without any leading
constant loss. The signed complement has now actually been paid. -/
theorem cellAmount_total (A : ℕ) {ξ ρ δ η : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4)
    (hδ : 0 ≤ δ) (hδu : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : Bool,
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∑ k ∈ occupied N e ξ ρ, cellAmount N e ξ ρ δ η (z k) (A+5) (P k) k) ≤
        (∑ k ∈ occupied N e ξ ρ, cellMain N e ξ ρ δ η (z k) (P k) k)+
        (∑ k ∈ occupied N e ξ ρ, lowRectangle N (longCell N e ξ ρ k) (shortCell ρ k) (z k))+
        (N : ℝ)/log (N : ℝ)^A := by
  obtain ⟨Nt,ht⟩ := tag_error_total (A+1) hξ hξ1 hρ hρu hδ hδu hη hηu
  obtain ⟨Ne,he⟩ := exceptional_total (A+1) hξ hρ hρu hδ hδu hη hηu
  refine ⟨max Nt (max Ne (exp 2)),?_⟩
  intro N hN e P z
  have htag := ht N ((le_max_left _ _).trans hN) e P z
  have hex := he N ((le_max_left _ _).trans ((le_max_right _ _).trans hN)) e P z
  have hnl : exp 2 ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hl : 2 ≤ log (N : ℝ) := by simpa only [log_exp] using log_le_log (exp_pos 2) hnl
  have herr : (N : ℝ)/log (N : ℝ)^(A+1)+(N : ℝ)/log (N : ℝ)^(A+1) ≤
      (N : ℝ)/log (N : ℝ)^A := by
    have hp : 0 < log (N : ℝ) := by linarith
    apply (le_div_iff₀ (pow_pos hp A)).mpr
    rw [pow_succ]
    field_simp
    nlinarith
  have hpoint : ∀ k ∈ occupied N e ξ ρ,
      cellAmount N e ξ ρ δ η (z k) (A+5) (P k) k ≤
        cellMain N e ξ ρ δ η (z k) (P k) k +
        lowRectangle N (longCell N e ξ ρ k) (shortCell ρ k) (z k) +
        ((externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k)).card : ℝ)*
          ((4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))/log (4*ρ^k.2*((2/3 : ℝ)*ρ^k.1))^((A+1)+4)) +
        ∑ t ∈ externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k),
          |exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k)
            (level N ρ δ k) η (z k) t| := by
    intro k _
    unfold cellAmount cellMain
    dsimp only
    rw [g9IntegerFibreCenter_externalDensity]
    have hneg : -(∑ t ∈ externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k),
        exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k) (level N ρ δ k) η (z k) t) ≤
      ∑ t ∈ externalTags true (P k) (externalInternalLevel (level N ρ δ k) η) η (z k),
        |exceptional N (longCell N e ξ ρ k) (shortCell ρ k) (P k) (level N ρ δ k) η (z k) t| := by
      rw [← sum_neg_distrib]
      exact sum_le_sum (fun _ _ => neg_le_abs _)
    linarith only [hneg]
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib] at hs
  linarith only [hs,htag,hex,herr]

#print axioms exceptional_total
#print axioms cellAmount_total
end Wu08FirstPrimeFour.Normalization
