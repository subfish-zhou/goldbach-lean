import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantActual
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment
import MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization
import MathlibNt.SieveTheory.LiLiuFouvryG9ExternalError

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal normalized external-density main term for one occupied rectangle. -/
def fouvryG9RectangleMain (N : ℕ) (ρ δ η : ℝ) (k : ℕ × ℕ × ℕ)
    (P : Finset ℕ) (z : ℝ) : ℝ :=
  let D := externalInternalLevel ((N : ℝ)^(5/9-δ)/
    (((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) η
  ∑ m ∈ fouvryG9LongProducts N ρ k, ∑ n ∈ fouvryG9RectanglePrimeSupport N ρ k,
    fouvryG9LongAlpha N ρ k m*fouvryG9RectangleBeta N n*
      externalDensity true P D η z (progressionDensity (m*n))

/-- Actual upper sieving on the entire occupied grid, with all distribution and
exceptional-transport costs paid. No weight, discrepancy, or mass bound is an
input. The displayed main term is an exact density expression, not yet its
analytic asymptotic evaluation. Prime carriers and cutoffs follow the threshold. -/
theorem fouvryG9Sieve_total (A : ℕ) {e ε δ η ρ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ P : (ℕ × ℕ × ℕ) → Finset ℕ, ∀ z : (ℕ × ℕ × ℕ) → ℝ,
      (∀ k ∈ fouvryG9GridUsed N e ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ fouvryG9GridUsed N e ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ fouvryG9GridUsed N e ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9RectangleSifted N ρ k (P k)) ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ, fouvryG9RectangleMain N ρ δ η k (P k) (z k)) +
          (N : ℝ)/Real.log (N : ℝ)^A := by
  have hδ0 : 0 ≤ δ := hε.le.trans hεδ.le
  obtain ⟨C,hC,hrem⟩ := fouvryG9RemainderMajorant_actual (g9TransportMu_pos hδ hη)
  obtain ⟨Nc,hc⟩ := fouvryG9ExternalError_total (A+1) he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨Nt,ht⟩ := g9Transport_grid_log_payment δ η ρ C (A+1) hδ0 hδ hη hηu hρ hC
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ0 hδ hη 0
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (4/53) (by norm_num))
  refine ⟨max Nc (max (Nt : ℝ) (max Nw (max Ng (Real.exp 2)))), ?_⟩
  intro N hN P z hP hPN hcut
  have hNc : Nc ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNt : Nt ≤ N := by exact_mod_cast (le_max_left _ _).trans hrest
  have hrest2 := (le_max_right _ _).trans hrest
  have hNw : Nw ≤ (N : ℝ) := (le_max_left _ _).trans hrest2
  have hrest3 := (le_max_right _ _).trans hrest2
  have hNg : Ng ≤ (N : ℝ) := (le_max_left _ _).trans hrest3
  have hNe : Real.exp 2 ≤ (N : ℝ) := (le_max_right _ _).trans hrest3
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)).trans hNe
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hlog : 2 ≤ Real.log (N : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 2) hNe
  have hsix : 6 ≤ (N : ℝ)^(4/53 : ℝ) := by simpa using hg N hNg
  let I := fouvryG9GridUsed N e ρ
  let T := fun k : ℕ × ℕ × ℕ => (2/3 : ℝ)*ρ^k.1
  let Q := fun k => (N : ℝ)^(5/9-δ)/(T k)^(5/9 : ℝ)
  let D := fun k => externalInternalLevel (Q k) η
  let H := C*(N : ℝ)^(1+g9TransportMu δ η)
  let E := fun k => ∑ t ∈ externalTags true (P k) (D k) η (z k),
    |fouvryG9RectangleError N ρ δ k (fun d => externalTerm true (P k) (D k) η (z k) t d)|
  let R := fun k => Real.exp (8*(η⁻¹)^3)*H*(4/(D k)^(η^2))*
    (1+Real.log (⌊Q k⌋₊ : ℝ))^2
  have hgeom : ∀ k ∈ I, 1 ≤ T k ∧ T k ≤ (N : ℝ)^(1/10 : ℝ) ∧ 3 ≤ ρ^k.1 := by
    intro k hk
    obtain ⟨_,_,_,hlo,hhi⟩ := fouvryG9Grid_buffered_geometry he hρ hρu
      (fouvryG9GridCell_nonempty_iff.mpr hk)
    dsimp [T]
    exact ⟨by linarith, hhi, by linarith⟩
  have hlevel : ∀ k ∈ I, 1 ≤ Q k ∧ 2 ≤ D k ∧ Q k ≤ (N : ℝ) := by
    intro k hk
    obtain ⟨_,hq,_,hd,hqn⟩ := hw N (T k) hNw (hgeom k hk).1 (hgeom k hk).2.1
    exact ⟨hq,hd,hqn⟩
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpoint : ∀ k ∈ I, fouvryG9RectangleSifted N ρ k (P k) ≤
      fouvryG9RectangleMain N ρ δ η k (P k) (z k)+E k+R k := by
    intro k hk
    obtain ⟨hq,hd,hqn⟩ := hlevel k hk
    have hq0 : 0 ≤ Q k := zero_le_one.trans hq
    have hd0 : 0 ≤ D k := (by norm_num : (0 : ℝ) ≤ 2).trans hd
    have hr : ∀ d ∈ Icc 1 ⌊Q k⌋₊,
        |bilinearDiscrepancy (fouvryG9LongProducts N ρ k) (fouvryG9RectanglePrimeSupport N ρ k)
          (fouvryG9LongAlpha N ρ k) (fouvryG9RectangleBeta N) N d| ≤ H/d.totient := by
      intro d hdm
      obtain ⟨hd1,hdq⟩ := mem_Icc.mp hdm
      have hdn : d ≤ N := by exact_mod_cast ((Nat.le_floor_iff hq0).mp hdq).trans hqn
      exact hrem N hNnat e ρ he hρ hρu k
        (fouvryG9GridCell_nonempty_iff.mpr hk) (hgeom k hk).2.2 d (by omega) hdn
    have hu := fouvryG9Rectangle_upper_transport N ρ k (P k) (hP k hk) (hPN k hk)
      hq0 hd hη hηu (hcut k hk) hH hr
    dsimp only at hu
    rw [g9IntegerFibreCenter_externalDensity] at hu
    change fouvryG9RectangleSifted N ρ k (P k) ≤
      fouvryG9RectangleMain N ρ δ η k (P k) (z k)+E k+
        ((externalTags true (P k) (D k) η (z k)).card : ℝ)*H*
          (4/(D k)^(η^2))*(1+Real.log (⌊Q k⌋₊ : ℝ))^2 at hu
    have hcard := (externalTags_card_and_wellFactorable true (P k) (z k) hd hη hηu).1.le
    have hcost : ((externalTags true (P k) (D k) η (z k)).card : ℝ)*H*
        (4/(D k)^(η^2))*(1+Real.log (⌊Q k⌋₊ : ℝ))^2 ≤ R k := by
      dsimp [R]
      gcongr
    exact hu.trans (add_le_add le_rfl hcost)
  have hE : (∑ k ∈ I, E k) ≤ (N : ℝ)/Real.log (N : ℝ)^(A+1) := hc N hNc P z
  have hR : (∑ k ∈ I, R k) ≤ (N : ℝ)/Real.log (N : ℝ)^(A+1) :=
    ht N hNt e T (fun k hk => ⟨(hgeom k hk).1,(hgeom k hk).2.1⟩)
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib] at hsum
  have hpay : (N : ℝ)/Real.log (N : ℝ)^(A+1)+(N : ℝ)/Real.log (N : ℝ)^(A+1) ≤
      (N : ℝ)/Real.log (N : ℝ)^A := by
    have hl0 : 0 < Real.log (N : ℝ) := by linarith
    apply (le_div_iff₀ (pow_pos hl0 A)).2
    rw [pow_succ]
    field_simp
    nlinarith
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
