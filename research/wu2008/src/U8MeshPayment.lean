import U8MeshFamily

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace U8Literal.Mesh

/-- The actual external centers, without a density/asymptotic replacement. -/
def externalCenter (N : ℕ) (ρ δ η : ℝ) (k : Key) (P : Finset ℕ) (z : ℝ) : ℝ :=
  ∑ t ∈ externalTags true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z,
    ∑ d ∈ (P.prod id).divisors,
      externalTerm true P (externalInternalLevel (OriginalU8.level N ρ δ k) η) η z t d *
        OriginalU8.center N ρ k d

/-- Both C2 and signed exceptional costs are paid on the original occupied mesh.
The loss of three logarithms is proved, and rho is fixed before the threshold.
The per-cell prime sets and cutoffs are arbitrary after the threshold. -/
theorem rectangles_paid (A : ℕ) {e ε δ η ρ σ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      (∑ k ∈ occupied N e ρ, OriginalU8.sifted N ρ k (P k)) ≤
        (∑ k ∈ occupied N e ρ, externalCenter N ρ δ η k (P k) (z k)) +
          σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  let c : ℝ := 4*2^(A+4)
  let C : ℝ := Real.exp (8*(η⁻¹)^3)*c+1
  let K : ℝ := 2/e
  have hK : 1 ≤ K := by dsimp [K]; apply (le_div_iff₀ he).mpr; linarith
  obtain ⟨Ns,hs⟩ := OriginalU8.sieve_fixed_eta_exceptional_paid (A+4)
    he he1 hε hεa hεδ hδ hη hηu (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Np,hp⟩ := OriginalU8.parameters he he1 hε hεa hεδ hδ.le
  obtain ⟨Ng,hg⟩ := g9WF_exists_internal_level_gate (hε.le.trans hεδ.le) hδ hη 0
  obtain ⟨Nm,hm⟩ := mesh_log_payment A hρ (show 0 ≤ C by dsimp [C,c]; positivity) hσ
  let L := max 1 (2*Real.log K)
  refine ⟨max Ns (max Np (max Ng (max Nm (Real.exp L)))), ?_⟩
  intro N hN P z hP hPN hcut
  have hNs := (le_max_left _ _).trans hN
  have hrest := (le_max_right _ _).trans hN
  have hNp := (le_max_left _ _).trans hrest
  have hrest₂ := (le_max_right _ _).trans hrest
  have hNg := (le_max_left _ _).trans hrest₂
  have hrest₃ := (le_max_right _ _).trans hrest₂
  have hNm := (le_max_left _ _).trans hrest₃
  have hNe : Real.exp L ≤ (N : ℝ) := (le_max_right _ _).trans hrest₃
  have hn : 0 < (N : ℝ) := (Real.exp_pos L).trans_le hNe
  have hL : L ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).mpr hNe
  have hlog : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hlarge : 2*Real.log K ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL
  have hn1 : 1 ≤ N := by
    exact_mod_cast (Real.one_le_exp (zero_le_one.trans (le_max_left _ _))).trans hNe
  have hlocal : ∀ k ∈ occupied N e ρ,
      OriginalU8.sifted N ρ k (P k) - externalCenter N ρ δ η k (P k) (z k) ≤
        C*(N : ℝ)/Real.log (N : ℝ)^(A+4) := by
    intro k hk
    have ho := Join.occupied_to_original hn1 hρ hk
    have hgeom := OriginalU8.geometry he hρ hρu ho
    have hparams := hp N hNp ρ hρ hρu k ho
    obtain ⟨_,_,_,hD,_⟩ := hg N ((2/3 : ℝ)*ρ^k.1) hNg hparams.2.2.1 hgeom.2.2.2.2
    change 2 ≤ externalInternalLevel (OriginalU8.level N ρ δ k) η at hD
    let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
    have hxlo : (N : ℝ)/K ≤ x := hgeom.2.1
    have hxhi : x ≤ 4*N := hgeom.2.2.1
    obtain ⟨hx0,hxl⟩ := fouvryG9GridCost_log_window hK hn hlarge hxlo
    have hxl0 : 0 < Real.log x := by linarith
    have hxq : 0 ≤ x/Real.log x^(A+4) := by positivity
    have hpoint := fouvryG9GridCost_one A hK hn hlog hlarge hxlo hxhi
      (E := x/Real.log x^(A+4)) (by rw [abs_of_nonneg hxq])
    rw [abs_of_nonneg hxq] at hpoint
    have htags := (externalTags_card_and_wellFactorable true (P k) (z k) hD hη hηu).1.le
    have hcost := mul_le_mul htags hpoint hxq (Real.exp_pos _).le
    have hpaid := hs N hNs ρ hρ hρu k ho (P k) (hP k hk) (hPN k hk) (z k) (hcut k hk)
    change OriginalU8.sifted N ρ k (P k) ≤ externalCenter N ρ δ η k (P k) (z k) +
      ((externalTags true (P k) (externalInternalLevel (OriginalU8.level N ρ δ k) η) η (z k)).card : ℝ)*
        (x/Real.log x^(A+4)) + 1*(N : ℝ)/Real.log (N : ℝ)^(A+4) at hpaid
    have heq : Real.exp (8*(η⁻¹)^3)*(c*(N : ℝ)/Real.log (N : ℝ)^(A+4)) +
        (N : ℝ)/Real.log (N : ℝ)^(A+4) = C*(N : ℝ)/Real.log (N : ℝ)^(A+4) := by
      dsimp [C]; ring
    change _ ≤ Real.exp (8*(η⁻¹)^3)*(c*(N : ℝ)/Real.log (N : ℝ)^(A+4)) at hcost
    apply (sub_le_iff_le_add).mpr
    calc
      _ ≤ externalCenter N ρ δ η k (P k) (z k) +
          Real.exp (8*(η⁻¹)^3)*(c*(N : ℝ)/Real.log (N : ℝ)^(A+4)) +
            1*(N : ℝ)/Real.log (N : ℝ)^(A+4) :=
        hpaid.trans (add_le_add (add_le_add le_rfl hcost) le_rfl)
      _ = _ := by rw [one_mul, add_assoc, heq, add_comm]
  have hsum := hm N hNm e
    (fun k => OriginalU8.sifted N ρ k (P k)-externalCenter N ρ δ η k (P k) (z k)) hlocal
  rw [sum_sub_distrib] at hsum
  linarith

/-- Full original physical small segment. Only outputBad and the fixed-e smallPrefix
remain unpaid; C2 and exceptional are no longer premises or residual summands. -/
theorem physicalSmall_paid (A : ℕ) {e ε δ η ρ σ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ P : Key → Finset ℕ, ∀ z : Key → ℝ,
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Prime) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, p.Coprime N) →
      (∀ k ∈ occupied N e ρ, ∀ p ∈ P k, (p : ℝ) < z k) →
      ((physicalSmall N).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ, externalCenter N ρ δ η k (P k) (z k)) +
          σ*(N : ℝ)/Real.log (N : ℝ)^A +
            (familyBad N e ρ P).card + (smallPrefix N e).card := by
  obtain ⟨M,hM⟩ := rectangles_paid A he he1 hε hεa hεδ hδ hη hηu hρ hρu hσ
  refine ⟨max M 1, ?_⟩
  intro N hN P z hP hPN hcut
  have hn : 1 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
  exact (physicalSmall_family hn e hρ P).trans
    (add_le_add (add_le_add (hM N ((le_max_left _ _).trans hN) P z hP hPN hcut) le_rfl) le_rfl)

end U8Literal.Mesh
