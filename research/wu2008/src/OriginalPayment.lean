import OriginalMajorant
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment

noncomputable section
open Finset Filter
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace OriginalU8

/-- Fixed-parameter, pointwise-rectangle exceptional payment. The threshold precedes
rho, every occupied rectangle, P, z and all actual external-family members.
No whole-mesh cardinality is absorbed, and no uniformity as eta tends to zero is claimed. -/
theorem exceptional_log_payment (A : ℕ) {e δ η σ : ℝ}
    (he : 0 < e) (hδ0 : 0 ≤ δ) (hδ : δ < 1/2)
    (hη : 0 < η) (hηu : η < 1/8) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k → ∀ P : Finset ℕ, ∀ z : ℝ,
      (∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
        |exceptional N ρ δ k P η z t|) ≤ σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,hrem⟩ := original_discrepancy_majorant (g9TransportMu_pos hδ hη)
  let B : ℝ := 16*Real.exp (8*(η⁻¹)^3)*C
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (g9Transport_eventually_envelope (B/σ) A (g9TransportMu_pos hδ hη))
  obtain ⟨Ng,hg⟩ := eventually_atTop.mp
    (g9Scale_eventually_const_mul_rpow_le 6 0 (100/1327) (by norm_num))
  obtain ⟨Nw,hw⟩ := g9WF_exists_internal_level_gate hδ0 hδ hη 0
  refine ⟨max M (max Ng Nw),?_⟩
  intro N hN ρ hρ hρu k hne P z
  have hNM : M ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNg : Ng ≤ (N : ℝ) := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNw : Nw ≤ (N : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨hN1,hlog,hpay⟩ := hM (N : ℝ) hNM
  have hNnat : 1 ≤ N := by exact_mod_cast hN1
  have hsix : 6 ≤ (N : ℝ)^(100/1327 : ℝ) := by simpa using hg N hNg
  obtain ⟨_,_,_,hlo,hhi⟩ := geometry he hρ hρu hne
  have hT : 1 ≤ (2/3 : ℝ)*ρ^k.1 := by linarith
  have hbig : 3 ≤ ρ^k.1 := by linarith
  obtain ⟨_,hQ,_,hD,hQN⟩ := hw N ((2/3 : ℝ)*ρ^k.1) hNw hT hhi
  change 1 ≤ level N ρ δ k at hQ
  change 2 ≤ externalInternalLevel (level N ρ δ k) η at hD
  change level N ρ δ k ≤ (N : ℝ) at hQN
  let H := C*(N : ℝ)^(1+g9TransportMu δ η)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hr : ∀ d ∈ Icc 1 ⌊level N ρ δ k⌋₊,
      |discrepancy N ρ k d| ≤ H/d.totient := by
    intro d hd
    obtain ⟨hd1,hdQ⟩ := mem_Icc.mp hd
    have hdN : d ≤ N := by
      exact_mod_cast ((Nat.le_floor_iff (zero_le_one.trans hQ)).mp hdQ).trans hQN
    exact hrem N hNnat e ρ he hρ hρu k hne hbig d (by omega) hdN
  have hex := exceptional_budget N ρ δ k P (z := z) hD hη hηu hH hr
  have hcard := (externalTags_card_and_wellFactorable true P z hD hη hηu).1.le
  have hfinite : (∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
      |exceptional N ρ δ k P η z t|) ≤
      Real.exp (8*(η⁻¹)^3)*H*(4/(externalInternalLevel (level N ρ δ k) η)^(η^2))*
        (1+Real.log (⌊level N ρ δ k⌋₊ : ℕ))^2 := by
    apply hex.trans
    gcongr
  have henv := g9Transport_one hN1 hlog hT hhi hδ0 hδ hη hηu hC.le
  change Real.exp (8*(η⁻¹)^3)*H*(4/(externalInternalLevel (level N ρ δ k) η)^(η^2))*
    (1+Real.log (⌊level N ρ δ k⌋₊ : ℕ))^2 ≤
      B*(N : ℝ)^(1-g9TransportMu δ η)*Real.log (N : ℝ)^2 at henv
  have hlogs : Real.log (N : ℝ)^2 ≤ Real.log (N : ℝ)^5 :=
    pow_le_pow_right₀ hlog (by norm_num)
  have hpaid : B*(N : ℝ)^(1-g9TransportMu δ η)*Real.log (N : ℝ)^5 ≤
      σ*(N : ℝ)/Real.log (N : ℝ)^A := by
    calc
      _ = σ*((B/σ)*(N : ℝ)^(1-g9TransportMu δ η)*Real.log (N : ℝ)^5) := by
        field_simp [hσ.ne']
      _ ≤ σ*((N : ℝ)/Real.log (N : ℝ)^A) := mul_le_mul_of_nonneg_left hpay hσ.le
      _ = _ := by ring
  exact (hfinite.trans henv).trans ((mul_le_mul_of_nonneg_left hlogs
    (by dsimp [B]; positivity)).trans hpaid)

/-- The signed non-primorial correction has now been paid, not discarded.
The C2 term is the existing pointwise-rectangle term; this is not a mesh sum. -/
theorem sieve_fixed_eta_exceptional_paid (A : ℕ) {e ε δ η σ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 100/1327)
    (hεδ : ε < δ) (hδ : δ < 1/2) (hη : 0 < η) (hηu : η < 1/8)
    (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ ρ : ℝ, 1 < ρ → ρ ≤ 5/4 → ∀ k : ℕ × ℕ × ℕ,
      Occupied N e ρ k → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p.Coprime N) →
      ∀ z : ℝ, (∀ p ∈ P, (p : ℝ) < z) →
      let D := externalInternalLevel (level N ρ δ k) η
      let S := externalTags true P D η z
      let x := 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1)
      sifted N ρ k P ≤
        (∑ t ∈ S, ∑ d ∈ (P.prod id).divisors,
          externalTerm true P D η z t d * center N ρ k d) +
        (S.card : ℝ)*(x/Real.log x^A) + σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨N₁,hS⟩ := sieve_fixed_eta A he he1 hε hεa hεδ hδ hη hηu
  obtain ⟨N₂,hE⟩ := exceptional_log_payment A he (hε.le.trans hεδ.le) hδ hη hηu hσ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ρ hρ hρu k hne P hP hPN z hcut
  have hs := hS N ((le_max_left _ _).trans hN) ρ hρ hρu k hne P hP hPN z hcut
  have hexc := hE N ((le_max_right _ _).trans hN) ρ hρ hρu k hne P z
  have hneg : -(∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
      exceptional N ρ δ k P η z t) ≤
      ∑ t ∈ externalTags true P (externalInternalLevel (level N ρ δ k) η) η z,
        |exceptional N ρ δ k P η z t| := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun t _ => neg_le_abs _
  dsimp only at hs ⊢
  linarith

end OriginalU8
