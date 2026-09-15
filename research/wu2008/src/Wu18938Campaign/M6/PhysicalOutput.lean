import Wu18938Campaign.M6.EighthEndpoint
import Wu18938Campaign.M6.LowOutputPayment

noncomputable section
open Finset
open scoped Classical

namespace Wu18938Campaign.M6
open U8Literal

theorem physicalSmall_output_inj (N : ℕ) :
    Set.InjOn (fun x : Label => output N x.1.1 (x.1.2 * x.2)) (physicalSmall N) := by
  rintro ⟨⟨a, b⟩, c⟩ hx ⟨⟨d, e⟩, f⟩ hy h
  obtain ⟨ha, hb, hc, _, _, _, _, _, hab, hbc, _, _, hprod, _⟩ := physicalSmall_data hx
  obtain ⟨hd, he, hf, _, _, _, _, _, hde, hef, _, _, hprod', _⟩ := physicalSmall_data hy
  change output N a (b * c) = output N d (e * f) at h
  rw [output_eq_original hx, output_eq_original hy] at h
  have hp : a * b * c = d * e * f := by
    change a * b * c < N at hprod
    change d * e * f < N at hprod'
    change N - a * b * c = N - d * e * f at h
    omega
  obtain ⟨rfl, rfl, rfl⟩ := ordered_prime_triple_unique ha hb hc hd he hf
    hab.le hbc hde.le hef hp
  rfl

theorem outputBad_card_le (N : ℕ) (e : ℝ) (P : Finset ℕ) (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hcut : ∀ p ∈ P, (p : ℝ) < z) :
    (outputBad N e P).card ≤ ⌈z⌉₊ := by
  have hb : (outputBad N e P).card ≤ (range ⌈z⌉₊).card := by
    apply card_le_card_of_injOn (fun x : Label => output N x.1.1 (x.1.2 * x.2))
    · intro x hx
      exact mem_range.mpr (Nat.lt_ceil.mpr
        (prime_output_lt_cut (outputBad_prime hx) hP hcut (mem_filter.mp hx).2))
    · intro x hx y hy h
      exact physicalSmall_output_inj N (mem_filter.mp (mem_filter.mp hx).1).1
        (mem_filter.mp (mem_filter.mp hy).1).1 h
  simpa only [card_range] using hb

theorem outputBad_log_paid (A : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ e : ℝ, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) < Real.sqrt N) →
      ((outputBad N e P).card : ℝ) ≤ σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨N₀, hN₀, hpay⟩ := sqrt_error_log_payment A hσ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN e P hP hcut
  have hc : ((outputBad N e P).card : ℝ) ≤ (⌈Real.sqrt N⌉₊ : ℝ) := by
    exact_mod_cast outputBad_card_le N e P (Real.sqrt N) hP hcut
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg (N : ℝ))
  have hs := Real.sqrt_nonneg (N : ℝ)
  have herr := hpay N hN
  linarith

theorem physicalPrefix_le_rectangles_paid_output (A : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ e ρ : ℝ, 1 < ρ →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, (p : ℝ) < Real.sqrt N) →
      ((physicalPrefix N e).card : ℝ) ≤
        (∑ k ∈ occupied N e ρ, rectangleSifted N ρ k P) +
          σ * (N : ℝ) / (Real.log N) ^ A := by
  obtain ⟨N₀, hN₀, hpay⟩ := outputBad_log_paid A hσ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN e ρ hρ P hP hcut
  exact (physicalPrefix_le_rectangles_add_outputBad (by omega) e hρ P).trans
    (add_le_add le_rfl (hpay N hN e P hP hcut))

end Wu18938Campaign.M6
