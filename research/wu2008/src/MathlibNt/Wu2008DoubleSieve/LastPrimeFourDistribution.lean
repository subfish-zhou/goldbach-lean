import MathlibNt.Wu2008DoubleSieve.LastPrimeFourMultiplicity
import MathlibNt.Wu2008DoubleSieve.LastPrimeFourPhysicalMap

/-! The actual two last-prime families consume one common generic BV threshold.
Absolute values are outside the full signed label sum; only the fixed number
of complete cofactor layers is paid. -/
namespace Wu2008DoubleSieve.LastPrimeFour
open Finset Real
open scoped Classical

noncomputable def signedR1 (N : ℕ) (e : Bool) (D : ℕ) (Z : ℝ) : ℝ :=
  ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ)^q.primeFactors.card *
    |∑ t ∈ (labels N e).filter (fun t => (cofactor t).Coprime q),
      omega3ProfileError N q (cofactor t) (lower N e t) (upper N e t)|

theorem signedR1_eq (N : ℕ) (e : Bool) (D : ℕ) (Z : ℝ) :
    signedR1 N e D Z = (family N e).R1 D Z := by
  change _ = ∑ q ∈ omega3SieveModuli N D Z, (3 : ℝ)^q.primeFactors.card *
    |∑ t ∈ (labels N e).filter (fun t => (cofactor t).Coprime q),
      1 * omega3ProfileError N q (cofactor t) (lower N e t) (upper N e t)|
  simp only [one_mul, signedR1]

/-- Every complete layer has an actual BV proof. The cutoff is chosen before
N, family choice, layer, support, and endpoints; empty layers are included. -/
theorem actual_layers_distribution (A : ℝ) {δ : ℝ} (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ e : Bool, ∀ j : ℕ, ∀ Z : ℝ,
      (family N e).layerR1 (0,0,0,0) j (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤
        C*N / log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT,hd⟩ := omega3_balanced_interval_distribution A
    truncatedSixthLowerAlpha 1 hA (by norm_num [truncatedSixthLowerAlpha])
    (by norm_num) hδ
  refine ⟨C,hC,T,hT,?_⟩
  intro N hN e j Z
  let L := family N e
  apply hd N hN (L.layerSupport j)
    (fun m => L.weight (L.layerLabel (0,0,0,0) j m))
    (fun m => L.lower (L.layerLabel (0,0,0,0) j m))
    (fun m => L.upper (L.layerLabel (0,0,0,0) j m))
  · intro m hm
    have ht := L.layerLabel_mem (0,0,0,0) hm
    have hg := label_balanced (by omega : 1 < N) ht.1
    change (N : ℝ)^truncatedSixthLowerAlpha ≤ L.cofactor _ ∧
      (L.cofactor _ : ℝ) ≤ (N : ℝ)^(1-truncatedSixthLowerAlpha) at hg
    simpa only [ht.2] using hg
  · intro m _
    norm_num [L, family]
  · intro m hm
    have ht := L.layerLabel_mem (0,0,0,0) hm
    have hg := (L.geometry _ ht.1).2
    simpa only [ht.2] using hg

/-- Full aggregate BV for both literal original families. K is fixed once and
for all, and the analytic constant is explicitly (K+1) times the layer constant. -/
theorem both_signed_aggregate_distribution (A : ℝ) {δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ e : Bool, ∀ Z : ℝ,
      signedR1 N e (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤
        (((layerBound : ℝ)+1)*C₀)*N / log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT,hd⟩ := actual_layers_distribution A hA hδ
  refine ⟨C,hC,T,hT,?_⟩
  intro N hN e Z
  rw [signedR1_eq]
  have hs := ((family N e).R1_le_layers (0,0,0,0) layerBound
    (fibre_card_le (by omega) e) _ Z).trans
      (sum_le_sum (fun j _ => hd N hN e j Z))
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ ≤ (layerBound : ℝ)*(C*N/log (N : ℝ)^A) := hs
    _ ≤ ((layerBound : ℝ)+1)*(C*N/log (N : ℝ)^A) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- The advertised two-family endpoint with one C and one T, not a threshold
or N-sized loss chosen separately for each original prime label. -/
theorem physical10_physical11_signed_BV (A : ℝ) {δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Z : ℝ,
      signedR1 N false (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N/log (N : ℝ)^A ∧
      signedR1 N true (⌊(N : ℝ)^(1/2-δ)⌋₊+1) Z ≤ C*N/log (N : ℝ)^A := by
  obtain ⟨C,hC,T,hT,hd⟩ := both_signed_aggregate_distribution A hA hδ
  exact ⟨((layerBound : ℝ)+1)*C,by positivity,T,hT,
    fun N hN Z => ⟨hd N hN false Z,hd N hN true Z⟩⟩

end Wu2008DoubleSieve.LastPrimeFour
