import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CanonicalBinomialIdentities
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ReciprocalIntegralParameters

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Canonical first-chart functions retain the same selector unit and reciprocal parameter on the second original integral chart. -/
theorem canonical_reciprocal_integral_pair
    {R A B L : Type} [CommRing R] [CommRing A] [CommRing B] [Field L]
    (f : R →+* L) (a : R →+* A) (b : R →+* B)
    (F : A →+* L) (G : B →+* L) (hF : F.comp a = f) (hG : G.comp b = f)
    (m α : ℕ) (hm : 0 < m) (ε : Rˣ) (s : A) (r : B)
    (hs : F s ≠ 0) (hr : G r = (F s)⁻¹)
    (w q t : normalizedChart F)
    (hw : w ^ m = StageTwo.integralCoeff F (a ε * s ^ α))
    (hq : (q : L) = (w : L) ^ (m / Nat.gcd m α) / F s ^ (α / Nat.gcd m α))
    (ht : (t : L) = F s ^ Nat.gcdA (m / Nat.gcd m α) (α / Nat.gcd m α) *
      (w : L) ^ Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α)) :
    ∃ qB sB : normalizedChart G,
      (qB : L) = (q : L) ∧ (sB : L) = (t : L)⁻¹ ∧ IsUnit qB ∧
      qB ^ Nat.gcd m α = StageTwo.integralCoeff G (b ε) ∧
      (sB : L) ^ (m / Nat.gcd m α) =
        (qB : L) ^ (-Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α)) * G r ∧
      (t : L) * (sB : L) = 1 := by
  let g := Nat.gcd m α
  let n := m / g
  let A₀ := Nat.gcdA n (α / g)
  let B₀ := Nat.gcdB n (α / g)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m α)) hg
  obtain ⟨hqpow, hqunit, htpow, _⟩ := canonical_binomial_integral_identities F m α hm
    (a ε) s (ε.isUnit.map a) hs w q t hw hq ht
  have hqG : (q : L) ^ g = G (b ε) := by
    have hh := congrArg (fun z : normalizedChart F => (z : L)) hqpow
    change (q : L) ^ g = F (a ε) at hh
    exact hh.trans ((DFunLike.congr_fun hF (ε : R)).trans (DFunLike.congr_fun hG (ε : R)).symm)
  have htG : (t : L) ^ n = (q : L) ^ B₀ * (G r)⁻¹ := by
    rw [hr, inv_inv]
    exact htpow
  obtain ⟨qB, sB, hqB, hsB, hqBpow, hsBpow⟩ := reciprocal_binomial_integral_parameters G g n hg hn
    (Units.map b.toMonoidHom ε) r (q : L) (t : L) B₀
    (by change (q : L) ^ g = G (b (ε : R)); exact hqG) htG
  have hquB : IsUnit qB := binomial_component_selector_isUnit G g hg (b ε)
    (ε.isUnit.map b) qB hqBpow
  have ht0 : (t : L) ≠ 0 := by
    intro hz
    have hh := htpow
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at hh
    exact mul_ne_zero (zpow_ne_zero _ ((hqunit.map (normalizedChart F).subtype).ne_zero)) hs hh.symm
  refine ⟨qB, sB, hqB, hsB, hquB, hqBpow, hsBpow, ?_⟩
  rw [hsB]
  exact mul_inv_cancel₀ ht0

end AlgebraicGeometry.RamifiedNormalization.StageFour
