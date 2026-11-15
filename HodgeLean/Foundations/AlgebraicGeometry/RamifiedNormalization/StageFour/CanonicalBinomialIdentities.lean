import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.CanonicalBranchParameter
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.ComponentSelector

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The canonical field expressions retain the selector unit, its exact power, the parameter power and generator reconstruction. -/
theorem canonical_binomial_integral_identities
    {A L : Type} [CommRing A] [Field L] (F : A →+* L)
    (m α : ℕ) (hm : 0 < m) (ε s : A) (hε : IsUnit ε) (hs : F s ≠ 0)
    (w q t : normalizedChart F)
    (hw : w ^ m = StageTwo.integralCoeff F (ε * s ^ α))
    (hq : (q : L) = (w : L) ^ (m / Nat.gcd m α) / F s ^ (α / Nat.gcd m α))
    (ht : (t : L) = F s ^ Nat.gcdA (m / Nat.gcd m α) (α / Nat.gcd m α) *
      (w : L) ^ Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α)) :
    q ^ Nat.gcd m α = StageTwo.integralCoeff F ε ∧ IsUnit q ∧
    (t : L) ^ (m / Nat.gcd m α) =
      (q : L) ^ Nat.gcdB (m / Nat.gcd m α) (α / Nat.gcd m α) * F s ∧
    (t : L) ^ (α / Nat.gcd m α) *
      (q : L) ^ Nat.gcdA (m / Nat.gcd m α) (α / Nat.gcd m α) = (w : L) := by
  let g := Nat.gcd m α
  let n := m / g
  let a := α / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m α)) hg
  have hcop : n.Coprime a := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨q₀, hq₀, hpow, hweq⟩ := binomial_component_selector F m α hm ε s hs w hw
  have heq : q = q₀ := Subtype.ext (hq.trans hq₀.symm)
  rw [← heq] at hpow hweq
  have hu := binomial_component_selector_isUnit F g hg ε hε q hpow
  have hwe : (w : L) ^ n = (q : L) * F s ^ a :=
    congrArg (fun z : normalizedChart F => (z : L)) hweq
  have hw0 : (w : L) ≠ 0 := by
    intro hz
    have h := hwe
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at h
    exact mul_ne_zero ((hu.map (normalizedChart F).subtype).ne_zero) (pow_ne_zero a hs) h.symm
  refine ⟨hpow, hu, ?_, ?_⟩
  · rw [ht]
    exact binomial_bezout_parameter_power n a hcop (F s) (w : L) (q : L) hs hwe
  · rw [ht]
    exact binomial_bezout_reconstruction n a hcop (F s) (w : L) (q : L) hw0 hwe

end AlgebraicGeometry.RamifiedNormalization.StageFour
