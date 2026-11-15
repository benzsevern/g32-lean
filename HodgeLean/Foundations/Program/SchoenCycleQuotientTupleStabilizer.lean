import HodgeLean.Foundations.Program.SchoenCycleQuotientPointPrimeStabilizer
import HodgeLean.Foundations.Program.SchoenCyclePowerPointStabilizer

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The actual retained quotient's affine-prime orbit stabilizer is the full geometric tuple stabilizer.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_quotient_tuple_stabilizer_eq
    (Z B : Over (Spec ↧ℂ)) (n : ℕ)
    [LocallyOfFiniteType (g3_power Z n).hom]
    (γ : g3_power Z n ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (U : B.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint (g3_power Z n)) (hx : x.underlying ∈ γ.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAction (g3_power Z n) B (Equiv.Perm (Fin n))
      (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
    let I := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
    MulAction.stabilizer (Equiv.Perm (Fin n))
      (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit (Equiv.Perm (Fin n)) I) =
      s2e_powerPointStabilizer Z n x := by
  letI := s2e_step1_sectionAction (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  let I := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
  apply Subgroup.ext
  intro σ
  change σ • (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit (Equiv.Perm (Fin n)) I) =
    (⟨I, MulAction.mem_orbit_self I⟩ : MulAction.orbit (Equiv.Perm (Fin n)) I) ↔
      Point.map (s2_permute Z n σ) x = x
  rw [Subtype.ext_iff]
  exact s2e_quotient_point_prime_stabilizer (g3_power Z n) B (Equiv.Perm (Fin n))
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n)
    γ hγ U hU x hx σ

#print axioms s2e_quotient_tuple_stabilizer_eq
end HodgeLean.Foundations.Program
