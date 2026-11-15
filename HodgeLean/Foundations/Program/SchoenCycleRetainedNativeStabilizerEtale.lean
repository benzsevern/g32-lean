import HodgeLean.Foundations.Program.SchoenCycleNativeFixedFunctionEtale
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionTower
import HodgeLean.Foundations.Program.SchoenCycleComplexPointAugmentation
import HodgeLean.Foundations.Program.SchoenCycleMixedExactFixedFunctionCotangent
import HodgeLean.Foundations.Program.SchoenCycleIdentifiedStabilizerEtale
import HodgeLean.Foundations.Program.SchoenCycleQuotientSectionInvariants
import HodgeLean.Foundations.Program.SchoenCycleQuotientTupleStabilizer
import HodgeLean.Foundations.Program.SchoenCycleQuotientAffineFiniteType

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual retained tuple stabilizer section algebra is etale over the retained quotient section ring at the contracted prime of the actual marked complex point, with its native complex scalars.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1; EGA IV, 17.6.1. -/
theorem s2e_retained_native_stabilizer_section_algebra_etale
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom] [IsIntegral B.left]
    (n : ℕ) (γ : g3_power Z n ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z n ⟶ T),
      (∀ σ, s2_permute Z n σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint (g3_power Z n)) (hxU : x.underlying ∈ γ.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set (g3_power Z n).left)) :
    let A := Γ(B.left, U)
    let C := Γ((g3_power Z n).left, γ.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAlgebra B U
    letI := s2e_step1_sectionAlgebra (g3_power Z n) (γ.left ⁻¹ᵁ U)
    letI : Algebra A C := (γ.left.app U).hom.toAlgebra
    letI := s2e_complex_section_app_tower (g3_power Z n) B γ U
    letI := s2e_step1_sectionAction (g3_power Z n) B (Equiv.Perm (Fin n))
      (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
    letI := s2e_quotient_sectionAction_base_smulComm (g3_power Z n) B (Equiv.Perm (Fin n))
      (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
    letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B (Equiv.Perm (Fin n))
      (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
    let S := FixedPoints.subalgebra ℂ C (s2e_powerPointStabilizer Z n x)
    letI : Algebra A S := (s2e_fixed_action_base_map ℂ A C (s2e_powerPointStabilizer Z n x)).toAlgebra
    let P := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
    Algebra.IsEtaleAt A (P.under S) := by
  dsimp only
  let A := Γ(B.left, U)
  let C := Γ((g3_power Z n).left, γ.left ⁻¹ᵁ U)
  let G := Equiv.Perm (Fin n)
  letI := s2e_step1_sectionAlgebra B U
  letI := s2e_step1_sectionAlgebra (g3_power Z n) (γ.left ⁻¹ᵁ U)
  letI : Algebra A C := (γ.left.app U).hom.toAlgebra
  letI := s2e_complex_section_app_tower (g3_power Z n) B γ U
  letI := s2e_step1_sectionAction (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  letI := s2e_quotient_sectionAction_base_smulComm (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  letI := s2e_step1_sectionAction_smulComm (g3_power Z n) B G
    (s2_permute Z n) (s2e_step1_permute_one Z n) (s2e_step1_permute_mul Z n) γ hγ U
  letI : Algebra.FiniteType ℂ A := s2e_finite_surjective_affine_sections_finiteType
    (g3_power Z n) B γ U hU
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  letI : Module.Finite A C := γ.left.finite_app U hU
  letI : Algebra.IsInvariant A C G := s2e_quotient_section_invariant_extension
    (g3_power Z n) B G (s2_permute Z n) (s2e_step1_permute_one Z n)
    (s2e_step1_permute_mul Z n) γ hγ hquot U hU
  letI := IsSchemeTheoreticallyDominant.of_isDominant γ.left
  have hinj : Function.Injective (algebraMap A C) := γ.left.app_injective U
  let P := ((hU.preimage γ.left).primeIdealOf ⟨x.underlying, hxU⟩).asIdeal
  letI : P.IsMaximal := (hU.preimage γ.left).primeIdealOf_isMaximal_of_isClosed
    ⟨x.underlying, hxU⟩ hcx
  let H := s2e_powerPointStabilizer Z n x
  letI : Fintype H := Fintype.ofFinite H
  letI : Algebra ℂ ((g3_power Z n).left.presheaf.stalk x.underlying) :=
    (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
  let a := fun σ : H => s2_permute Z n σ.val
  let ha1 : a 1 = 𝟙 (g3_power Z n) := s2e_step1_permute_one Z n
  let hamul : ∀ u v, a (u * v) = a v ≫ a u := fun u v => s2e_step1_permute_mul Z n u.val v.val
  let hinv := fun σ : H => hγ σ.val
  let hfix := fun σ : H => s2e_complex_point_fixed_underlying (g3_power Z n) (a σ) x σ.property
  let f0 := s2e_complex_fixed_function_local_pullback (g3_power Z n) B H a ha1 hamul γ hinv
    U (hU.preimage γ.left) x.underlying hxU hfix
  let ε := (s2e_complex_point_augmentation (g3_power Z n) x).comp f0
  apply s2e_native_fixed_function_etale_of_stabilizer_eq A C G hinj P H
    (s2e_quotient_tuple_stabilizer_eq Z B n γ hγ U hU x hxU).symm
  exact ε

#print axioms s2e_retained_native_stabilizer_section_algebra_etale
end HodgeLean.Foundations.Program
