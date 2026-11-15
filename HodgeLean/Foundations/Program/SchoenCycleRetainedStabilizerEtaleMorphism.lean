import HodgeLean.Foundations.Program.SchoenCycleRetainedStabilizerEtaleNeighbourhood
import HodgeLean.Foundations.Program.SchoenCycleFixedFunctionScalarTowers
import HodgeLean.Foundations.Program.SchoenCycleAffineSectionEtaleMorphism

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual stabilizer basic neighbourhood maps etale to the original retained quotient with every original base section evaluation retained.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem s2e_retained_stabilizer_etale_morphism
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
    ∃ g : S, g ∉ P.under S ∧
      ∃ f : Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g)) ⟶ B,
        Etale f.left ∧
        ∀ (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))))
          (a : A), Point.evaluate U a (Point.map f z) =
            ComplexPoint.affineSpecEquiv (Localization.Away g) z
              (algebraMap S (Localization.Away g)
                (s2e_fixed_action_base_map ℂ A C (s2e_powerPointStabilizer Z n x) a)) := by
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
  let H := s2e_powerPointStabilizer Z n x
  let S := FixedPoints.subalgebra ℂ C H
  letI : Algebra A S := (s2e_fixed_action_base_map ℂ A C H).toAlgebra
  letI : IsScalarTower ℂ A S := (s2e_fixed_function_scalar_towers ℂ A C H).1
  obtain ⟨g, hg, het⟩ := s2e_retained_native_stabilizer_etale_neighbourhood
    Z B n γ hγ hquot U hU x hxU hcx
  letI : Algebra.Etale A (Localization.Away g) := het
  let G : A →ₐ[ℂ] Localization.Away g := IsScalarTower.toAlgHom ℂ A (Localization.Away g)
  obtain ⟨f, hf, hv⟩ := s2e_affine_section_etale_morphism B U hU (Localization.Away g) G
    (RingHom.etale_algebraMap.mpr het)
  refine ⟨g, hg, f, hf, ?_⟩
  intro z a
  exact (hv z a).trans (congrArg (ComplexPoint.affineSpecEquiv (Localization.Away g) z)
    (IsScalarTower.algebraMap_apply A S (Localization.Away g) a))

#print axioms s2e_retained_stabilizer_etale_morphism
end HodgeLean.Foundations.Program
