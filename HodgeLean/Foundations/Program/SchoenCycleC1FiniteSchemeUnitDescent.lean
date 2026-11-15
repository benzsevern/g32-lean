import HodgeLean.Foundations.Program.SchoenCycleC1NormalUnitDescent
import HodgeLean.Foundations.Program.SchoenCycleC1DominantGenericPoint
import HodgeLean.Foundations.Program.SchoenCycleC1SectionFieldTowerHelpers
import HodgeLean.Foundations.Program.SchoenQuotientNormality

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A base rational function whose actual pullback is a unit on the whole
affine inverse image descends to a unit on the original smooth base chart.
The original generic stalk map and both section embeddings are retained. -/
theorem s2e_c1_finite_scheme_unit_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [IsDominant f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (t : Y.left.functionField) (u : Γ(X.left, f.left ⁻¹ᵁ U)ˣ) :
    let hg := s2e_c1_dominant_generic_point f.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    letI : Nonempty (f.left ⁻¹ᵁ U) := ⟨⟨genericPoint X.left, by
      change f.left (genericPoint X.left) ∈ U
      rw [hg]
      exact ((genericPoint_spec Y.left).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)⟩⟩
    φ t = X.left.germToFunctionField (f.left ⁻¹ᵁ U) (u : Γ(X.left, f.left ⁻¹ᵁ U)) →
      ∃ v : Γ(Y.left, U)ˣ, Y.left.germToFunctionField U (v : Γ(Y.left, U)) = t := by
  dsimp only
  let hg := s2e_c1_dominant_generic_point f.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    f.left.stalkMap (genericPoint X.left)).hom
  letI : Nonempty (f.left ⁻¹ᵁ U) := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ U
    rw [hg]
    exact ((genericPoint_spec Y.left).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)⟩⟩
  intro ht
  letI : Algebra Y.left.functionField X.left.functionField := φ.toAlgebra
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  letI : Algebra Γ(Y.left, U) X.left.functionField :=
    ((X.left.germToFunctionField (f.left ⁻¹ᵁ U)).hom.comp (f.left.app U).hom).toAlgebra
  letI : IsScalarTower Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(Y.left, U) Y.left.functionField X.left.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (s2e_c1_genericStalkMap_comp_germ f.left hg U)).symm
  letI : IsFractionRing Γ(Y.left, U) Y.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y.left U hU
  letI : IsFractionRing Γ(X.left, f.left ⁻¹ᵁ U) X.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen X.left _ (hU.preimage f.left)
  letI : Module.Finite Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := f.left.finite_app U hU
  letI : IsIntegrallyClosed Γ(Y.left, U) :=
    s2_affineOpen_sections_integrallyClosed (zmtiso_normal_of_smooth Y.left Y.hom) hU
  exact s2e_c1_normal_unit_descent t u ht

end HodgeLean.Foundations.Program
