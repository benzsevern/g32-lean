import Mathlib.AlgebraicGeometry.Morphisms.Finite
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FibreDegreeHelpers

/-! # Affine section towers for the actual generic stalk embedding -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The retained generic stalk transport agrees with restriction of the
actual affine section map to rational functions. -/
theorem s2e_c1_genericStalkMap_comp_germ
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (hg : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X) = f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  have hx : genericPoint X ∈ f ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
      (by simpa using ‹Nonempty (f ⁻¹ᵁ U)›)
  have htransport (x y : Y) (h : x = y) (hx : x ∈ U) (hy : y ∈ U) :
      Y.presheaf.germ U y hy ≫ eqToHom (congrArg Y.presheaf.stalk h.symm) =
        Y.presheaf.germ U x hx := by
    subst y
    simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, htransport (f (genericPoint X)) (genericPoint Y) hg hx]
  exact f.germ_stalkMap U (genericPoint X) hx

/-- The degree over the projection's specified generic stalk embedding
is the rank of the actual section algebra on any nonempty affine base chart. -/
theorem s2e_c1_genericStalk_fieldDegree_eq_section_finrank
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
    (hg : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.finrank Y.functionField X.functionField =
      Module.finrank Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  letI := φ.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra Γ(Y, U) X.functionField :=
    ((X.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (s2e_c1_genericStalkMap_comp_germ f hg U)).symm
  haveI : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  haveI : IsFractionRing Γ(X, f ⁻¹ᵁ U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ (hU.preimage f)
  exact IsFractionRing.finrank_eq Γ(Y, U) Y.functionField Γ(X, f ⁻¹ᵁ U) X.functionField


/-- An etale geometric fibre on a finite flat affine chart measures the
degree over the exact retained generic stalk embedding. -/
theorem s2e_c1_genericStalk_fieldDegree_eq_geometric_fibre_card
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
    (hg : f (genericPoint X) = genericPoint Y)
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (k : Type) [Field k] [IsSepClosed k] :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    ∀ [Algebra Γ(Y, U) k] [Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U)]
      [Algebra.Etale k (k ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U))],
    Module.finrank Y.functionField X.functionField =
      Nat.card (Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] k) := by
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  letI := φ.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  dsimp only
  intro hk hflat hEt
  letI := hk
  letI := hflat
  letI := hEt
  haveI : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := f.finite_app U hU
  exact (s2e_c1_genericStalk_fieldDegree_eq_section_finrank f hg U hU).trans
    (s2e_c1_finiteFlat_rank_eq_geometric_fibre_card Γ(Y, U) Γ(X, f ⁻¹ᵁ U) k)


end HodgeLean.Foundations.Program
