import HodgeLean.Foundations.BundleThom.SubcomplexMayerVietorisHelpers
import HodgeLean.Foundations.BundleThom.CokernelColimitHelpers

/-! # Actual relative chain diagrams for a fixed singular subcomplex

The relative complexes retain the supplied ambient subcomplex and its intersection with the fixed subspace.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology
namespace HodgeLean.Foundations.BundleThom

/-- The actual rational chain diagram of subcomplex inclusions in a supplied simplicial set.
Source: Hatcher, Algebraic Topology, §2.1, singular subcomplex chains. -/
def i1_subcomplexChainFunctor (X : SSet.{0}) : X.Subcomplex ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  SSet.Subcomplex.toSSetFunctor (X := X) ⋙ (SSet.chainComplexFunctor.{0,0,1} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The actual chain inclusion of intersection with a supplied fixed subcomplex, functorially in the ambient domain.
Source: Hatcher, Algebraic Topology, §2.2, relative Mayer–Vietoris chain diagrams. -/
def i1_relativeSubcomplexArrowFunctor (X : SSet.{0}) (Z : X.Subcomplex) :
    X.Subcomplex ⥤ Arrow (ChainComplex (ModuleCat.{0} ℚ) ℕ) where
  obj U := Arrow.mk (SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (inf_le_left : U ⊓ Z ≤ U)) (ModuleCat.of ℚ ℚ))
  map {U V} f := Arrow.homMk
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_inf (leOfHom f) le_rfl)) (ModuleCat.of ℚ ℚ))
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (leOfHom f)) (ModuleCat.of ℚ ℚ)) (by
      change SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _ =
        SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      rfl)
  map_id U := by
    apply Arrow.hom_ext
    · exact ((SSet.chainComplexFunctor.{0,0,1} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id _
    · exact ((SSet.chainComplexFunctor.{0,0,1} (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id _
  map_comp f g := by
    apply Arrow.hom_ext
    · change SSet.chainComplexMap _ _ = SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    · change SSet.chainComplexMap _ _ = SSet.chainComplexMap _ _ ≫ SSet.chainComplexMap _ _
      rw [← CategoryTheory.Functor.map_comp]
      rfl

/-- Actual relative rational chains modulo the fixed subcomplex on every supplied ambient domain.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative singular chains. -/
def i1_relativeSubcomplexChainFunctor (X : SSet.{0}) (Z : X.Subcomplex) :
    X.Subcomplex ⥤ ChainComplex (ModuleCat.{0} ℚ) ℕ :=
  i1_relativeSubcomplexArrowFunctor X Z ⋙ coker (C := ChainComplex (ModuleCat.{0} ℚ) ℕ)

end HodgeLean.Foundations.BundleThom
