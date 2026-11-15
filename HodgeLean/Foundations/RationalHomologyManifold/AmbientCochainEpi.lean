import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainComplex
import HodgeConjecture.Mathlib.AlgebraicTopology.SimplicialSet.ChainComplexSplit
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Degreewise surjectivity of the actual ambient cochain restriction.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Actual cochains on an open subspace extend to ambient rational singular cochains.
Source: Hatcher, Algebraic Topology, section 3.1; extension of linear functionals on the singular chain inclusion.
HC no distance; AV milestone no distance.
-/
theorem ambientCochainPresheafRestriction_app_surjective (X : TopCat.{0}) (p : ℕ)
    (U : Opens X) :
    Function.Surjective ((ambientCochainPresheafRestriction X p).app (Opposite.op U)) := by
  let g := Opens.inclusion' U
  let f := (singularChainComplexMap ℚ g).f p
  haveI : Mono g := ConcreteCategory.mono_of_injective g Subtype.val_injective
  haveI : IsSplitMono f :=
    AlgebraicTopology.isSplitMono_singularChainComplexFunctor_map_f g (ModuleCat.of ℚ ℚ) p
  have hf : Function.Injective f := (ModuleCat.mono_iff_injective f).mp inferInstance
  exact LinearMap.dualMap_surjective_of_injective hf

#print axioms ambientCochainPresheafRestriction_app_surjective
/-- The actual ambient-to-local restriction is an epimorphism of presheaves in each degree.
Source: Hatcher, Algebraic Topology, section 3.1; degreewise extension of singular cochains.
HC no distance; AV milestone no distance.
-/
theorem ambientCochainPresheafRestriction_epi (X : TopCat.{0}) (p : ℕ) :
    Epi (ambientCochainPresheafRestriction X p) := by
  haveI (U : (Opens X)ᵒᵖ) : Epi ((ambientCochainPresheafRestriction X p).app U) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (ambientCochainPresheafRestriction_app_surjective X p U.unop)
  exact NatTrans.epi_of_epi_app _

#print axioms ambientCochainPresheafRestriction_epi
end HodgeLean.Foundations.RationalHomologyManifold
