import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Abelian.Exact

/-! Normalization of actual cycle classes under exact functor comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Exact functor comparison of actual homology retains the canonical projection from cycles.
Source: Weibel, An Introduction to Homological Algebra, section 1.3; functorial homology comparison.
HC no distance; AV milestone no distance.
-/
theorem exactFunctor_homology_projection {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  change ((h.map F).cyclesIso.hom ≫ F.map h.π) ≫ F.map h.homologyIso.inv = _
  simp only [Category.assoc, ← F.map_comp]
  rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

#print axioms exactFunctor_homology_projection
end HodgeLean.Foundations.RationalHomologyManifold
