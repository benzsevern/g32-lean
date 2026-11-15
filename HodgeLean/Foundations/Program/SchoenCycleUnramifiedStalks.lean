import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Maximal ideals along actual unramified stalk maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual unramified stalk map extends the source maximal ideal to the
target maximal ideal.
Source: Hartshorne, Algebraic Geometry, II.8; Stacks Project, Tag 00UW. -/
theorem s2e_unramified_stalk_maximalIdeal
    {X Y : Scheme} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] (x : X) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  letI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  letI : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  letI : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  simpa only [RingHom.algebraMap_toAlgebra] using
    (Algebra.FormallyUnramified.map_maximalIdeal
      (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x))

/-- A generator of the base maximal ideal pulls back to a generator of the
actual maximal ideal along an unramified stalk map.
Source: Hartshorne, Algebraic Geometry, II.8; Stacks Project, Tag 00UW. -/
theorem s2e_unramified_stalk_parameter
    {X Y : Scheme} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] (x : X)
    (t : Y.presheaf.stalk (f x))
    (ht : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) = Ideal.span {t}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) = Ideal.span {f.stalkMap x t} := by
  rw [← s2e_unramified_stalk_maximalIdeal f x, ht, Ideal.map_span, Set.image_singleton]

end HodgeLean.Foundations.Program
