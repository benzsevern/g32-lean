import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Maximal ideals of actual unramified stalk maps -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual unramified morphism locally of finite type extends the
maximal ideal of the target stalk to the maximal ideal of the source stalk.
Source: Stacks Project, Tag 00UW;
Mathlib, Algebra.FormallyUnramified.map_maximalIdeal. -/
theorem s2e_unramified_stalk_map_maximalIdeal
    {X Y : Scheme} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (x : X) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f x
  exact Algebra.FormallyUnramified.map_maximalIdeal

#print axioms s2e_unramified_stalk_map_maximalIdeal
/-- An unramified essentially finite type algebra which is local extends
any maximal ideal lying below its maximal ideal to that maximal ideal.
Source: Stacks Project, Tag 00UW;
Mathlib, Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal. -/
theorem s2e_unramified_local_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    (I : Ideal R) [I.IsMaximal]
    (hI : I.map (algebraMap R S) ≤ IsLocalRing.maximalIdeal S) :
    I.map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let J := I.map (algebraMap R S)
  let Q := S ⧸ J
  letI : Algebra (R ⧸ I) Q := inferInstanceAs (Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  letI : IsScalarTower R (R ⧸ I) Q := inferInstanceAs
    (IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  have : Algebra.FormallyUnramified R Q := Algebra.FormallyUnramified.comp R S Q
  have : Algebra.FormallyUnramified (R ⧸ I) Q :=
    Algebra.FormallyUnramified.of_restrictScalars R _ _
  have : Algebra.EssFiniteType R Q := Algebra.EssFiniteType.comp R S Q
  have : Algebra.EssFiniteType (R ⧸ I) Q := Algebra.EssFiniteType.of_comp R _ _
  have : Module.Finite (R ⧸ I) Q := Algebra.FormallyUnramified.finite_of_free _ _
  have : IsReduced Q := Algebra.FormallyUnramified.isReduced_of_field (R ⧸ I) Q
  have : IsArtinianRing Q := isArtinian_of_tower (R ⧸ I) inferInstance
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hI)
  have : IsLocalRing Q := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hzero : IsLocalRing.maximalIdeal Q = ⊥ := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal Q) bot_ne_top,
      IsArtinianRing.jacobson_eq_radical, ← Ideal.zero_eq_bot, ← nilradical, nilradical_eq_zero]
  have hfield : IsField Q := (IsLocalRing.isField_iff_maximalIdeal_eq (R := Q)).mpr hzero
  apply IsLocalRing.eq_maximalIdeal
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield

#print axioms s2e_unramified_local_map_maximalIdeal
end HodgeLean.Foundations.Program
