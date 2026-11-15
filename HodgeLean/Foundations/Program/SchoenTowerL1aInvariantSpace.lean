import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantGluing

/-! # The scheme glued from invariant section rings

The relative affine scheme constructed from invariant sections, with its
actual affine cover and map to the specified base.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Relative affine gluing data for the invariant rings of an affine map from a finite endomorphism family.
Source: Stacks Project, tags 04A9 and 01LH, invariant functions and relative affine gluing. -/
def s2v_l1a_invariantGlueData
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    (Scheme.AffineZariskiSite.directedCover Y).RelativeGluingData :=
  Scheme.AffineZariskiSite.relativeGluingData
    (s2v_l1a_finite_fixedSectionStructureMap_coequifibered f a ha)

instance s2v_l1a_invariantGlueData_locallyDirected
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    ((s2v_l1a_invariantGlueData f a ha).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The actual scheme obtained by gluing the invariant section rings over the specified base.
Source: Stacks Project, tags 04A9 and 01LH, invariant functions and relative affine gluing. -/
def s2v_l1a_invariantSpace
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) : Scheme :=
  (s2v_l1a_invariantGlueData f a ha).glued

example {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    s2v_l1a_invariantSpace f a ha = (s2v_l1a_invariantGlueData f a ha).glued := rfl

/-- The map from the invariant-ring scheme to the original base.
Source: Stacks Project, tag 01LH, the structure map of relative affine gluing. -/
def s2v_l1a_invariantSpaceMap
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    s2v_l1a_invariantSpace f a ha ⟶ Y :=
  (s2v_l1a_invariantGlueData f a ha).toBase

example {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    s2v_l1a_invariantSpaceMap f a ha = (s2v_l1a_invariantGlueData f a ha).toBase := rfl

/-- The affine cover of the invariant-ring scheme by spectra of the actual invariant rings.
Source: Stacks Project, tag 01LH, the cover of a relative affine gluing. -/
def s2v_l1a_invariantSpaceCover
    {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    (s2v_l1a_invariantSpace f a ha).OpenCover :=
  (s2v_l1a_invariantGlueData f a ha).cover

example {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f)
    (U : Y.AffineZariskiSite) :
    (s2v_l1a_invariantSpaceCover f a ha).X U =
      Spec (CommRingCat.of (s2v_l1a_fixedSectionSubring f a ha U.1)) := rfl

example {X Y : Scheme} {T : Type*} [Finite T]
    (f : X ⟶ Y) [IsAffineHom f]
    (a : T → (X ⟶ X)) (ha : ∀ t, a t ≫ f = f) :
    (s2v_l1a_invariantGlueData f a ha).functor =
      ((Scheme.AffineZariskiSite.toOpensFunctor Y).op ⋙
        s2v_l1a_fixedSectionDiagram f a ha).rightOp ⋙ Scheme.Spec := rfl

end HodgeLean.Foundations.Program
