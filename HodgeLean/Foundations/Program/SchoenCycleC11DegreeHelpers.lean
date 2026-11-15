import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Complex-point surjectivity detects surjectivity for a morphism with closed scheme image.
Source: Hartshorne, Algebraic Geometry, II.3.14, Jacobson closed-point detection. -/
theorem s2e_c11_surjective_of_complex_points
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (hc : IsClosed (Set.range f.left)) (hs : Function.Surjective (Point.map f)) :
    Surjective f.left := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  refine ⟨?_⟩
  intro y
  by_contra hy
  have hyc : y ∈ (Set.range f.left)ᶜ := hy
  obtain ⟨z, hzc, hz⟩ := nonempty_inter_closedPoints ⟨y, hyc⟩ hc.isOpen_compl.isLocallyClosed
  let p : Point ℂ Y := Over.homMk (pointOfClosedPoint Y.hom z hz)
    (pointOfClosedPoint_comp Y.hom z hz)
  obtain ⟨q, hq⟩ := hs p
  have hp : p.underlying = z := pointOfClosedPoint_apply Y.hom z hz _
  apply hzc
  refine ⟨q.underlying, ?_⟩
  exact (congrArg Point.underlying hq).trans hp

/-- The actual scheme diagonal viewed with its inherited complex structure.
Source: Mathlib, pullback.diagonal_fst. -/
def s2e_c11_diagonalOver (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) :
    X ⟶ Over.mk (pullback.fst f.left f.left ≫ X.hom) :=
  Over.homMk (pullback.diagonal f.left) (by
    change pullback.diagonal f.left ≫ (pullback.fst f.left f.left ≫ X.hom) = X.hom
    simp only [← Category.assoc, pullback.diagonal_fst, Category.id_comp])

/-- Injectivity on complex points makes the actual diagonal surjective on complex points.
Source: Mathlib, pullback universal property and diagonal projection identities. -/
theorem s2e_c11_diagonal_point_surjective
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (hinj : Function.Injective (Point.map f)) :
    Function.Surjective (Point.map (s2e_c11_diagonalOver X Y f)) := by
  intro z
  let a : Point ℂ X := Over.homMk (z.left ≫ pullback.fst f.left f.left) (by
    rw [Category.assoc]; exact Over.w z)
  have hstruct : pullback.snd f.left f.left ≫ X.hom =
      pullback.fst f.left f.left ≫ X.hom := by
    rw [← Over.w f, ← Category.assoc, ← Category.assoc, pullback.condition]
  let b : Point ℂ X := Over.homMk (z.left ≫ pullback.snd f.left f.left) (by
    rw [Category.assoc, hstruct]; exact Over.w z)
  have hab : a = b := by
    apply hinj
    apply Over.OverMorphism.ext
    change (z.left ≫ pullback.fst f.left f.left) ≫ f.left =
      (z.left ≫ pullback.snd f.left f.left) ≫ f.left
    rw [Category.assoc, Category.assoc, pullback.condition]
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (a.left ≫ pullback.diagonal f.left) ≫ pullback.fst f.left f.left =
      z.left ≫ pullback.fst f.left f.left
    rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    rfl
  · change (a.left ≫ pullback.diagonal f.left) ≫ pullback.snd f.left f.left =
      z.left ≫ pullback.snd f.left f.left
    rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    exact congrArg (fun t => t.left) hab

/-- For finite unramified maps, complex-point injectivity detects the scheme monomorphism.
Source: Mathlib, the open diagonal of an unramified morphism and pullback.isIso_diagonal_iff. -/
theorem s2e_c11_finite_unramified_mono_of_point_injective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [IsFinite f.left] [FormallyUnramified f.left]
    (hinj : Function.Injective (Point.map f)) : Mono f.left := by
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  let δ : X ⟶ P := s2e_c11_diagonalOver X Y f
  letI : LocallyOfFiniteType P.hom := by
    change LocallyOfFiniteType (pullback.fst f.left f.left ≫ X.hom)
    infer_instance
  have hc : IsClosed (Set.range δ.left) :=
    (pullback.diagonal f.left).isClosedEmbedding.isClosed_range
  have hs : Surjective δ.left := s2e_c11_surjective_of_complex_points X P δ hc
    (s2e_c11_diagonal_point_surjective X Y f hinj)
  have hd : IsIso (pullback.diagonal f.left) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f.left).mp hd

/-- A finite etale map bijective on complex points is a scheme isomorphism.
Source: Mathlib, Flat.isIso_of_surjective_of_mono; SGA 1, Expose I, Proposition 5.1. -/
theorem s2e_c11_finite_etale_isIso_of_point_bijective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left]
    (hbij : Function.Bijective (Point.map f)) : IsIso f.left := by
  letI : Mono f.left := s2e_c11_finite_unramified_mono_of_point_injective X Y f hbij.1
  letI : Surjective f.left := s2e_c11_surjective_of_complex_points X Y f
    f.left.isClosedMap.isClosed_range hbij.2
  exact Flat.isIso_of_surjective_of_mono f.left

/-- The exact point-preimage of a section makes its restricted component point map bijective.
Source: SGA 1, Expose I, Proposition 5.1, pointwise degree-one criterion. -/
theorem s2e_c11_section_component_point_bijective
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (s : Point ℂ Y → Point ℂ X)
    (hs : ∀ y, Point.map f (s y) = y) (U : X.left.Opens)
    (hpoints : Point.underlying ⁻¹' (U : Set X.left) = Set.range s) :
    Function.Bijective (Point.map (openInclusion X U ≫ f)) := by
  let i := openInclusion X U
  have hleft (q : Point ℂ (openScheme X U)) :
      s (Point.map f (Point.map i q)) = Point.map i q := by
    have hmem : Point.map i q ∈ Point.underlying ⁻¹' (U : Set X.left) :=
      q.underlying.property
    rw [hpoints] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [← hy, hs y]
  constructor
  · intro a b h
    apply map_injective_of_mono i
    rw [← hleft a, ← hleft b]
    exact congrArg s h
  · intro y
    have hy : s y ∈ Point.underlying ⁻¹' (U : Set X.left) := by
      rw [hpoints]
      exact ⟨y, rfl⟩
    let q := (openHomeomorph X U).symm ⟨s y, hy⟩
    have hi : Point.map i q = s y :=
      congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨s y, hy⟩)
    refine ⟨q, ?_⟩
    rw [Point.map_comp_apply, hi, hs y]

end HodgeLean.Foundations.Program
