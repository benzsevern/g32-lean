import HodgeLean.Foundations.Program.SchoenCycleU1SpecAlgebraPoint
import HodgeLean.Foundations.Program.SchoenCycleU1DualResiduePoint

/-! # Actual affine algebra point maps and their residues -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Composition of actual affine complex scheme maps is induced by composition
of their specified complex algebra maps.
Source: Hartshorne, Algebraic Geometry, II.2; Mathlib, `Spec.map_comp`. -/
theorem s2e_u1_specOverMap_comp
    {A C E : Type} [CommRing A] [CommRing C] [CommRing E]
    [Algebra ℂ A] [Algebra ℂ C] [Algebra ℂ E]
    (φ : A →ₐ[ℂ] C) (ψ : C →ₐ[ℂ] E) :
    s2e_u1_specOverMap ψ ≫ s2e_u1_specOverMap φ =
      s2e_u1_specOverMap (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [s2e_u1_specOverMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp] <;> rfl

/-- Actual complex affine points commute with the scheme map of a specified
complex algebra homomorphism.
Source: Hartshorne, Algebraic Geometry, II.2, affine points and their maps. -/
theorem s2e_u1_specAlgebraPoint_map
    {A C : Type} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]
    (φ : A →ₐ[ℂ] C) (e : C →ₐ[ℂ] ℂ) :
    Point.map (s2e_u1_specOverMap φ) (s2e_u1_specAlgebraPoint C e) =
      s2e_u1_specAlgebraPoint A (e.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Point.map, Over.comp_left, s2e_u1_specOverMap, s2e_u1_specAlgebraPoint,
    Over.homMk_left, ← Spec.map_comp] <;> rfl

/-- The actual residue point of an affine dual-number algebra point is its
specified complex residue evaluation.
Source: Hartshorne, Algebraic Geometry, II.8, reduction of tangent vectors. -/
theorem s2e_u1_dualResiduePoint_specOverMap
    {A : Type} [CommRing A] [Algebra ℂ A] (φ : A →ₐ[ℂ] DualNumber ℂ) :
    Point.map (s2e_u1_specOverMap φ) s2e_u1_dualResiduePoint =
      s2e_u1_specAlgebraPoint A ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Point.map, Over.comp_left, s2e_u1_specOverMap, s2e_u1_dualResiduePoint,
    s2e_u1_specAlgebraPoint, Over.homMk_left, ← Spec.map_comp] <;> rfl

/-- The actual constant dual extension of an affine complex point is induced
by its complex evaluation followed by the specified scalar inclusion.
Source: Hartshorne, Algebraic Geometry, II.8, constant tangent vectors. -/
theorem s2e_u1_constantDualPoint_specAlgebraPoint
    {A : Type} [CommRing A] [Algebra ℂ A] (e : A →ₐ[ℂ] ℂ) :
    s2e_u1_constantDualPoint (s2e_u1_specOver A) (s2e_u1_specAlgebraPoint A e) =
      s2e_u1_specOverMap ((TrivSqZeroExt.inlAlgHom ℂ ℂ ℂ).comp e) := by
  apply Over.OverMorphism.ext
  simp only [s2e_u1_constantDualPoint, s2e_u1_specAlgebraPoint, s2e_u1_specOverMap,
    s2e_u1_specOver, Over.mk_hom, Over.homMk_left, ← Spec.map_comp] <;> rfl

/-- Actual constant dual points commute with every morphism over the complex base.
Source: Hartshorne, Algebraic Geometry, II.8, functoriality of constant tangent vectors. -/
theorem s2e_u1_constantDualPoint_map
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (x : ComplexPoint X) :
    s2e_u1_constantDualPoint X x ≫ f =
      s2e_u1_constantDualPoint Y (Point.map f x) := by
  apply Over.OverMorphism.ext
  simp only [s2e_u1_constantDualPoint, Point.map, Over.comp_left, Over.homMk_left,
    Category.assoc]

end HodgeLean.Foundations.Program
