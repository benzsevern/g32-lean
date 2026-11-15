import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Defs
import HodgeLean.Foundations.Program.SchoenSelectedGeometrySphere

/-! # Retained point slices and projective coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.Program
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual exceptional slice over the specified point of the centre.
Source: Hartshorne, Algebraic Geometry, II.3, fibre products.
HC no distance; AV milestone no distance. -/
abbrev exceptionalSlice {B' B : Over (Spec ↧ℂ)} (b : B' ⟶ B)
    (x : ComplexPoint B) := pullback b x

example {B' B : Over (Spec ↧ℂ)} (b : B' ⟶ B) (x : ComplexPoint B) :
    pullback.fst b x ≫ b = pullback.snd b x ≫ x := pullback.condition

/-- The retained normalization restricted to the exceptional point slice.
Source: Schoen (1988), Lemma 2.5, printed p. 15.
HC no distance; AV milestone no distance. -/
abbrev coveringSlice {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) := pullback β (pullback.fst b x)

example {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) :
    pullback.fst β (pullback.fst b x) ≫ β =
      pullback.snd β (pullback.fst b x) ≫ pullback.fst b x := pullback.condition

/-- The actual projection from the covering slice to the exceptional slice.
Source: Schoen (1988), Lemma 2.5, printed p. 15.
HC no distance; AV milestone no distance. -/
abbrev sliceProjection {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) : coveringSlice β b x ⟶ exceptionalSlice b x :=
  pullback.snd β (pullback.fst b x)

example {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) :
    sliceProjection β b x ≫ pullback.fst b x =
      pullback.fst β (pullback.fst b x) ≫ β := pullback.condition.symm

/-- Restriction of the retained deck morphism to the actual covering slice.
Source: Schoen (1988), Lemma 2.5, printed p. 15.
HC no distance; AV milestone no distance. -/
def sliceDeck {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β) :
    coveringSlice β b x ⟶ coveringSlice β b x :=
  pullback.lift (pullback.fst _ _ ≫ d) (pullback.snd _ _)
    (by rw [Category.assoc, hd, pullback.condition])

example {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B')
    (b : B' ⟶ B) (x : ComplexPoint B) (d : W ⟶ W) (hd : d ≫ β = β) :
    sliceDeck β b x d hd ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d := by
  simp [sliceDeck]

/-- The original-field generator after removing the selected exceptional factor.
Source: Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
HC no distance; AV milestone no distance. -/
def dividedGenerator {K : Type*} [Field K] (t u : K) : K := t / u

example : dividedGenerator (12 : ℚ) 3 = 4 := by norm_num [dividedGenerator]

/-- The actual projective line over the complex base.
Source: Hartshorne, Algebraic Geometry, II.2.5.
HC no distance; AV milestone no distance. -/
abbrev projectiveLine : Over (Spec ↧ℂ) :=
  Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ))

example : ComplexPoint projectiveLine := s0_sphere_projective_homeomorph ((2 : ℂ) : OnePoint ℂ)

/-- The specified projective coordinate on actual complex points of the line.
Source: Hartshorne, Algebraic Geometry, II.2.5; s0_sphere_projective_homeomorph.
HC no distance; AV milestone no distance. -/
def lineCoordinate : ComplexPoint projectiveLine ≃ₜ OnePoint ℂ :=
  s0_sphere_projective_homeomorph.symm

example : lineCoordinate (s0_sphere_projective_homeomorph ((2 : ℂ) : OnePoint ℂ)) =
    ((2 : ℂ) : OnePoint ℂ) := lineCoordinate.apply_symm_apply _

/-- Coordinates on the labelled actual projective-line point spaces.
Source: Schoen (1988), Lemma 2.5, printed p. 15; product topology.
HC no distance; AV milestone no distance. -/
def componentCoordinate (m a : ℕ) :
    (ZMod (Nat.gcd m a) × ComplexPoint projectiveLine) ≃ₜ componentModel m a :=
  (Homeomorph.refl _).prodCongr lineCoordinate

example : componentCoordinate 6 2 (1, lineCoordinate.symm ((2 : ℂ) : OnePoint ℂ)) =
    (1, ((2 : ℂ) : OnePoint ℂ)) := by
  simp [componentCoordinate]

end AlgebraicGeometry.RamifiedNormalization.StageFour
