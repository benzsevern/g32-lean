import HodgeLean.Foundations.Curves.Picard.Defs
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Fiber

/-! # Divisor families on curve products

Ideals retain their scheme structure, including over nonreduced parameter schemes.
The parameter-space record contains a scheme and a family, with no representation field.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Curves.Picard.Families

/-- The actual curve product over the complex ground scheme.
Source: Hartshorne, Algebraic Geometry, II.3, fibre products. -/
abbrev Product (C T : Over (Spec ↧ℂ)) : Scheme := pullback C.hom T.hom

example (C T : Over (Spec ↧ℂ)) : Product C T ⟶ T.left := pullback.snd _ _

/-- The map on curve products induced by a parameter morphism.
Source: Hartshorne II.3, universal property of fibre products. -/
def productMap (C : Over (Spec ↧ℂ)) {T T' : Over (Spec ↧ℂ)} (f : T' ⟶ T) :
    Product C T' ⟶ Product C T :=
  pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp)

example (C : Over (Spec ↧ℂ)) {T T' : Over (Spec ↧ℂ)} (f : T' ⟶ T) :
    productMap C f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left := by
  simp [productMap]

/-- Fibre dimension measured with its actual residue-field algebra structure.
Source: Stacks Project, Tag 0B9C, degree of a finite flat divisor. -/
def fiberDegree {D T : Scheme} (p : D ⟶ T) (t : T) : ℕ :=
  letI := (((Scheme.ΓSpecIso (T.residueField t)).inv ≫
    (p.fiberToSpecResidueField t).appTop).hom).toAlgebra
  Module.finrank (T.residueField t) Γ(p.fiber t, ⊤)

example {D T : Scheme} (p : D ⟶ T) [IsEmpty D] (t : T) :
    fiberDegree p t = 0 := by
  letI : IsEmpty (p.fiber t) := Function.isEmpty (p.fiberι t)
  letI := (((Scheme.ΓSpecIso (T.residueField t)).inv ≫
    (p.fiberToSpecResidueField t).appTop).hom).toAlgebra
  change Module.finrank (T.residueField t) Γ(p.fiber t, ⊤) = 0
  exact Module.finrank_zero_of_subsingleton

example (T : Scheme) (t : T) : fiberDegree (𝟙 T) t = 1 := by
  let p := (𝟙 T : T ⟶ T).fiberToSpecResidueField t
  haveI : IsIso p := inferInstanceAs (IsIso (pullback.snd (𝟙 T) _))
  haveI : IsIso p.appTop := Scheme.Γ.map_isIso p.op
  let φ := (Scheme.ΓSpecIso (T.residueField t)).inv ≫ p.appTop
  haveI : IsIso φ := by
    dsimp only [φ]
    infer_instance
  letI := φ.hom.toAlgebra
  change Module.finrank (T.residueField t) Γ((𝟙 T : T ⟶ T).fiber t, ⊤) = 1
  apply Module.finrank_of_bijective_algebraMap
  exact (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance

/-- A finite flat relative effective Cartier divisor of specified degree.
The local equations are regular on an affine neighbourhood of every product point.
Source: Stacks Project, Tags 056P and 0B9C. -/
structure Family (C T : Over (Spec ↧ℂ)) (n : ℕ) where
  ideal : (Product C T).IdealSheafData
  localEquation : ∀ x : Product C T, ∃ U : (Product C T).affineOpens,
    x ∈ U.1 ∧ ∃ a : Γ(Product C T, U.1),
      IsRegular a ∧ ideal.ideal U = Ideal.span ({a} : Set Γ(Product C T, U.1))
  finite : IsFinite (ideal.subschemeι ≫ pullback.snd C.hom T.hom)
  flat : Flat (ideal.subschemeι ≫ pullback.snd C.hom T.hom)
  degree : ∀ t : T.left,
    fiberDegree (ideal.subschemeι ≫ pullback.snd C.hom T.hom) t = n

example (D : Family E E 2) (t : E.left) :
    fiberDegree (D.ideal.subschemeι ≫ pullback.snd E.hom E.hom) t = 2 := D.degree t

example (D : Family E E 3) (t : E.left) :
    fiberDegree (D.ideal.subschemeι ≫ pullback.snd E.hom E.hom) t = 3 := D.degree t

/-- The graph ideal of an actual parameter-to-curve morphism.
Source: Stacks Project, Tag 0B9E, sums of graphs. -/
def graphIdeal {C T : Over (Spec ↧ℂ)} (f : T ⟶ C) :
    (Product C T).IdealSheafData :=
  (pullback.lift f.left (𝟙 T.left) (by simp)).ker

example : (graphIdeal (𝟙 E)).subscheme ⟶ Product E E :=
  (graphIdeal (𝟙 E)).subschemeι

/-- A scheme with a degree-n family, before any universal property is imposed.
Source: Stacks Project, Tag 0B9C, universal divisor on the Hilbert scheme. -/
structure ParameterSpace (C : Over (Spec ↧ℂ)) (n : ℕ) where
  base : Over (Spec ↧ℂ)
  universal : Family C base n

example (A : ParameterSpace E 2) (t : A.base.left) :
    fiberDegree (A.universal.ideal.subschemeι ≫ pullback.snd E.hom A.base.hom) t = 2 :=
  A.universal.degree t

/-- The ordered scheme power in the category of complex schemes.
Source: Hartshorne II.3, finite fibre products. -/
abbrev OrderedPower (C : Over (Spec ↧ℂ)) (n : ℕ) : Over (Spec ↧ℂ) :=
  ∏ᶜ (fun _ : Fin n => C)

example (C : Over (Spec ↧ℂ)) : OrderedPower C 2 ⟶ C :=
  Pi.π (fun _ : Fin 2 => C) 0

end HodgeLean.Foundations.Curves.Picard.Families
