import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.Adapters.CycleClassPullbackDefs
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Geometric inputs for abelian images and quotients

These objects retain schemes over ℂ and their algebraic group morphisms.
Fractions retain an algebraic numerator and a positive integral denominator.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.AbelianQuotient

/-- An abelian variety over ℂ, without a specified endomorphism field or dimension.
Source: Mumford, *Abelian Varieties*, §§7–8; Birkenhake–Lange, §2.4. -/
structure Variety where
  X : Over (Spec ↧ℂ)
  group : GrpObj X
  commutative : IsCommMonObj X
  integral : IsIntegral X.left
  smooth : Smooth X.hom
  projective : IsProjective X.hom

attribute [instance] Variety.group Variety.commutative Variety.integral
  Variety.smooth Variety.projective

/-- A homomorphism of the actual algebraic group objects.
Source: Mumford, *Abelian Varieties*, §7; `CategoryTheory.IsMonHom`. -/
structure Hom (A B : Variety) where
  hom : A.X ⟶ B.X
  mon : IsMonHom hom

attribute [instance] Hom.mon

/-- Multiplication by an integer as an algebraic morphism.
Source: Mumford, *Abelian Varieties*, §7; `AbelianEnd`. -/
def multiplication (A : Variety) (n : ℤ) : Hom A A :=
  ⟨(n : AbelianEnd A.X).hom, inferInstance⟩

/-- The canonical scheme-theoretic image, over the original base.
Source: Mumford, *Abelian Varieties*, §8; Mathlib `Scheme.Hom.image`. -/
def imageModel {A B : Variety} (f : Hom A B) : Over (Spec ↧ℂ) :=
  Over.mk (f.hom.left.imageι ≫ B.X.hom)

/-- The canonical image inclusion over ℂ.
Source: Mathlib `Scheme.Hom.imageι`; Mumford, *Abelian Varieties*, §8. -/
def imageInclusion {A B : Variety} (f : Hom A B) : imageModel f ⟶ B.X :=
  Over.homMk f.hom.left.imageι

/-- The canonical factor to the scheme-theoretic image.
Source: Mathlib `Scheme.Hom.toImage`; Mumford, *Abelian Varieties*, §8. -/
def imageFactor {A B : Variety} (f : Hom A B) : A.X ⟶ imageModel f :=
  Over.homMk f.hom.left.toImage (by
    change f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom) = A.X.hom
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Over.w])

/-- An abelian subvariety retains its algebraic embedding.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3. -/
structure Subvariety (A : Variety) where
  B : Variety
  inclusion : Hom B A
  embedding : IsClosedImmersion inclusion.hom.left

attribute [instance] Subvariety.embedding

/-- Raw algebraic projection data. No quotient property is stored in these data.
Source: Mumford, *Abelian Varieties*, §§7–8 (quotient homomorphism). -/
structure Projection {A : Variety} (_S : Subvariety A) where
  Q : Variety
  map : Hom A Q

/-- The sum of two subvariety inclusions, on the actual scheme product.
Source: Mumford, *Abelian Varieties*, §19 (addition isogeny). -/
def additionMap {A : Variety} (S T : Subvariety A) :
    MonoidalCategory.tensorObj S.B.X T.B.X ⟶ A.X :=
  (fst S.B.X T.B.X ≫ S.inclusion.hom) * (snd S.B.X T.B.X ≫ T.inclusion.hom)

/-- A rational algebraic homomorphism represented by a numerator and positive denominator.
This is a fraction presentation, with no chosen equivalence relation on presentations.
Source: Mumford, *Abelian Varieties*, §19, Hom tensored with ℚ. -/
structure FractionHom (A B : Variety) where
  numerator : Hom A B
  denominator : ℕ
  positive : 0 < denominator

/-- The rational cohomological action of a fraction presentation, in contravariant order.
Source: Birkenhake–Lange, §1.2; `homPullback`. -/
def rationalPullback {A B : Variety} (f : FractionHom A B) :
    HQ B.X 1 →ₗ[ℚ] HQ A.X 1 :=
  (f.denominator : ℚ)⁻¹ • homPullback f.numerator.hom 1

end HodgeLean.Foundations.AbelianQuotient
