import HodgeLean.Foundations.AbelianQuotient.Proofs

/-! # Abelian image, quotient and multiplication section interface

The first stage retains the algebraic objects and rational pullback variance.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.AbelianQuotient
/-- The canonical scheme image inherits an abelian variety structure; its factor is onto.
Source: Mumford, *Abelian Varieties*, §8; Birkenhake–Lange, §2.4. -/
theorem connected_image {A B : Variety} (f : Hom A B) :
    ∃ G : GrpObj (imageModel f),
      letI := G
      IsCommMonObj (imageModel f) ∧ IsIntegral (imageModel f).left ∧
      Smooth (imageModel f).hom ∧ IsProjective (imageModel f).hom ∧
      IsMonHom (imageFactor f) ∧ IsMonHom (imageInclusion f) ∧
      Function.Surjective (Point.map (imageFactor f)) :=
  connected_image_aux f

/-- The quotient is an actual abelian variety with the expected kernel and universal property.
Source: Mumford, *Abelian Varieties*, §§7–8; Birkenhake–Lange, §5.3. -/
theorem quotient_exists {A : Variety} (S : Subvariety A) :
    ∃ q : Projection S,
      Function.Surjective (Point.map q.map.hom) ∧
      {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
        Set.range (Point.map S.inclusion.hom) ∧
      ∀ (T : Variety) (f : Hom A T), S.inclusion.hom ≫ f.hom = (1 : S.B.X ⟶ T.X) →
        ∃! g : Hom q.Q T, q.map.hom ≫ g.hom = f.hom :=
  quotient_exists_aux S

/-- Rational H¹ of the quotient identifies with the kernel of restriction to the subvariety.
Source: Birkenhake–Lange, §§2.4, 5.3; Mumford, *Abelian Varieties*, §8. -/
theorem quotient_h1 {A : Variety} {S : Subvariety A} (q : Projection S)
    (hs : Function.Surjective (Point.map q.map.hom))
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom)) :
    Function.Injective (homPullback q.map.hom 1) ∧
      LinearMap.range (homPullback q.map.hom 1) =
        LinearMap.ker (homPullback S.inclusion.hom 1) :=
  quotient_h1_aux q hs hk

/-- Injective rational H¹ pullback forces geometric surjectivity.
Source: Birkenhake–Lange, §§2.4, 5.3; S4 contract A1a9. -/
theorem surjective_of_injective_h1 {A B : Variety} (f : Hom A B)
    (hi : Function.Injective (homPullback f.hom 1)) :
    Function.Surjective (Point.map f.hom) :=
  surjective_of_injective_h1_aux f hi

/-- Poincaré reducibility: the sum with a complementary abelian subvariety is an isogeny.
Projectivity in `Variety` supplies polarizability; this is not a statement for general tori.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3. -/
theorem complement_exists {A : Variety} (S : Subvariety A) :
    ∃ T : Subvariety A, ccm2_IsogenyOnPoints (additionMap S T) :=
  complement_exists_aux S

/-- An isogeny has an algebraic fraction inverse with both multiplication identities.
The associated rational H¹ actions are mutual inverses.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3. -/
theorem rational_inverse {A B : Variety} (f : Hom A B) (hi : ccm2_IsogenyOnPoints f.hom) :
    ∃ g : FractionHom B A,
      g.numerator.hom ≫ f.hom = (multiplication B g.denominator).hom ∧
      f.hom ≫ g.numerator.hom = (multiplication A g.denominator).hom ∧
      (homPullback f.hom 1).comp (rationalPullback g) = LinearMap.id ∧
      (rationalPullback g).comp (homPullback f.hom 1) = LinearMap.id :=
  rational_inverse_aux f hi

/-- A surjective algebraic homomorphism has a positive integral multiplication section.
The pullback equation has contravariant order and retains the factor N.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3; S4 A1b. -/
theorem denominator_clearing {A B : Variety} (f : Hom A B)
    (hs : Function.Surjective (Point.map f.hom)) :
    ∃ (N : ℕ) (s : Hom B A), 0 < N ∧
      s.hom ≫ f.hom = (multiplication B N).hom ∧
      (homPullback s.hom 1).comp (homPullback f.hom 1) =
        (N : ℚ) • (LinearMap.id : HQ B.X 1 →ₗ[ℚ] HQ B.X 1) :=
  denominator_clearing_aux f hs

end HodgeLean.Foundations.AbelianQuotient
