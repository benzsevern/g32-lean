import HodgeLean.Foundations.AbelianQuotient.QuotientCohomology
import HodgeLean.Foundations.AbelianQuotient.H1Helpers
import HodgeLean.Foundations.AbelianQuotient.SurjectiveSection
import HodgeLean.Foundations.AbelianQuotient.ImageGroup
import HodgeLean.Foundations.AbelianQuotient.ComplementConstruction
import HodgeLean.Foundations.AbelianQuotient.QuotientConstruction
import HodgeLean.Foundations.AbelianQuotient.QuotientUniversal

/-! # Abelian quotient first-stage proof obligations

Seven geometric statements for subsequent proof work.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.AbelianQuotient
/-- The canonical scheme image inherits an abelian variety structure; its factor is onto.
Source: Mumford, *Abelian Varieties*, §8; Birkenhake–Lange, §2.4. -/
theorem connected_image_aux {A B : Variety} (f : Hom A B) :
    ∃ G : GrpObj (imageModel f),
      letI := G
      IsCommMonObj (imageModel f) ∧ IsIntegral (imageModel f).left ∧
      Smooth (imageModel f).hom ∧ IsProjective (imageModel f).hom ∧
      IsMonHom (imageFactor f) ∧ IsMonHom (imageInclusion f) ∧
      Function.Surjective (Point.map (imageFactor f)) := by
  exact canonical_image_abelian f

/-- The quotient is an actual abelian variety with the expected kernel and universal property.
Source: Mumford, *Abelian Varieties*, §§7–8; Birkenhake–Lange, §5.3. -/
theorem quotient_exists_aux {A : Variety} (S : Subvariety A) :
    ∃ q : Projection S,
      Function.Surjective (Point.map q.map.hom) ∧
      {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
        Set.range (Point.map S.inclusion.hom) ∧
      ∀ (T : Variety) (f : Hom A T), S.inclusion.hom ≫ f.hom = (1 : S.B.X ⟶ T.X) →
        ∃! g : Hom q.Q T, q.map.hom ≫ g.hom = f.hom := by
  obtain ⟨q, hs, hk, ψ, hψs, hψ⟩ := exists_quotient_geometry S
  refine ⟨q, hs, hk, ?_⟩
  intro T f hf
  exact factor_unique_of_period_surjective S q.map hs hk ψ hψs hψ T f hf

/-- Rational H¹ of the quotient identifies with the kernel of restriction to the subvariety.
Source: Birkenhake–Lange, §§2.4, 5.3; Mumford, *Abelian Varieties*, §8. -/
theorem quotient_h1_aux {A : Variety} {S : Subvariety A} (q : Projection S)
    (hs : Function.Surjective (Point.map q.map.hom))
    (hk : {a : ComplexPoint A.X | Point.map q.map.hom a = 1} =
      Set.range (Point.map S.inclusion.hom)) :
    Function.Injective (homPullback q.map.hom 1) ∧
      LinearMap.range (homPullback q.map.hom 1) =
        LinearMap.ker (homPullback S.inclusion.hom 1) := by
  refine ⟨injective_pullback_of_surjective q.map hs,
    le_antisymm (quotient_range_le_kernel q hk) (quotient_kernel_le_range q hs hk)⟩

/-- Injective rational H¹ pullback forces geometric surjectivity.
Source: Birkenhake–Lange, §§2.4, 5.3; S4 contract A1a9. -/
theorem surjective_of_injective_h1_aux {A B : Variety} (f : Hom A B)
    (hi : Function.Injective (homPullback f.hom 1)) :
    Function.Surjective (Point.map f.hom) := by
  obtain ⟨L, hL⟩ := spec_abelianHom_analyticRepresentation f.hom
  have hsurj := analytic_surjective_of_injective_pullback f hi L hL
  intro q
  obtain ⟨w, hw⟩ := surjective_complexExponential B.X (TopologicalSpace.dim B.X.left)
    (Additive.ofMul q)
  obtain ⟨v, rfl⟩ := hsurj w
  refine ⟨Additive.toMul (complexExponential A.X (TopologicalSpace.dim A.X.left) v), ?_⟩
  rw [← hL, hw]
  rfl

/-- Poincaré reducibility: the sum with a complementary abelian subvariety is an isogeny.
Projectivity in `Variety` supplies polarizability; this is not a statement for general tori.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3. -/
theorem complement_exists_aux {A : Variety} (S : Subvariety A) :
    ∃ T : Subvariety A, ccm2_IsogenyOnPoints (additionMap S T) := by
  exact exists_complementary_subvariety S

set_option maxRecDepth 2000 in
/-- An isogeny has an algebraic fraction inverse with both multiplication identities.
The associated rational H¹ actions are mutual inverses.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3. -/
theorem rational_inverse_aux {A B : Variety} (f : Hom A B) (hi : ccm2_IsogenyOnPoints f.hom) :
    ∃ g : FractionHom B A,
      g.numerator.hom ≫ f.hom = (multiplication B g.denominator).hom ∧
      f.hom ≫ g.numerator.hom = (multiplication A g.denominator).hom ∧
      (homPullback f.hom 1).comp (rationalPullback g) = LinearMap.id ∧
      (rationalPullback g).comp (homPullback f.hom 1) = LinearMap.id := by
  obtain ⟨N, g, hN, hgf, hfg⟩ := integral_inverse A B f.hom inferInstance hi
  refine ⟨⟨g, N, hN⟩, hgf, hfg, ?_, ?_⟩
  · change (homPullback f.hom 1).comp ((N : ℚ)⁻¹ • homPullback g.hom 1) = _
    rw [LinearMap.comp_smul, ← spec_homPullback_comp, hfg]
    rw [multiplication_nat_hom]
    change (N : ℚ)⁻¹ • homPullback ((𝟙 A.X) ^ (N : ℤ)) 1 = _
    rw [spec_homPullback_zpow, spec_homPullback_id, smul_smul]
    simp only [Int.cast_natCast]
    rw [inv_mul_cancel₀ (show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne'), one_smul]
  · change ((N : ℚ)⁻¹ • homPullback g.hom 1).comp (homPullback f.hom 1) = _
    rw [LinearMap.smul_comp, ← spec_homPullback_comp, hgf]
    rw [multiplication_nat_hom]
    change (N : ℚ)⁻¹ • homPullback ((𝟙 B.X) ^ (N : ℤ)) 1 = _
    rw [spec_homPullback_zpow, spec_homPullback_id, smul_smul]
    simp only [Int.cast_natCast]
    rw [inv_mul_cancel₀ (show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne'), one_smul]

/-- A surjective algebraic homomorphism has a positive integral multiplication section.
The pullback equation has contravariant order and retains the factor N.
Source: Mumford, *Abelian Varieties*, §19; Birkenhake–Lange, §5.3; S4 A1b. -/
theorem denominator_clearing_aux {A B : Variety} (f : Hom A B)
    (hs : Function.Surjective (Point.map f.hom)) :
    ∃ (N : ℕ) (s : Hom B A), 0 < N ∧
      s.hom ≫ f.hom = (multiplication B N).hom ∧
      (homPullback s.hom 1).comp (homPullback f.hom 1) =
        (N : ℚ) • (LinearMap.id : HQ B.X 1 →ₗ[ℚ] HQ B.X 1) := by
  obtain ⟨N, s, hN, h⟩ := exists_multiplication_section f hs
  exact ⟨N, s, hN, h, multiplication_section_pullback f s N h⟩

end HodgeLean.Foundations.AbelianQuotient
