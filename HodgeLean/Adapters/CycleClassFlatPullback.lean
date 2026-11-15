import HodgeLean.Adapters.CycleClassFlatPullbackProofs

/-! # Smooth sum maps and constructed flat inverse-image cycles

The smoothness statements isolate the geometric inputs. Cycle coefficients use generic
lengths of the actual scheme-theoretic inverse image. Comparison with singular cohomology
requires further ambient supported-class maps. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Source: Stacks Project, Tags 054K (Chevalley) and 01T9 (Jacobson schemes and finite-type points). -/
theorem ccm3_points_surjective {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z)
    (hf : Function.Surjective (Point.map f)) :
    Surjective f.left ∧ IsDominant f.left :=
  ccm3_points_surjective_aux f hf

/-- Source: Hartshorne, Algebraic Geometry, III.10.7 (generic smoothness), applied on the regular locus of the source; Jacobson closed points on a nonempty open. -/
theorem ccm3_exists_relative_smooth_point {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [IsIntegral Z.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [LocallyOfFinitePresentation f.left] [IsDominant f.left] :
    ∃ p : ComplexPoint X, p.left (IsLocalRing.closedPoint ℂ) ∈ f.left.smoothLocus :=
  ccm3_exists_relative_smooth_point_aux f

/-- Source: Mathlib CategoryTheory.GrpObj.mulRight; Stacks Project, Tag 01V4, smoothness invariant under isomorphisms. -/
theorem ccm3_translation_smoothLocus {X Z : Over (Spec ↧ℂ)}
    [GrpObj X] [GrpObj Z] (f : X ⟶ Z) [IsMonHom f]
    [LocallyOfFinitePresentation f.left] (p : ComplexPoint X) (x : X.left) :
    (GrpObj.mulRight p).hom.left x ∈ f.left.smoothLocus ↔ x ∈ f.left.smoothLocus :=
  ccm3_translation_smoothLocus_aux f p x

/-- Source: Mathlib Scheme.Hom.isOpen_smoothLocus and nonempty_inter_closedPoints; the closed-point test on a Jacobson scheme. -/
theorem ccm3_smooth_of_complex_points {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (f : X ⟶ Z) [LocallyOfFinitePresentation f.left]
    (h : ∀ p : ComplexPoint X, p.left (IsLocalRing.closedPoint ℂ) ∈ f.left.smoothLocus) :
    Smooth f.left :=
  ccm3_smooth_of_complex_points_aux f h

/-- Source: Assembly of ccm3_points_surjective, ccm3_exists_relative_smooth_point, ccm3_translation_smoothLocus and ccm3_smooth_of_complex_points. -/
theorem ccm3_smooth_surjective_group_hom {X Z : Over (Spec ↧ℂ)}
    [GrpObj X] [GrpObj Z] [IsIntegral X.left] [IsIntegral Z.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsMonHom f]
    (hf : Function.Surjective (Point.map f)) : Smooth f.left :=
  ccm3_smooth_surjective_group_hom_aux f hf

/-- Source: ccm3_smooth_surjective_group_hom and ccm2_pwSumMap_surjective_of_ne_zero. -/
theorem ccm3_pwSumMap_smooth_of_ne_zero {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Smooth (P.pwSumMap θ a).left :=
  ccm3_pwSumMap_smooth_of_ne_zero_aux P θ a ha

section StageTwoRestatement
variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}

/-- Stage 2's smoothness statement, with exactly the same binders and conclusion.
Source: `ccm3_pwSumMap_smooth_of_ne_zero`. -/
theorem ccm3_ccm2_pwSumMap_smooth_of_ne_zero (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (ha : a ≠ 0) :
    Smooth (P.pwSumMap θ a).left :=
  ccm3_pwSumMap_smooth_of_ne_zero P θ a ha

end StageTwoRestatement

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_genericLength_finite_pos {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    0 < ccm3_genericLength f.left x y ∧ ccm3_genericLength f.left x y < ⊤ :=
  ccm3_genericLength_finite_pos_aux f x y hy

/-- Source: Mathlib NoetherianSpace.finite_irreducibleComponents; unique generic points of irreducible closed subsets of schemes. -/
theorem ccm3_inverse_components_finite {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    Set.Finite {y : (ccm3_inverseIdeal f.left x).subscheme |
      closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
        irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme} :=
  ccm3_inverse_components_finite_aux f x

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_coeff {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (y : (ccm3_inverseIdeal f.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme) :
    ccm3_flatPullbackPrime f.left x ((ccm3_inverseIdeal f.left x).subschemeι y) =
      ((ccm3_genericLength f.left x y).toNat : ℚ) :=
  ccm3_flatPullbackPrime_coeff_aux f x y hy

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_support {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (z : X.left) :
    ccm3_flatPullbackPrime f.left x z ≠ 0 ↔
      ∃ y : (ccm3_inverseIdeal f.left x).subscheme,
        (ccm3_inverseIdeal f.left x).subschemeι y = z ∧
        closure ({y} : Set (ccm3_inverseIdeal f.left x).subscheme) ∈
          irreducibleComponents (ccm3_inverseIdeal f.left x).subscheme :=
  ccm3_flatPullbackPrime_support_aux f x z

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullbackPrime_ne_zero {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Surjective f.left] (x : Z.left) :
    ccm3_flatPullbackPrime f.left x ≠ 0 :=
  ccm3_flatPullbackPrime_ne_zero_aux f x

/-- Source: Fulton, Intersection Theory, second edition, §1.7, flat inverse-image dimension formula; Stacks Project, Lemma 42.13.1. -/
theorem ccm3_flatPullbackPrime_codimension {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [IsIntegral X.left] [IsIntegral Z.left]
    [Flat f.left] (q : ℕ) (x : Z.left) (hx : Order.coheight x = q)
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    Order.coheight z = q :=
  ccm3_flatPullbackPrime_codimension_aux f q x hx z hz

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullback_add {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (c d : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c + d) =
      ccm3_flatPullback f.left c + ccm3_flatPullback f.left d :=
  ccm3_flatPullback_add_aux f c d

/-- Source: Fulton, Intersection Theory, second edition, §1.5 (fundamental cycle) and §1.7 (flat pullback); Stacks Project, Definition 42.14.1 (Tag 02RA). -/
theorem ccm3_flatPullback_id {X : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (c : AlgebraicCycle X.left ℚ) :
    ccm3_flatPullback (𝟙 X.left) c = c :=
  ccm3_flatPullback_id_aux c

end HodgeLean.Adapters
