import HodgeLean.Foundations.Program.SchoenCycleU1NativeCurveJets

/-! # Actual scheme stalk jets along native coordinate curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexPoint Filter Topology TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

/-- The native coordinate curve gives a dual-number map on every actual
regular section ring near its base point.
Source: Hartshorne, Algebraic Geometry, II.8; HodgeConjecture,
`analyticAt_localChart_symm_evaluate`. -/
def s2e_u1_nativeSectionJet
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hp : p.underlying ∈ U) : Γ(Z.left, U) →+* DualNumber ℂ := by
  letI := s2e_step1_sectionAlgebra Z U
  exact (s2e_u1_sectionJetAlong Z U (s2e_u1_nativeCurve Z p)
    (s2e_u1_nativeCurve_regular_sections Z p U hp).1
    (s2e_u1_nativeCurve_regular_sections Z p U hp).2).toRingHom

/-- Native section jets agree under the actual restriction maps.
Source: Hartshorne, Algebraic Geometry, II.2, restriction of regular functions. -/
theorem s2e_u1_nativeSectionJet_res
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U V : Z.left.Opens) (hVU : V ≤ U) (hp : p.underlying ∈ V)
    (s : Γ(Z.left, U)) :
    s2e_u1_nativeSectionJet Z p V hp ((Z.left.presheaf.map (homOfLE hVU).op).hom s) =
      s2e_u1_nativeSectionJet Z p U (hVU hp) s := by
  change s2e_u1_analyticGermJet (s2e_u1_analyticGerm _
      ((s2e_u1_nativeCurve_regular_sections Z p V hp).2 _)) =
    s2e_u1_analyticGermJet (s2e_u1_analyticGerm _
      ((s2e_u1_nativeCurve_regular_sections Z p U (hVU hp)).2 s))
  congr 1
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards [(s2e_u1_nativeCurve_regular_sections Z p V hp).1] with t ht
  exact (Point.evaluate_res hVU s (s2e_u1_nativeCurve Z p t) ht).symm

/-- The section jets form a cocone over all actual Zariski neighbourhoods.
Source: Hartshorne, Algebraic Geometry, II.2, the stalk as a direct limit. -/
def s2e_u1_nativeStalkJetCocone
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z) :
    Cocone ((OpenNhds.inclusion p.underlying).op ⋙ Z.left.presheaf) where
  pt := CommRingCat.of (DualNumber ℂ)
  ι :=
    { app := fun U => CommRingCat.ofHom
        (s2e_u1_nativeSectionJet Z p U.unop.val U.unop.property)
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        ext s
        exact s2e_u1_nativeSectionJet_res Z p U.unop.val V.unop.val
          i.unop.le V.unop.property s }

/-- The native curve gives an actual ring map from the scheme local ring to
complex dual numbers.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8, local tangent vectors. -/
def s2e_u1_nativeStalkJet
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z) :
    Z.left.presheaf.stalk p.underlying →+* DualNumber ℂ :=
  (colimit.desc _ (s2e_u1_nativeStalkJetCocone Z p)).hom

/-- The actual scheme stalk map recovers the native Taylor jet of a regular section.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_nativeStalkJet_germ
    (Z : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Z.hom] (p : ComplexPoint Z)
    (U : Z.left.Opens) (hp : p.underlying ∈ U) (s : Γ(Z.left, U)) :
    s2e_u1_nativeStalkJet Z p ((Z.left.presheaf.germ U p.underlying hp).hom s) =
      s2e_u1_nativeSectionJet Z p U hp s := by
  change ((Z.left.presheaf.germ U p.underlying hp) ≫
    colimit.desc _ (s2e_u1_nativeStalkJetCocone Z p)).hom s = _
  erw [colimit.ι_desc]
  rfl

end HodgeLean.Foundations.Program
