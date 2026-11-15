import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexCapScalar

/-! # Original local complex caps linear in the actual normal coclass -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original local cap between actual ambient and intrinsic local homology, linear in the original normal support cohomology class.
Source: Hatcher, Algebraic Topology, section 3.3, bilinearity of relative cap products.
HC no distance; AV milestone no distance. -/
def properCycle_complex_product_local_cap (r d : ℕ) :
    RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of ((Fin r → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' ({0} : Set (Fin d → ℂ))ᶜ)) (2 * d) →ₗ[ℚ]
      (orientationGroup (TopCat.of ((Fin r → ℂ) × (Fin d → ℂ))) (2 * (r + d)) (0, 0) →ₗ[ℚ]
        orientationGroup (TopCat.of (Fin r → ℂ)) (2 * r) 0) := by
  let E := Fin r → ℂ
  let F := Fin d → ℂ
  let X := TopCat.of (E × F)
  let eN : orientationGroup X (2 * (r + d)) (0, 0) ≅
      orientationGroup X (2 * d + 2 * r) (0, 0) :=
    eqToIso (congrArg (fun n => orientationGroup X n (0, 0)) (by omega))
  let eS := properCycle_product_triad_local_homology_iso E F (2 * d + 2 * r)
  let eT := properCycle_product_tangent_local_homology_iso E F (2 * r)
  let f := eS.inv.hom.comp eN.hom.hom
  let K := triadCapCohomologyLinear ℚ X
    (Prod.snd ⁻¹' ({0} : Set F)ᶜ) {z | z.1 = 0}ᶜ (2 * d) (2 * r)
  refine
    { toFun := fun a => eT.hom.hom.comp ((K a).comp f)
      map_add' := ?_
      map_smul' := ?_ }
  · intro a b
    ext c
    change eT.hom.hom ((K (a + b)) (f c)) =
      eT.hom.hom ((K a) (f c)) + eT.hom.hom ((K b) (f c))
    rw [map_add, LinearMap.add_apply, map_add]
  · intro t a
    ext c
    change eT.hom.hom ((K (t • a)) (f c)) = t • eT.hom.hom ((K a) (f c))
    rw [map_smul, LinearMap.smul_apply, map_smul]

/-- Applying the original variable-class local cap to the original projected normalized normal coclass recovers the specified standard local cap exactly.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_product_local_cap_standard (r d : ℕ) :
    properCycle_complex_product_local_cap r d
      (relativeCohomologyMap ℚ (2 * d)
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d))) =
      properCycle_standard_complex_local_cap r d := rfl

/-- A literal multiplicity in the original projected normal coclass gives that multiplicity times the actual common cap scalar on the original intrinsic orientation.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.3, cap bilinearity.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_product_local_cap_multiplicity (r d : ℕ) (m : ℚ) :
    properCycle_complex_product_local_cap r d
      (m • relativeCohomologyMap ℚ (2 * d)
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d)))
      (properCycle_complex_product_standard_orientation r d) =
        (m * properCycle_standard_complex_cap_scalar r d) • standardComplexLocalClass ℚ r := by
  rw [map_smul, LinearMap.smul_apply, properCycle_complex_product_local_cap_standard,
    ← properCycle_standard_complex_cap_scalar_formula, smul_smul]

/-- A nonzero actual normal multiplicity gives a nonzero original ambient-to-intrinsic local cap value.
Source: Fulton, Intersection Theory, section 19.1; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_product_local_cap_multiplicity_ne_zero
    (r d : ℕ) (m : ℚ) (hm : m ≠ 0) :
    properCycle_complex_product_local_cap r d
      (m • relativeCohomologyMap ℚ (2 * d)
        (properCycle_product_support_projection (Fin r → ℂ) (TopCat.of (Fin d → ℂ)) {0})
        (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
          (standardComplexLocalClass_ne_zero_for_chart d)))
      (properCycle_complex_product_standard_orientation r d) ≠ 0 := by
  rw [properCycle_complex_product_local_cap_multiplicity]
  exact smul_ne_zero (mul_ne_zero hm (properCycle_standard_complex_cap_scalar_ne_zero r d))
    (standardComplexLocalClass_ne_zero_for_chart r)

end HodgeLean.Foundations.QuotientDuality
