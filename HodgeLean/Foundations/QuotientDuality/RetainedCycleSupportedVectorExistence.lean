import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedChainNonvanishing
import HodgeLean.Foundations.QuotientDuality.RetainedCycleTriangulatedCap
import HodgeLean.Foundations.QuotientDuality.ProperCycleMiddleSupportIdentification

/-! # Supported vectors from actual ambient singular images -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero ambient image of actual support homology supplies a nonzero original supported cohomology vector. -/
theorem retained_supported_vector_of_nonzero_ambient_image
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ y ∈ γ.support, Order.coheight y = k)
    (c : Homology ℚ (a3b4_an X.hom) (2*k+2*k))
    (ho : ∀ x, Function.Bijective (orientationLine (a3b4_an X.hom) (2*k+2*k) c x))
    (hv : ∀ j : ℕ, j ≠ 2*k+2*k → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    (z : Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k))
    (hz : homologyMap ℚ (2*k) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ)).map z ≠ 0) :
    ∃ a : s2e_supportedClass X γ k, a ≠ 0 := by
  letI : T2Space (a3b4_an X.hom) := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : CompactSpace (a3b4_an X.hom) := inferInstanceAs (CompactSpace (ComplexPoint X))
  let S : Closeds (a3b4_an X.hom) :=
    ⟨a3b4_cycleSupport X.hom γ, a3b4a_classSupport_isClosed X.hom γ⟩
  let e := properCycle_middle_support_identification_aux X k hk hdim γ hc
  let f := properCycle_derived_support_chain_class_map (a3b4_an X.hom) S
    (2*k+2*k) c ho hv (2*k)
  have hn := retained_derived_support_chain_class_nonzero_in_window (a3b4_an X.hom)
    (retainedProjectiveTriangulation X) (2*k+2*k)
    (retainedGlobalLocalOrientation (a3b4_an X.hom) _ c ho hv) S c ho hv (2*k)
    (by omega) z hz
  refine ⟨e.hom.hom (f.hom z), ?_⟩
  intro h
  exact hn ((ConcreteCategory.bijective_of_isIso e.hom).1 (h.trans (map_zero _).symm))

end HodgeLean.Foundations.QuotientDuality
