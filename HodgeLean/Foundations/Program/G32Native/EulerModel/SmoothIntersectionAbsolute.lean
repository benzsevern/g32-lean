import HodgeLean.Foundations.Program.G32Native.EulerModel.SmoothIntersection

/-! # Absolute classes of smooth proper intersections -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- A smooth proper intersection of generic length one represents the actual cup product. -/
theorem smooth_intersection_cycleClass
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (h : 2 * p + 2 * q = 2 * (p + q)) (x y : X.left)
    (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (hsm : ∀ v : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) →
      (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι v ∉
          (cycleComponentSingularAmbientClosedFiltration X y 0 : Set X.left) →
      v ∈ ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι ≫ X.hom).smoothLocus)
    (hlength : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x) (ccm3_primeIdeal X.left y) w = 1)
    (hregular : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X x 0 : Set X.left) ∧
      (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w ∉
          (cycleComponentSingularAmbientClosedFiltration X
            y 0 : Set X.left))
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (hsupport : ∀ w : (ccm3_primeIdeal X.left x ⊔
      ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subschemeι w) ≤
        cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X y) :
    (cupProductOf X).cup h (cycleComponentSheafClass X x hx)
      (cycleComponentSheafClass X y hy) =
        ccm3_cycleClass X (p + q) (hc9k_primeIntersectionCycle X x y) := by
  rw [← hc9k_forget_supported_intersectionCycle_aux X p q x y hcodim hsupport]
  have hcast (S : Closeds (ComplexPoint X)) {i j k : ℕ} (h : i + j = k)
      (a : HQ X i) (b : HQ X j)
      (u : H_[S]^(i + j)(X; ℚ)) (v : H_[S]^k(X; ℚ)) (huv : u = h.symm ▸ v)
      (hab : (HQ.linearEquiv X (i + j)).symm (forgetSupport ℚ X S (i + j) u) =
        (cupProductOf X).cup rfl a b) :
      (cupProductOf X).cup h a b = (HQ.linearEquiv X k).symm (forgetSupport ℚ X S k v) := by
    subst h huv
    exact hab.symm
  exact hcast _ h _ _ _ _
    (smooth_supported_intersection_product X p q h x y hx hy hsm hlength hregular hcodim hsupport)
    (ccm16_supportedCup_forget X _ _ (2 * p) (2 * q) _ _)

#print axioms smooth_intersection_cycleClass
/-- Every component of a scheme intersection has analytic support in both factors. -/
theorem intersection_component_support_le
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left) (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) :
    cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y := by
  have hmem : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w ∈
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).support : Set X.left) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rw [Scheme.IdealSheafData.support_sup] at hmem
  obtain ⟨hx, hy⟩ := hmem
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({x} : Set X.left), isClosed_closure⟩).support : Set X.left) at hx
  change _ ∈ ((Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ({y} : Set X.left), isClosed_closure⟩).support : Set X.left) at hy
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hx hy
  intro a ha
  change Point.underlying a ∈ closure ({_} : Set X.left) at ha
  constructor
  · change Point.underlying a ∈ closure ({x} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure ha
  · change Point.underlying a ∈ closure ({y} : Set X.left)
    exact closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure ha


#print axioms intersection_component_support_le
end HodgeLean.Foundations.Program.G32Native.EulerModel
