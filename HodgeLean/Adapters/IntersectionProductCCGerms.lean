import HodgeLean.Adapters.IntersectionProductCCSupport

/-! # Detection of supported intersection coefficients by local germs -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
/-- Integer component coefficients of a supported class are determined on smooth component
points away from the other components.
Source: `hc9k_supportedClass_eq_of_generic_germs` and generic smoothness. -/
theorem a3cc_supportedIntersectionSum_eq_of_germs (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) = r)
    (m : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme → ℤ)
    (u : H_[cycleComponentAnalyticClosedSupport X x ⊓
      cycleComponentAnalyticClosedSupport X y]^(2 * r)(X; ℚ))
    (hlocal : ∀ (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
      (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
      (a : ComplexPoint X),
      a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) →
      (∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
        closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
        w' ≠ w → a ∉ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w')) →
      a ∉ cycleComponentSingularAnalyticClosedFiltration X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) 0 →
      ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * r) a u =
      m w • ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * r) a
        (supportEnlarge X (a3cc_intersection_support_le X x y w) (2 * r)
          (cycleComponentSupportedInjectiveClass X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)
            (hcodim w hw)))) :
    u = a3cc_supportedIntersectionSum X r x y hcodim (fun w => (m w : ℚ)) := by
  classical
  let I := {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
    closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme}
  let : Fintype I := (hc9k_components_finite X x y).fintype
  choose a haS hother hsing using fun c : I =>
    a3cc_exists_intersection_component_point X x y c
  refine hc9k_supportedClass_eq_of_generic_germs X I r
    (fun c => (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1)
    (fun c => hcodim c.1 c.2) _ (hc9k_support_inf_eq_iSup X x y) (2 * r) rfl a
    haS (fun c => hc9k_mem_componentBoundary_compl X I _ c (a c) (hother c) (hsing c))
    _ _ ?_
  intro c
  have ho : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      w' ≠ c.1 → a c ∉ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w') :=
    fun w' hw' hne => hother c ⟨w', hw'⟩ (fun he => hne (congrArg Subtype.val he))
  exact (hlocal c.1 c.2 (a c) (haS c) ho (hsing c)).trans
    (a3cc_supportedIntersectionSum_germ X r x y hcodim m c.1 c.2 (a c) ho).symm

end HodgeLean.Adapters
