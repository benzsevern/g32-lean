import HodgeLean.Foundations.Program.SchoenCycleU1AnalyticJet
import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Analytic section germs along actual complex-point curves -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- Regular sections evaluated along an analytic curve define a ring map to
analytic germs. The curve is required to stay in the specified open near zero.
Source: Hartshorne, Algebraic Geometry, II.2; Serre, GAGA, section 2. -/
def s2e_u1_sectionGermAlong (X : Over (Spec ↧ℂ)) (U : X.left.Opens)
    (c : ℂ → ComplexPoint X)
    (hU : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ U)
    (hc : ∀ s : Γ(X.left, U), AnalyticAt ℂ (fun z => Point.evaluate U s (c z)) 0) :
    Γ(X.left, U) →+* s2e_u1_analyticGermRing where
  toFun s := s2e_u1_analyticGerm (fun z => Point.evaluate U s (c z)) (hc s)
  map_zero' := by
    apply Subtype.ext
    change ((fun z => Point.evaluate U 0 (c z)) : Germ (𝓝 (0 : ℂ)) ℂ) =
      ((fun _ : ℂ => (0 : ℂ)) : Germ (𝓝 (0 : ℂ)) ℂ)
    apply Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp [Point.evaluate, hz]
  map_one' := by
    apply Subtype.ext
    change ((fun z => Point.evaluate U 1 (c z)) : Germ (𝓝 (0 : ℂ)) ℂ) =
      ((fun _ : ℂ => (1 : ℂ)) : Germ (𝓝 (0 : ℂ)) ℂ)
    apply Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp [Point.evaluate, hz]
  map_add' s t := by
    apply Subtype.ext
    change ((fun z => Point.evaluate U (s + t) (c z)) : Germ (𝓝 (0 : ℂ)) ℂ) =
      ((fun z => Point.evaluate U s (c z) + Point.evaluate U t (c z)) : Germ (𝓝 (0 : ℂ)) ℂ)
    apply Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp [Point.evaluate, hz]
  map_mul' s t := by
    apply Subtype.ext
    change ((fun z => Point.evaluate U (s * t) (c z)) : Germ (𝓝 (0 : ℂ)) ℂ) =
      ((fun z => Point.evaluate U s (c z) * Point.evaluate U t (c z)) : Germ (𝓝 (0 : ℂ)) ℂ)
    apply Germ.coe_eq.mpr
    filter_upwards [hU] with z hz
    simp [Point.evaluate, hz]

/-- Pulling back regular functions and then taking curve germs agrees with
mapping the actual complex-point curve first.
Source: Hartshorne, Algebraic Geometry, II.2; Serre, GAGA, section 2. -/
theorem s2e_u1_sectionGermAlong_map
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (V : Y.left.Opens)
    (c : ℂ → ComplexPoint X)
    (hV : ∀ᶠ z in 𝓝 (0 : ℂ), (c z).underlying ∈ f.left ⁻¹ᵁ V)
    (hc : ∀ s : Γ(X.left, f.left ⁻¹ᵁ V),
      AnalyticAt ℂ (fun z => Point.evaluate (f.left ⁻¹ᵁ V) s (c z)) 0)
    (hd : ∀ s : Γ(Y.left, V),
      AnalyticAt ℂ (fun z => Point.evaluate V s (Point.map f (c z))) 0) :
    (s2e_u1_sectionGermAlong X (f.left ⁻¹ᵁ V) c hV hc).comp (f.left.app V).hom =
      s2e_u1_sectionGermAlong Y V (fun z => Point.map f (c z))
        (by
          filter_upwards [hV] with z hz
          change f.left (c z).underlying ∈ (V : Set Y.left)
          exact hz) hd := by
  ext s
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall (fun z => (Point.evaluate_map f V s (c z)).symm)

end HodgeLean.Foundations.Program
