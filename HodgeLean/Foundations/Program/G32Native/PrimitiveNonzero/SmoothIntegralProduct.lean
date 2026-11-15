import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.CoordinateClasses
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.IntersectionCycle
import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.SmoothIntersectionAbsolute

/-! # Cup products for smooth integral scheme intersections -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

/-- Smooth integral intersections of expected codimension multiply their actual component classes. -/
theorem smooth_integral_subscheme_cup
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (I J : Q.left.IdealSheafData)
    [IsIntegral I.subscheme] [IsIntegral J.subscheme] [IsIntegral (I ⊔ J).subscheme]
    [Smooth (I.subschemeι ≫ Q.hom)] [Smooth (J.subschemeι ≫ Q.hom)]
    [Smooth ((I ⊔ J).subschemeι ≫ Q.hom)]
    (p q : ℕ)
    (hI : Order.coheight (I.subschemeι (genericPoint I.subscheme)) = p)
    (hJ : Order.coheight (J.subschemeι (genericPoint J.subscheme)) = q)
    (hK : Order.coheight ((I ⊔ J).subschemeι (genericPoint (I ⊔ J).subscheme)) = p + q) :
    (cupProductOf Q).cup (by change 2 * p + 2 * q = 2 * (p + q); omega)
      (cycleComponentSheafClass Q (I.subschemeι (genericPoint I.subscheme)) hI)
      (cycleComponentSheafClass Q (J.subschemeι (genericPoint J.subscheme)) hJ) =
      cycleComponentSheafClass Q ((I ⊔ J).subschemeι (genericPoint (I ⊔ J).subscheme)) hK := by
  classical
  letI := ccm12_isNoetherian Q
  let x := I.subschemeι (genericPoint I.subscheme)
  let y := J.subschemeι (genericPoint J.subscheme)
  have hi : ccm3_primeIdeal Q.left x = I := subscheme_generic_primeIdeal Q I
  have hj : ccm3_primeIdeal Q.left y = J := subscheme_generic_primeIdeal Q J
  letI : Smooth (cycleComponentι Q.left x ≫ Q.hom) := subscheme_generic_component_smooth Q I
  letI : Smooth (cycleComponentι Q.left y ≫ Q.hom) := subscheme_generic_component_smooth Q J
  have hbI := smooth_component_boundary_zero Q x
  have hbJ := smooth_component_boundary_zero Q y
  have hcodim : ∀ w : (ccm3_primeIdeal Q.left x ⊔ ccm3_primeIdeal Q.left y).subscheme,
      closure {w} ∈ irreducibleComponents (ccm3_primeIdeal Q.left x ⊔ ccm3_primeIdeal Q.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal Q.left x ⊔ ccm3_primeIdeal Q.left y).subschemeι w) = p + q := by
    rw [hi, hj]
    intro w hw
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hw
    have he : w = genericPoint (I ⊔ J).subscheme :=
      (isGenericPoint_def.mpr hw).eq (genericPoint_spec _)
    subst w
    exact hK
  have h := smooth_intersection_cycleClass Q p q (by omega) x y hI hJ
    (by rw [hi, hj]; intro v _ _; rw [Scheme.Hom.smoothLocus_eq_top]; trivial)
    (by rw [hi, hj]; exact fun w hw => reduced_intersection_generic_length_one Q.left I J w hw)
    (by intro w hw; simp [hbI, hbJ]) hcodim
    (fun w _ => intersection_component_support_le Q x y w)
  change (cupProductOf Q).cup _ _ _ = ccm3_cycleClass Q (p + q)
    (ccm11_intersectionCycle Q.left (ccm3_primeIdeal Q.left x) (ccm3_primeIdeal Q.left y)) at h
  rw [hi, hj, integral_intersection_cycle, prime_single_cycleClass Q (p + q) _ hK, one_smul] at h
  exact h

#print axioms smooth_integral_subscheme_cup
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
