import HodgeLean.Foundations.Program.G32Native.EulerModel.Hyperplane
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

/-! # Exact literal subscheme cycles under the supplied ambient isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual ambient isomorphism sends the literal pulled-back integral subscheme to the original coefficient-one component cycle. -/
theorem subscheme_comap_componentCycle {Q P : Over (Spec ↧ℂ)}
    (e : Q ≅ P) (I : P.left.IdealSheafData)
    [IsIntegral (s2c_subscheme P I).left]
    [IsIntegral (s2c_subscheme Q (I.comap e.hom.left)).left] :
    s2e_componentCycle (s2c_subschemeι Q (I.comap e.hom.left) ≫ e.hom) ℚ =
      s2e_componentCycle (s2c_subschemeι P I) ℚ := by
  let j := s2c_subschemeι Q (I.comap e.hom.left)
  let g := s2c_subschemeι P I
  let f := j ≫ e.hom
  letI : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion (I.comap e.hom.left).subschemeι)
  letI : IsClosedImmersion g.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  letI : IsClosedImmersion f.left := by
    change IsClosedImmersion (j.left ≫ e.hom.left)
    infer_instance
  have hrange : Set.range f.left = Set.range g.left := by
    change Set.range (e.hom.left ∘ (I.comap e.hom.left).subschemeι) =
      Set.range I.subschemeι
    rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    change e.hom.left '' (e.hom.left ⁻¹' I.support.carrier) = I.support.carrier
    exact Set.image_preimage_eq _ e.hom.left.homeomorph.surjective
  have hp : f.left (genericPoint (s2c_subscheme Q (I.comap e.hom.left)).left) =
      g.left (genericPoint (s2c_subscheme P I).left) :=
    IsGenericPoint.eq (s2e_componentCycle_closure f)
      ((s2e_componentCycle_closure g).trans hrange.symm)
  change s2e_componentCycle f ℚ = s2e_componentCycle g ℚ
  simp only [s2e_componentCycle, hp]

#print axioms subscheme_comap_componentCycle
end HodgeLean.Foundations.Program.G32Native.EulerModel
