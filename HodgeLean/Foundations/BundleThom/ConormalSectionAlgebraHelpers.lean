import HodgeLean.Foundations.BundleThom.AnalyticNormalDefs

/-! # Algebra of conormal section specialization

Specialization retains addition of actual local algebraic sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.BundleThom

/-- Specialization of local conormal sections is additive.
Source: Hartshorne, Algebraic Geometry, II.5, pullback and specialization of module sections. -/
def i1_conormalSectionSpecialization {Q : Over (Spec ↧ℂ)} {V : Scheme}
    (j : Q.left ⟶ V) (U : Q.left.Opens) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen U) :
    (SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.sheaf j)) →+ i1_conormalFibre j x where
  toFun s := i1_conormalSectionValue j U s x hx
  map_zero' := by
    simp only [i1_conormalSectionValue, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]
    rfl
  map_add' s t := by
    simp only [i1_conormalSectionValue, Functor.map_add, Preadditive.comp_add,
      Preadditive.add_comp]
    rfl

/-- Every local regular coefficient is continuous on its analytic open domain.
Source: Hartshorne, Algebraic Geometry, II.2, regular functions; analytic evaluation topology. -/
theorem i1_regularEvaluation_continuous (Q : Over (Spec ↧ℂ)) (U : Q.left.Opens)
    (s : Γ(Q.left, U)) :
    Continuous (fun x : (Point.overOpen U : Set (ComplexPoint Q)) =>
      Point.evaluate U s x.1) := by
  apply continuous_def.mpr
  intro O hO
  have heq : (fun x : (Point.overOpen U : Set (ComplexPoint Q)) =>
        Point.evaluate U s x.1) ⁻¹' O =
      Subtype.val ⁻¹' (Point.overOpen U ∩ Point.evaluate U s ⁻¹' O) := by
    ext x
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  rw [heq]
  exact (Point.isOpen_overOpen_inter_preimage U s O hO).preimage continuous_subtype_val

end HodgeLean.Foundations.BundleThom
