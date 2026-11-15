import HodgeLean.Ported.Hironaka.Scheme.Modules.IdealSheafFinite

/-! Passage from module generators of an ideal sheaf to ideal generators. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Generators of the section module give generators of the ideal of functions. -/
theorem g32l4_ideal_module_generators {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) {K : Type} (g : K → Γ(I.toModules, U))
    (hg : Submodule.span Γ(X, U) (Set.range g) = ⊤) :
    Ideal.span (Set.range (fun k => (I.toModulesSectionsEquiv U (g k) : Γ(X, U)))) =
      I.ideal U := by
  let e := I.toModulesSectionsEquiv U
  have he : Submodule.span Γ(X, U) (Set.range (fun k => e (g k))) = ⊤ := by
    have h := congrArg (Submodule.map e.toLinearMap) hg
    rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective] at h
    exact h
  have h := congrArg (Submodule.map (I.ideal U).subtype) he
  rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
    Submodule.range_subtype] at h
  exact h

end HodgeLean.Foundations.Program
