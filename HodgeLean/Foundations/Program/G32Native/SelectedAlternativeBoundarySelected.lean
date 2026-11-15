import HodgeLean.Foundations.Program.G32Native.SelectedAlternativeBoundaryAudit

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Retain the selected J, group structure and action simultaneously at every parameter. -/
theorem selectedAlternative_cover_transport {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∀ t : b6t_polydisc c,
      let X := Classical.choose (g32y_cover_spec D t hg B)
      X.J = g32x_J D t ∧
      HEq X.grp (inferInstance : GrpObj (g32x_J D t)) ∧
      HEq X.aut (fun a ↦ ((Classical.choose (g32x_deck_realization D t)) a).hom) := by
  intro t
  exact Classical.choose_spec (g32y_cover_spec D t hg B)

/-- The U17 and T14 outputs give hS for the migrated selected family. -/
theorem selectedAlternative_hS {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    let X := fun t : b6t_polydisc c ↦ Classical.choose (g32y_cover_spec D t hg B)
    (by_elab do
      let xt ← Lean.Elab.Term.elabTerm (Lean.mkIdent `X) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let xt ← Lean.instantiateMVars xt
      let family ← Lean.Meta.forallTelescopeReducing (← Lean.Meta.inferType xt) fun ts _ => do
        if ts.size != 1 then throwError "Expected a selected family with one parameter; got {← Lean.Meta.inferType xt}"
        let supplier ← Lean.Meta.mkAppM ``g32p_SchoenSupplier #[Lean.mkApp xt ts[0]!]
        Lean.Meta.mkForallFVars ts supplier
      Lean.Meta.forallTelescope family fun ts _ => do
        let f ← Lean.Meta.mkAppM ``selectedAlternative_supplier #[Lean.mkApp xt ts[0]!]
        let ty ← Lean.Meta.inferType f
        let u := ty.bindingDomain!
        let t := ty.bindingBody!.bindingDomain!
        let hu ← Lean.Meta.mkForallFVars ts u
        let ht ← Lean.Meta.mkForallFVars ts t
        Lean.mkArrow hu (← Lean.mkArrow ht family)) := by
  intro X hU17 hT14 t
  exact selectedAlternative_supplier (X t) (hU17 t) (hT14 t)

#print axioms selectedAlternative_cover_transport
#print axioms selectedAlternative_hS
end HodgeLean.Foundations.Program
