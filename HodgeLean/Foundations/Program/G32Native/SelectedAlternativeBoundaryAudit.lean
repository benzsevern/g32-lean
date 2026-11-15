import HodgeLean.Foundations.Program.G32Native.SelectedCoverSpec
import HodgeLean.Foundations.Program.SchoenTransferJ12SupplierAssembly

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry HodgeLean.Papers
namespace HodgeLean.Foundations.Program

private theorem selectedAlternative_pairList_length (L : List (ℕ × ℕ)) :
    (L.flatMap fun p => [p.1, p.2]).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

/-- Simplicity supplies a pair count for every admissible supplier. -/
theorem selectedAlternative_pair_count {A : g32t_Sixfold} (X : g32p_Cover A)
    (S : g32p_Supplier) (hS : g32p_Admissible X.aut S) :
    ∃ r : ℕ, (g32p_exponents S).length = 2 * r ∧
      ((g32p_exponents S) = [] ↔ r = 0) ∧
      ((g32p_exponents S) ≠ [] ↔ 0 < r) := by
  obtain ⟨L, hp, _⟩ := hS.1
  have hlen := selectedAlternative_pairList_length L
  have he : (g32p_exponents S).length = 2 * L.length := hp.length_eq.symm.trans hlen
  refine ⟨L.length, he, ?_, ?_⟩
  · rw [← List.length_eq_zero_iff]
    omega
  · change ¬ (g32p_exponents S) = [] ↔ _
    rw [← List.length_eq_zero_iff]
    omega

/-- U17 and T14 supply the literal alternatives at the same cover.
The two premises retain every native existential and instance binder. -/
theorem selectedAlternative_supplier {A : g32t_Sixfold} (X : g32p_Cover A) :
    (by_elab do
      let x ← Lean.Elab.Term.elabTerm (Lean.mkIdent `X) none
      let f ← Lean.Meta.mkAppM ``s4_selected_native_supplier #[x]
      let ty ← Lean.Meta.inferType f
      let native := ty.bindingDomain!
      let result := ty.bindingBody!
      Lean.Meta.forallTelescope native fun xs body => do
        let alts := body.getAppArgs
        let exps ← Lean.Meta.mkAppM ``g32p_exponents #[xs[0]!]
        let nil ← Lean.Elab.Term.elabTerm (← `(([] : List ℕ))) none
        let empty ← Lean.Meta.mkEq exps nil
        let nonempty ← Lean.Meta.mkAppM ``Not #[empty]
        let u ← Lean.Meta.mkForallFVars xs (← Lean.mkArrow empty alts[1]!)
        let t ← Lean.Meta.mkForallFVars xs (← Lean.mkArrow nonempty alts[0]!)
        Lean.mkArrow u (← Lean.mkArrow t result)) := by
  classical
  intro hU17 hT14
  apply s4_selected_native_supplier X
  intro S hS
  obtain ⟨r, hlen, hz, hp⟩ := selectedAlternative_pair_count X S hS
  by_cases hr : r = 0
  · exact Or.inr (hU17 S hS (hz.mpr hr))
  · exact Or.inl (hT14 S hS (hp.mpr (Nat.pos_of_ne_zero hr)))

#print axioms selectedAlternative_pair_count
#print axioms selectedAlternative_supplier
end HodgeLean.Foundations.Program
