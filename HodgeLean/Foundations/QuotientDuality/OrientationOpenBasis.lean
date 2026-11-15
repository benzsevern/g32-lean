import HodgeLean.Foundations.QuotientDuality.OrientationDefs

/-! Contractible open bases on open subspaces. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

lemma contractible_open_basis_on_open (X : TopCat.{0})
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ W : Opens X, x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)
    (U : Opens X) (x : U) (V : Opens U) (hx : x ∈ V) :
    ∃ W : Opens U, x ∈ W ∧ ContractibleSpace W ∧ W ≤ V := by
  let B : Opens X := ⟨Subtype.val '' (V : Set U), U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩
  obtain ⟨W, hxW, hW, hWB⟩ := hX x.1 B ⟨x, hx, rfl⟩
  have hWU : (W : Set X) ⊆ U := by
    intro z hz
    obtain ⟨v, _, hv⟩ := hWB hz
    exact hv ▸ v.2
  let W' : Opens U := ⟨Subtype.val ⁻¹' W, W.isOpen.preimage continuous_subtype_val⟩
  let e : W' ≃ₜ W :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun z => ⟨⟨z.1, hWU z.2⟩, z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨W', hxW, e.contractibleSpace_iff.mpr hW, ?_⟩
  intro z hz
  obtain ⟨v, hv, he⟩ := hWB hz
  have he' : v = z := Subtype.ext he
  exact he' ▸ hv

end HodgeLean.Foundations.QuotientDuality
