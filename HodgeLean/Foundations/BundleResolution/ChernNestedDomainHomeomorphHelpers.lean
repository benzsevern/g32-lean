import Mathlib.Topology.Homeomorph.Lemmas

/-! # Actual nested domain coordinates

A subset contained in a supplied ambient domain has the same topology
when it is viewed as a nested subtype or as its original subset.
HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.BundleResolution

def i1_nestedDomainHomeomorph {T : Type*} [TopologicalSpace T]
    {U W : Set T} (h : U ⊆ W) : {w : W // w.val ∈ U} ≃ₜ U where
  toFun x := ⟨x.val.val, x.property⟩
  invFun u := ⟨⟨u.val, h u.property⟩, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

end HodgeLean.Foundations.BundleResolution
