import HodgeLean.Foundations.Program.G32Native.HolomorphicTangentDual

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native
open Module

/-- An intertwining equivalence identifies the eigenspaces in an invariant subspace.
Source: Bourbaki, Algebra, II §5, restriction and transport of linear maps. -/
def invariantEigenspaceEquiv {K V U : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup U] [Module K U]
    (T : End K V) (S : End K U) (H : Submodule K V)
    (hT : ∀ x ∈ H, T x ∈ H) (e : H ≃ₗ[K] U)
    (h : ∀ x : H, e ⟨T x, hT x x.property⟩ = S (e x)) (z : K) :
    ↥(T.eigenspace z ⊓ H) ≃ₗ[K] ↥(S.eigenspace z) where
  toFun x := ⟨e ⟨x, x.property.2⟩, by
    rw [Module.End.mem_eigenspace_iff]
    rw [← h]
    have hx := Module.End.mem_eigenspace_iff.mp x.property.1
    have he : (⟨T x, hT x x.property.2⟩ : H) = z • ⟨x, x.property.2⟩ :=
      Subtype.ext hx
    rw [he, map_smul]⟩
  invFun y := ⟨e.symm y, by
    refine ⟨?_, (e.symm y).property⟩
    change (e.symm y).val ∈ T.eigenspace z
    rw [Module.End.mem_eigenspace_iff]
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    have he : (⟨T (e.symm y), hT _ (e.symm y).property⟩ : H) = z • e.symm y := by
      apply e.injective
      rw [h, e.apply_symm_apply, map_smul, e.apply_symm_apply, hy]
    exact congrArg Subtype.val he⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg (fun t : H => t.val) (e.symm_apply_apply ⟨x, x.property.2⟩)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add e (⟨x, x.property.2⟩ : H) (⟨y, y.property.2⟩ : H))
  map_smul' c x := Subtype.ext (map_smul e c (⟨x, x.property.2⟩ : H))

#print axioms invariantEigenspaceEquiv
end HodgeLean.Foundations.Program.G32Native
