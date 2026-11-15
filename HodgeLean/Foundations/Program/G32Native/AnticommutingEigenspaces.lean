import HodgeLean.Foundations.Program.G32Native.TypeIIIInducedAction

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- An injective anticommuting operator preserving a subspace pairs its two
opposite eigenspace intersections, so they have equal dimensions.
Source: G32 v0.16, Lemma 8.1, first paragraph of proof (the linear algebra
of the anticommuting quaternion on a Hodge summand). -/
theorem finrank_eigenspace_inf_eq_of_anticommutes
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Module.Finite K E]
    (J T : Module.End K E) (P : Submodule K E)
    (hT : Function.Injective T) (hanti : ∀ x, J (T x) = -T (J x))
    (hP : P.map T ≤ P) (μ : K) :
    Module.finrank K ↥(Module.End.eigenspace J μ ⊓ P) =
      Module.finrank K ↥(Module.End.eigenspace J (-μ) ⊓ P) := by
  have hle (a : K) :
      Module.finrank K ↥(Module.End.eigenspace J a ⊓ P) ≤
        Module.finrank K ↥(Module.End.eigenspace J (-a) ⊓ P) := by
    let f : ↥(Module.End.eigenspace J a ⊓ P) →ₗ[K]
        ↥(Module.End.eigenspace J (-a) ⊓ P) :=
      { toFun x := ⟨T x, by
          constructor
          · apply Module.End.mem_eigenspace_iff.mpr
            rw [hanti, Module.End.mem_eigenspace_iff.mp x.property.1, map_smul, neg_smul]
          · exact hP (Submodule.mem_map_of_mem x.property.2)⟩
        map_add' x y := Subtype.ext (T.map_add x y)
        map_smul' a x := Subtype.ext (T.map_smul a x) }
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro x y hxy
    apply Subtype.ext
    exact hT (congrArg Subtype.val hxy)
  apply le_antisymm (hle μ)
  have hreverse := hle (-μ)
  rw [neg_neg] at hreverse
  exact hreverse

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.finrank_eigenspace_inf_eq_of_anticommutes
