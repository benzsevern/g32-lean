import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualRestrictionScheme

/-! # The canonical quotient-ring cover of the residual scheme -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A family of original affine neighbourhoods covering the residual support
gives an open cover with the actual residual quotient rings as its objects. -/
def pairedC3ResidualQuotientCover {X : Scheme} (I : X.IdealSheafData)
    {ι : Type*} (V : ι → X.affineOpens)
    (hV : (⨆ j, I.subschemeι ⁻¹ᵁ (V j).1) = ⊤) : I.subscheme.OpenCover :=
  Scheme.Cover.mkOfCovers ι
    (fun j => Spec (CommRingCat.of (Γ(X, V j) ⧸ I.ideal (V j))))
    (fun j => I.subschemeCover.f (V j)) (by
      intro x
      have hx : x ∈ (⨆ j, I.subschemeι ⁻¹ᵁ (V j).1) := by
        rw [hV]
        trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      have hr : x ∈ (I.subschemeCover.f (V j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hr
      exact ⟨j, y, hy⟩)

/-- The cover retains the original canonical subscheme chart inclusions. -/
theorem pairedC3_residual_quotient_cover_map {X : Scheme} (I : X.IdealSheafData)
    {ι : Type*} (V : ι → X.affineOpens)
    (hV : (⨆ j, I.subschemeι ⁻¹ᵁ (V j).1) = ⊤) (j : ι) :
    (pairedC3ResidualQuotientCover I V hV).f j = I.subschemeCover.f (V j) := rfl

#print axioms pairedC3ResidualQuotientCover
#print axioms pairedC3_residual_quotient_cover_map
end HodgeLean.Foundations.Program.G32Native
