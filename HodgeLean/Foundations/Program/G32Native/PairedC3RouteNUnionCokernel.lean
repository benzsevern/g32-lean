import HodgeLean.Foundations.Program.G32Native.UnionConormalGlobalExact

/-! # The cokernel of the natural union conormal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The natural union comparison has as its cokernel the direct image of
the intersection conormal on the second component. This uses right
exactness, without a smoothness or local-freeness premise on that component.
Source: Fulton, Intersection Theory, Appendix B.7.4;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
def pairedUnionConormalCokernelIso
    {V T T₁ T₂ Z : Scheme.{0}} [IsLocallyNoetherian V]
    (t : T ⟶ V) (t₁ : T₁ ⟶ V) (t₂ : T₂ ⟶ V)
    [IsClosedImmersion t] [IsClosedImmersion t₁] [IsClosedImmersion t₂]
    (a : T₁ ⟶ T) (s₁ : Z ⟶ T₁) (s₂ : Z ⟶ T₂)
    [IsClosedImmersion s₁] [IsClosedImmersion s₂]
    (ha : a ≫ t = t₁) (hs : s₁ ≫ t₁ = s₂ ≫ t₂)
    (hunion : t.ker = t₁.ker ⊓ t₂.ker)
    (hinter : (s₁ ≫ t₁).ker = t₁.ker ⊔ t₂.ker) :
    cokernel (unionConormalFirst t t₁ a ha) ≅
      (Scheme.Modules.pushforward s₁).obj (s2c_conormal s₂) := by
  let C := unionConormalComplex t t₁ t₂ a s₁ s₂ ha hs hunion
  haveI : Epi C.g := unionConormalLast_epi t₁ t₂ s₁ s₂ hs hinter
  have hC : C.Exact :=
    unionConormal_exact_of_locallyNoetherian t t₁ t₂ a s₁ s₂ ha hs hunion hinter
  exact (cokernelIsCokernel C.f).coconePointUniqueUpToIso hC.gIsCokernel

#print axioms pairedUnionConormalCokernelIso
end HodgeLean.Foundations.Program.G32Native
