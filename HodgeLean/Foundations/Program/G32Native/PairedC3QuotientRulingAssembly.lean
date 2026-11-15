import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualQuotientCover
import HodgeLean.Foundations.Program.G32Native.PairedC3RulingDescent

/-! # Marked ruling assembly on the original residual quotient cover -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u v
namespace HodgeLean.Foundations.Program.G32Native

/-- Compatible smooth maps on the canonical quotient charts supply a smooth
ruling with the original marked intersection square. The chart objects and
inclusions are those of the ideal subscheme, without replacing the source. -/
theorem pairedC3_quotient_ruling_assembly
    {S X : Scheme.{u}} (I : X.IdealSheafData) (s : I.subscheme ⟶ S)
    (C : Over S) {ι : Type v} (V : ι → X.affineOpens)
    (hV : (⨆ j, I.subschemeι ⁻¹ᵁ (V j).1) = ⊤)
    (f : ∀ j, (pairedC3ResidualQuotientCover.{v,u,u} I V hV).X j ⟶ C.left)
    (hf : ∀ j k,
      pullback.fst ((pairedC3ResidualQuotientCover.{v,u,u} I V hV).f j)
        ((pairedC3ResidualQuotientCover.{v,u,u} I V hV).f k) ≫ f j =
      pullback.snd _ _ ≫ f k)
    (hbase : ∀ j, f j ≫ C.hom = (pairedC3ResidualQuotientCover.{v,u,u} I V hV).f j ≫ s)
    (hs : ∀ j, Smooth (f j))
    {D T : Scheme.{u}} (a : D ⟶ T) (b : D ⟶ I.subscheme) (c : T ⟶ C.left)
    (H : ∀ j, IsPullback
      ((pairedC3ResidualQuotientCover.{v,u,u} I V hV).pullbackHom b j)
      (((pairedC3ResidualQuotientCover.{v,u,u} I V hV).pullback₁ b).f j ≫ a) (f j) c) :
    ∃ g : Over.mk s ⟶ C, Smooth g.left ∧ IsPullback a b c g.left := by
  let U := pairedC3ResidualQuotientCover.{v,u,u} I V hV
  refine ⟨pairedC3RulingOfCover (Over.mk s) C U f hf hbase, ?_, ?_⟩
  · exact pairedC3_ruling_of_cover_smooth (Over.mk s) C U f hf hbase hs
  · exact pairedC3_ruling_of_cover_marked_square (Over.mk s) C U f hf hbase a b c H

#print axioms pairedC3_quotient_ruling_assembly
end HodgeLean.Foundations.Program.G32Native
