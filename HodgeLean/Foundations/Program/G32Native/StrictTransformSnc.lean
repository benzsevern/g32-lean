import HodgeLean.Foundations.Program.G32Native.StrictTransformFamilySnc
import Mathlib.Data.Complex.Basic

/-! Retain SNC on the old labels after a blow-up along an SNC centre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Discarding the exceptional label from the total transform retains SNC. -/
theorem g32l4_strictTransformFamily_isSnc
    (B : Over (Spec ↧ℂ)) [Smooth B.hom]
    (E : Scheme.DivisorFamily B.left) (K : B.left.IdealSheafData)
    (hE : E.IsSnc) (hK : E.HasSncWith K) :
    (g32l4_strictTransformFamily E K).IsSnc := by
  have htotal := totalTransform_isSnc B.hom E K hE hK
  constructor
  · intro i
    exact htotal.1 (toLex (Sum.inl i))
  · intro x
    obtain ⟨m, z, hz, c, hc, hI⟩ := htotal.2 x
    let lift : {i : E.ι // x ∈ ((E.component i).strictTransform K).support} →
        {i : (E.totalTransform K).ι // x ∈ ((E.totalTransform K).component i).support} :=
      fun i => ⟨toLex (Sum.inl i.val), i.property⟩
    have hlift : Function.Injective lift := by
      intro a b h
      apply Subtype.ext
      have hval := congrArg (fun i => ofLex i.val) h
      exact Sum.inl_injective hval
    refine ⟨m, z, hz, c ∘ lift, hc.comp hlift, ?_⟩
    intro i
    exact hI (lift i)

end HodgeLean.Foundations.Program
