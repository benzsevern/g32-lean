import HodgeLean.Adapters.NormalConeB4aClassManifoldInverse

/-! # Inverse regularity for retained base charts with zero normal coordinates -/

noncomputable section
set_option maxHeartbeats 100000
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

/-- The zero-dimensional second factor in the retained holomorphic chart
predicate still gives an analytic inverse on the original base chart target. -/
theorem retained_holomorphic_base_inverse
    (Y : Over (Spec ↧ℂ)) (m : ℕ) [SmoothOfRelativeDimension m Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (b : OpenPartialHomeomorph (ComplexPoint Y) (Fin m → ℂ))
    (hb : a3b4_IsHolChart Y.hom (b.trans
      ((Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph))) :
    ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω b.symm b.target := by
  let e := b.trans
    ((Homeomorph.prodUnique (Fin m → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)
  have he := a3b4a_classHolomorphicChart_contMDiffOn Y m m 0 e hb
  have hfst := (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin 0 → ℂ)).contMDiff.comp_contMDiffOn he
  have hreg : ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω b b.source :=
    hfst.mono (fun _ hy => ⟨hy, Set.mem_univ _⟩)
  exact a3b4a_classManifoldChart_inverse b hreg

#print axioms retained_holomorphic_base_inverse
end HodgeLean.Foundations.TubularEuler
