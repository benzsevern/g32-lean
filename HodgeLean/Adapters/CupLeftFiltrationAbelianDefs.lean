import HodgeLean.Adapters.HolomorphicPeriodsDeRham
import HodgeLean.Adapters.ResolutionClassActionDefs

/-! # The primitive complex as a resolution between de Rham and singular cochains

Stage hl5 of the `hL` track (`docs/specs/CupLeftFiltrationAbelian.md`). Stage 4k
(`HolomorphicPeriodsDeRham`) built the two-term complex `T' = [Ω^0 → Ω^0/ℂ]` with
`q' : ℂ[0] ⟶ T'` (`constantsToPrimitiveComplex`), the comparison `T' ⟶ T = [Ω^0 → Ω^1_cl]` and
the inclusion `T ⟶ Ω•`, and the integration map `r : T' ⟶ S•` (`primitiveComplexToSingular`).
This file names the composite `p : T' ⟶ Ω•` and proves, from stage 4k's proved quasi-isomorphism
statements, that `q'`, `p` and `r` lie in the class `W = analyticQuasiIsomorphisms X` that defines
the derived category (two out of three for `p` and `r`).

Everything here is a definition or a lemma with a complete proof. HC no distance; AV milestone no
distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The map `p : T' = [Ω^0 → Ω^0/ℂ] ⟶ Ω•`: the comparison `T' ⟶ T = [Ω^0 → Ω^1_cl]` (identity in
degree `0`, `[f] ↦ df` in degree `1`) followed by the inclusion `T ⟶ Ω•`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3; stage 4k
`primitiveComplexToClosedFormComplex` and `closedFormComplexToDeRham`. -/
def primitiveComplexToDeRham : primitiveComplex X ⟶ Ω•(X) :=
  primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X

example : primitiveComplexToDeRham X =
    primitiveComplexToClosedFormComplex X ≫ closedFormComplexToDeRham X :=
  rfl

/-- `q' : ℂ[0] ⟶ T'` followed by `p` is upstream's `q_Ω : ℂ[0] ⟶ Ω•`.
Source: stage 4k `spec_constantsToPrimitiveComplex_comp` and
`spec_constantsToClosedFormComplex_comp_toDeRham`. -/
theorem constantsToPrimitiveComplex_comp_toDeRham :
    constantsToPrimitiveComplex X ≫ primitiveComplexToDeRham X =
      constantsToHolomorphicDeRhamComplexInt X := by
  rw [primitiveComplexToDeRham, ← Category.assoc, spec_constantsToPrimitiveComplex_comp,
    spec_constantsToClosedFormComplex_comp_toDeRham]

/-- `q' : ℂ[0] ⟶ T'` is in `W`.
Source: stage 4k `spec_constantsToPrimitiveComplex_quasiIso`. -/
theorem constantsToPrimitiveComplex_mem :
    analyticQuasiIsomorphisms X (constantsToPrimitiveComplex X) :=
  (HomologicalComplex.mem_quasiIso_iff _).mpr (spec_constantsToPrimitiveComplex_quasiIso X)

/-- `p : T' ⟶ Ω•` is in `W`: `q'` and `q' ≫ p = q_Ω` are quasi-isomorphisms.
Source: Mathlib's `quasiIso_of_comp_left` (two out of three); stage 4k
`spec_constantsToPrimitiveComplex_quasiIso`; upstream
`constantsToHolomorphicDeRhamComplexInt_quasiIso`. -/
theorem primitiveComplexToDeRham_mem :
    analyticQuasiIsomorphisms X (primitiveComplexToDeRham X) := by
  have := spec_constantsToPrimitiveComplex_quasiIso X
  have : QuasiIso (constantsToPrimitiveComplex X ≫ primitiveComplexToDeRham X) := by
    rw [constantsToPrimitiveComplex_comp_toDeRham]
    infer_instance
  exact (HomologicalComplex.mem_quasiIso_iff _).mpr
    (quasiIso_of_comp_left (constantsToPrimitiveComplex X) (primitiveComplexToDeRham X))

/-- `r : T' ⟶ S•` is in `W`: `q'` and `q' ≫ r = q_S` are quasi-isomorphisms.
Source: Mathlib's `quasiIso_of_comp_left` (two out of three); stage 4k
`spec_constantsToPrimitiveComplex_quasiIso` and
`spec_constantsToPrimitiveComplex_comp_toSingular`; upstream
`constantsToSingularCochainComplexInt_quasiIso`. -/
theorem primitiveComplexToSingular_mem :
    analyticQuasiIsomorphisms X (primitiveComplexToSingular X) := by
  have := spec_constantsToPrimitiveComplex_quasiIso X
  have : QuasiIso (constantsToPrimitiveComplex X ≫ primitiveComplexToSingular X) := by
    rw [spec_constantsToPrimitiveComplex_comp_toSingular]
    exact constantsToSingularCochainComplexInt_quasiIso X ℂ
  exact (HomologicalComplex.mem_quasiIso_iff _).mpr
    (quasiIso_of_comp_left (constantsToPrimitiveComplex X) (primitiveComplexToSingular X))

end HodgeLean.Adapters
