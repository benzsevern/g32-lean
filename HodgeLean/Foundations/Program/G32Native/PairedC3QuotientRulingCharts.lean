import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientRulingAssembly
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualComplexRestriction

/-! # Local ratio maps with their original complex structure -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- Local morphism data on the canonical residual quotient cover. Overlap
agreement, smoothness and the marked squares are separate assertions. -/
structure PairedC3QuotientRulingCharts
    {X : Scheme.{0}} (I : X.IdealSheafData) (s : I.subscheme ⟶ Spec ↧ℂ) where
  Index : Type
  V : Index → X.affineOpens
  covers : (⨆ j, I.subschemeι ⁻¹ᵁ (V j).1) = ⊤
  map : ∀ j, Over.mk ((pairedC3ResidualQuotientCover.{0,0,0} I V covers).f j ≫ s) ⟶
    projectiveLine

/-- The projective chart map of a quotient-ring parameter retains the
specified residual structure morphism to the complex base. -/
def pairedC3ResidualProjectiveMap
    (X : Over (Spec ↧ℂ)) (I : X.left.IdealSheafData)
    (V : X.left.affineOpens) (k : Fin 2) (z : Γ(X.left, V) ⧸ I.ideal V) :
    Over.mk (I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom) ⟶ projectiveLine := by
  let p := I.subschemeCover.f V ≫ I.subschemeι ≫ X.hom
  letI := pairedC3SpecAlgebra p
  exact Over.homMk (projectiveLineChart k z).left
    ((Over.w (projectiveLineChart k z)).trans (pairedC3_spec_algebra_structure_map p))

#print axioms pairedC3ResidualProjectiveMap
end HodgeLean.Foundations.Program.G32Native
