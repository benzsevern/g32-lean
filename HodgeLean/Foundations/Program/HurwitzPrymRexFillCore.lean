import HodgeLean.Foundations.Program.HurwitzPrymRexFillChart

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: the topology and charted space of the filled surface

The charts of `HurwitzPrymRexFillChart`, composed with a linear identification `κ : ℂ ≃ E`, form a
`ChartedSpaceCore`: their transitions are continuous on open sets. This gives the topology and the
charted space structure of the filled surface.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex HodgeLean.Foundations.Program.HurwitzPrymRexPunct

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous linear equivalence as a partial equivalence.
Source: Mathlib `Homeomorph.toOpenPartialHomeomorph`. -/
def κPE (κ : ℂ ≃L[ℂ] E) : PartialEquiv ℂ E := κ.toHomeomorph.toOpenPartialHomeomorph.toPartialEquiv

example (κ : ℂ ≃L[ℂ] E) (z : ℂ) : κPE κ z = κ z := rfl

theorem κPE_source (κ : ℂ ≃L[ℂ] E) : (κPE κ).source = univ := rfl
theorem κPE_target (κ : ℂ ≃L[ℂ] E) : (κPE κ).target = univ := rfl

theorem trans_κ_source {M : Type} (κ : ℂ ≃L[ℂ] E) (A A' : PartialEquiv M ℂ) :
    ((A.trans (κPE κ)).symm.trans (A'.trans (κPE κ))).source =
      κ.symm ⁻¹' (A.symm.trans A').source := by
  ext w
  simp [PartialEquiv.trans_source, κPE, PartialEquiv.trans_target]

theorem trans_κ_apply {M : Type} (κ : ℂ ≃L[ℂ] E) (A A' : PartialEquiv M ℂ) (w : E) :
    ((A.trans (κPE κ)).symm.trans (A'.trans (κPE κ))) w = κ ((A.symm.trans A') (κ.symm w)) := rfl

namespace Setup

variable (S : Setup E' p) (hp : IsQuotientCoveringMap p G) [Finite G]

theorem transition (x y : S.C hp) :
    IsOpen ((S.chart hp x).symm.trans (S.chart hp y)).source ∧
      ContinuousOn ((S.chart hp x).symm.trans (S.chart hp y))
        ((S.chart hp x).symm.trans (S.chart hp y)).source := by
  rcases x with u | c <;> rcases y with u' | c'
  · exact S.transition_AA hp u u'
  · exact S.transition_AP hp u c'
  · exact S.transition_PA hp c u'
  · exact S.transition_PP hp c c'

/-- **The chart core of the filled surface**, with model `E`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, Theorem 8.4; Mathlib `ChartedSpaceCore`. -/
def core (κ : ℂ ≃L[ℂ] E) : ChartedSpaceCore E (S.C hp) where
  atlas := range fun x ↦ (S.chart hp x).trans (κPE κ)
  chartAt x := (S.chart hp x).trans (κPE κ)
  mem_chart_source x := ⟨S.mem_chart_source hp x, by simp [κPE]⟩
  chart_mem_atlas x := ⟨x, rfl⟩
  open_source := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [trans_κ_source]
    exact (S.transition hp x y).1.preimage κ.symm.continuous
  continuousOn_toFun := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    rw [trans_κ_source]
    exact κ.continuous.comp_continuousOn ((S.transition hp x y).2.comp
      κ.symm.continuous.continuousOn fun w hw ↦ hw)

example (κ : ℂ ≃L[ℂ] E) (x : S.C hp) : (S.core hp κ).chartAt x = (S.chart hp x).trans (κPE κ) :=
  rfl

end Setup

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
