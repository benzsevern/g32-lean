import HodgeLean.Adapters.NormalConeB4aGysinGraphChart
import HodgeLean.Adapters.NormalConeB4aGysinHolomorphicComposition
import HodgeLean.Adapters.NormalConeB4aGysinNormalCycles

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

/-- A holomorphic graph representation of the cycle support constructs a normal
chart transverse to every original vertical disk through that support. -/
theorem a3b4a_gysin_graph_normal_chart
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    (γ : AlgebraicCycle Z ℚ) {n c : ℕ}
    (Φ : OpenPartialHomeomorph (ComplexPoint (Over.mk q))
      ((Fin n → ℂ) × (Fin c → ℂ))) (hΦ : a3b4_IsHolChart q Φ)
    (ψ : C((Fin n → ℂ), (Fin c → ℂ)))
    (hψ : ∀ y ∈ Φ.source, AnalyticAt ℂ ψ (Φ y).1)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport q γ ↔ (Φ y).2 = ψ (Φ y).1)
    (a : Fin n → ℂ) (v : Fin c → ℂ) (hav : (a, v) ∈ Φ.target)
    (hz : Φ.symm (a, v) ∈ a3b4_cycleSupport q γ) :
    ∃ C : A3b4aGysinNormalChart q γ c, C.point = Φ.symm (a, v) ∧
      HasFDerivAt (fun v' => (C.chart (Φ.symm (a, v' + v))).2)
        (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  obtain ⟨Ψ, hsource, hcoord, hsupport, hderiv⟩ :=
    a3b4a_gysin_graph_flattening_chart Φ ψ (a3b4_cycleSupport q γ) hS
  let S := f4_analytification (Over.mk q)
  have hhol : a3b4_IsHolChart q Ψ := by
    constructor
    · intro j
      change S.IsHolFun (fun y : Ψ.source => (Ψ y).1 j)
      simp only [hcoord]
      rw [hsource]
      exact hΦ.1 j
    · intro j
      have hp : ∀ k, S.IsHolFun (fun y : Ψ.source => (Φ y).1 k) := by
        intro k
        rw [hsource]
        exact hΦ.1 k
      have hq : S.IsHolFun (fun y : Ψ.source => (Φ y).2 j) := by
        rw [hsource]
        exact hΦ.2 j
      have hc := a3b4a_gysin_holomorphic_coordinate_composition S
        (fun y : Ψ.source => (Φ y).1) hp (fun b => ψ b j) (fun y =>
          ((ContinuousLinearMap.proj j).analyticAt _).comp
            (hψ y (hsource ▸ y.2)))
      have hsub := (S.atlas.holSubring Ψ.source).sub_mem hq hc
      change S.IsHolFun (fun y : Ψ.source => (Φ y).2 j - ψ (Φ y).1 j) at hsub
      simpa only [hcoord, Pi.sub_apply] using hsub
  refine ⟨{ tangentDim := n
            chart := Ψ
            support_eq := hsupport
            point := Φ.symm (a, v)
            mem_source := hsource.symm ▸ Φ.map_target hav
            mem_support := hz
            holomorphic := hhol }, rfl, hderiv a v hav⟩

end HodgeLean.Adapters
