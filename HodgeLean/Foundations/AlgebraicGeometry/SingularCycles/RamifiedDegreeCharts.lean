import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeAnalytic
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeLocal

/-! # Centered chart domains for an isolated point map

The coordinate expression uses the actual map and the supplied charts.
Its zero is isolated on an open coordinate neighbourhood of the origin.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

def centeredPointChartMap
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] (d : ℕ)
    (f : M → N) (eX : OpenPartialHomeomorph M (Fin d → ℂ))
    (eZ : OpenPartialHomeomorph N (Fin d → ℂ)) (x : M) :
    (Fin d → ℂ) → (Fin d → ℂ) :=
  fun v => eZ (f (eX.symm (v + eX x))) - eZ (f x)

theorem exists_centered_point_chart_domain
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] (d : ℕ)
    (f : M → N) (hf : Continuous f)
    (eX : OpenPartialHomeomorph M (Fin d → ℂ))
    (eZ : OpenPartialHomeomorph N (Fin d → ℂ))
    (x : M) (hx : x ∈ eX.source) (hz : f x ∈ eZ.source)
    (U : Set M) (hU : IsOpen U) (hxU : x ∈ U)
    (hiso : ∀ y ∈ U, f y = f x → y = x) :
    ∃ O : Set (Fin d → ℂ), IsOpen O ∧ (0 : Fin d → ℂ) ∈ O ∧
      (∀ v ∈ O, v + eX x ∈ eX.target ∧ eX.symm (v + eX x) ∈ U ∧
        f (eX.symm (v + eX x)) ∈ eZ.source) ∧
      ∀ v ∈ O, centeredPointChartMap d f eX eZ x v = 0 ↔ v = 0 := by
  let W : Set M := U ∩ f ⁻¹' eZ.source
  have hW : IsOpen W := hU.inter (eZ.open_source.preimage hf)
  let O : Set (Fin d → ℂ) :=
    (fun v => v + eX x) ⁻¹' (eX.target ∩ eX.symm ⁻¹' W)
  have hO : IsOpen O := (eX.isOpen_inter_preimage_symm hW).preimage
    (continuous_id.add continuous_const)
  have h0O : (0 : Fin d → ℂ) ∈ O := by
    change 0 + eX x ∈ eX.target ∧ eX.symm (0 + eX x) ∈ W
    rw [zero_add, eX.left_inv hx]
    exact ⟨eX.map_source hx, hxU, hz⟩
  refine ⟨O, hO, h0O, (fun _ hv => ⟨hv.1, hv.2.1, hv.2.2⟩), ?_⟩
  intro v hv
  constructor
  · intro hzero
    have heq : eZ (f (eX.symm (v + eX x))) = eZ (f x) := sub_eq_zero.mp hzero
    have hfval : f (eX.symm (v + eX x)) = f x := eZ.injOn hv.2.2 hz heq
    have hs : eX.symm (v + eX x) = x := hiso _ hv.2.1 hfval
    have hcoord : v + eX x = eX x :=
      (eX.right_inv hv.1).symm.trans (congrArg eX hs)
    exact add_right_cancel (hcoord.trans (zero_add (eX x)).symm)
  · rintro rfl
    simp only [centeredPointChartMap, zero_add, eX.left_inv hx, sub_self]

theorem centeredPointChartMap_analyticAt
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] (f : X ⟶ Z) (d : ℕ)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : HodgeLean.Adapters.a3b4_IsHolChart X.hom eX)
    (heZ : HodgeLean.Adapters.a3b4_IsHolChart Z.hom eZ)
    (x : ComplexPoint X) (v : Fin d → ℂ)
    (hv : v + pointChart eX x ∈ (pointChart eX).target)
    (hvZ : Point.map f ((pointChart eX).symm (v + pointChart eX x)) ∈ eZ.source) :
    AnalyticAt ℂ
      (centeredPointChartMap d (Point.map f) (pointChart eX) (pointChart eZ) x) v := by
  have h := map_in_pointChart_analytic f d eX eZ heX heZ (v + pointChart eX x) hv hvZ
  have ht : AnalyticAt ℂ (fun w : Fin d → ℂ => w + pointChart eX x) v :=
    analyticAt_id.add analyticAt_const
  change AnalyticAt ℂ (fun w => pointChart eZ
    (Point.map f ((pointChart eX).symm (w + pointChart eX x))) -
      pointChart eZ (Point.map f x)) v
  exact (h.comp (f := fun w : Fin d → ℂ => w + pointChart eX x) (x := v) ht).sub analyticAt_const

end AlgebraicGeometry.SingularCycles
