import HodgeLean.Adapters.NormalConeB4aGysinProductDimension
import HodgeLean.Adapters.NormalConeB4aGysinSmoothParametrization

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- A smooth source injective on complex points has dimension at most the
ambient coordinate dimension at every point mapping into a holomorphic chart. -/
theorem a3b4a_gysin_smooth_source_chart_dimension_le
    (X Y : Over (Spec (CommRingCat.of ℂ))) (d n c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hf : Function.Injective (Point.map f))
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (x : ComplexPoint X)
    (hx : Point.map f x ∈ Φ.source) : d ≤ n + c := by
  let e := chartAt (Fin d → ℂ) x
  let V := Point.map f ⁻¹' Φ.source
  let U := e.target ∩ e.symm ⁻¹' V
  have hU : IsOpen U := e.isOpen_inter_preimage_symm
    (Φ.open_source.preimage (Point.continuous_map f))
  have hxs : x ∈ e.source := mem_chart_source (Fin d → ℂ) x
  have hne : U.Nonempty := by
    refine ⟨e x, e.map_source hxs, ?_⟩
    change Point.map f (e.symm (e x)) ∈ Φ.source
    rwa [e.left_inv hxs]
  have hfin : ∀ a, {z | z ∈ U ∧ Φ (Point.map f (e.symm z)) = a}.Finite := by
    intro a
    apply Set.Subsingleton.finite
    intro u hu v hv
    apply e.symm.injOn hu.1.1 hv.1.1
    apply hf
    apply Φ.injOn hu.1.2 hv.1.2
    exact hu.2.trans hv.2.symm
  exact a3b4a_gysin_finite_fibre_product_dimension_le U hU hne
    (fun a => Φ (Point.map f (e.symm a)))
    (a3b4a_gysin_smooth_source_coordinate_parametrization X Y d n c f Φ hΦ x) hfin

end HodgeLean.Adapters
