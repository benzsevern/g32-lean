import HodgeLean.Foundations.QuotientDuality.ProperCycleEtaleOpenLocalSheets

/-! # Original residue-degree local homology pushforward on a generic finite etale open -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- On an actual finite etale affine base open, the literal original singular map has local homology multiplicity equal to the original generic residue degree, with the original complex-normalized classes and without global finiteness.
Source: Fulton, Intersection Theory, section 1.4; SGA 1, Expose I and Expose XII, finite etale degree and analytic local inverses; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_open_residue_local_degree
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f.left ⁻¹ᵁ U)]
    [IsFinite (f.left ∣_ U)] [Etale (f.left ∣_ U)]
    (d : ℕ) (y₀ : ComplexPoint (openScheme Y U))
    (cX : Homology ℚ (a3b4_an X.hom) (2 * d))
    (cY : Homology ℚ (a3b4_an Y.hom) (2 * d))
    (hcomplexX : ∀ (e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)),
      (∀ i, (f4_analytification X).IsHolFun (fun z : e.source => e z i)) →
      ∀ (x : ComplexPoint X) (hx : x ∈ e.source),
        localOrientation (a3b4_an X.hom) (2 * d) cX x = localClassOfChart d e x hx)
    (hcomplexY : ∀ (e : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ)),
      (∀ i, (f4_analytification Y).IsHolFun (fun z : e.source => e z i)) →
      ∀ (z : ComplexPoint Y) (hz : z ∈ e.source),
        localOrientation (a3b4_an Y.hom) (2 * d) cY z = localClassOfChart d e z hz)
    (e : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ)) (hy : Point.map (openInclusion Y U) y₀ ∈ e.source)
    (he : ∀ i, (f4_analytification Y).IsHolFun (fun z : e.source => e z i)) :
    localOrientation (a3b4_an Y.hom) (2 * d)
      (homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f)) cX) (Point.map (openInclusion Y U) y₀) =
      (a1p_degree f.left (genericPoint X.left) : ℚ) •
        localOrientation (a3b4_an Y.hom) (2 * d) cY (Point.map (openInclusion Y U) y₀) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  let y := Point.map (openInclusion Y U) y₀
  have hfinite := properCycle_complex_fibre_finite_of_finite_target_open X Y f U y₀
  have hlocalU := properCycle_local_sheets_over_finite_etale_open X Y f U
  have hyU : y ∈ Point.overOpen U := (openHomeomorph Y U y₀).property
  have hlocal : IsLocalHomeomorphOn (Point.map f) ((Point.map f) ⁻¹' {y}) := by
    intro x hx
    apply hlocalU x
    change Point.map f x ∈ Point.overOpen U
    rw [show Point.map f x = y from hx]
    exact hyU
  have hc := properCycle_holomorphic_local_degree
    (f4_analytification X) (f4_analytification Y)
    (TopCat.ofHom (Point.continuousMap f)) (f4_map_isHom f) y hlocal hfinite d cX cY
    hcomplexX hcomplexY
    (fun V hV hyV => properCycle_holomorphic_chart_neighborhood_basis
      (f4_analytification Y) d y e hy he V hV hyV)
  rw [properCycle_generic_degree_eq_fibre_card_on_finite_etale_open X Y f hg U hU y₀]
  exact hc

end HodgeLean.Foundations.QuotientDuality
