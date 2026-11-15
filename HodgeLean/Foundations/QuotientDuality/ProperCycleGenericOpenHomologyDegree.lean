import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericOpenLocalDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomologyLineLocalization

/-! # Original global homology degree detected on a generic finite etale open -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A normalized one-dimensional target top homology upgrades the actual generic finite etale local degree to the global homology pushforward with the original residue degree.
Source: Fulton, Intersection Theory, section 1.4; Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_open_residue_homology_degree
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
    (hdim : Module.finrank ℚ (Homology ℚ (a3b4_an Y.hom) (2 * d)) = 1)
    (e : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ)) (hy : Point.map (openInclusion Y U) y₀ ∈ e.source)
    (he : ∀ i, (f4_analytification Y).IsHolFun (fun z : e.source => e z i)) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f)) cX =
      (a1p_degree f.left (genericPoint X.left) : ℚ) • cY := by
  letI : T2Space (ComplexPoint Y) := f4_t2Space Y
  let y := Point.map (openInclusion Y U) y₀
  have hcY : localOrientation (a3b4_an Y.hom) (2 * d) cY y ≠ 0 := by
    rw [hcomplexY e he y hy]
    exact localClassOfChart_ne_zero d e y hy
  apply properCycle_homology_line_local_orientation_injective
    (a3b4_an Y.hom) (2 * d) y cY hcY hdim
  have hlocal := properCycle_generic_open_residue_local_degree X Y f hg U hU d y₀
    cX cY hcomplexX hcomplexY e hy he
  exact hlocal.trans (map_smul
    (relativeHomologyProjection ℚ (pointComplementPair y) (2 * d)).hom
    (a1p_degree f.left (genericPoint X.left) : ℚ) cY).symm

end HodgeLean.Foundations.QuotientDuality
