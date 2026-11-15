import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralDefs
import HodgeLean.Foundations.Program.CurveJacobianRest2Simplex

/-! Integral chains for the normalized period interface.
HC no distance; AV milestone no distance. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Manifold
open scoped Simplicial ContDiff
namespace HodgeLean.Foundations.Program
/-- Singular chains with integral coefficients on the scheme's complex points.
Source: Hatcher, Algebraic Topology, §2.1. -/
abbrev s4_c1a6_chains (Y : Over (Spec ↧ℂ)) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of (ComplexPoint Y) : TopCat.{0})
example := s4_c1a6_chains

/-- The integral singular simplex of a smooth path restricted to the unit interval.
Source: Hatcher, Algebraic Topology, §2.1; Griffiths–Harris, §2.2. -/
def s4_c1a6_pathChain (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    (γ : ℝ → ComplexPoint Y) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) 1 γ) :
    (s4_c1a6_chains Y).X 1 :=
  (TopCat.toSSet.obj (TopCat.of (ComplexPoint Y))).ιChainComplex
    (R := ModuleCat.of ℤ ℤ)
    (b3Rest2_pathSimplex ⟨fun t => γ t, hγ.continuous.comp continuous_subtype_val⟩) 1
example := @s4_c1a6_pathChain

/-- The canonical class of an integral cycle modulo torsion.
Source: Hatcher, Algebraic Topology, §2.1 and §3.1. -/
def s4_c1a6_cycleClass (Y : Over (Spec ↧ℂ))
    (z : (s4_c1a6_chains Y).cycles 1) : s4_c1a6_integralLattice Y :=
  Submodule.Quotient.mk ((s4_c1a6_chains Y).homologyπ 1 z)
example := s4_c1a6_cycleClass
end HodgeLean.Foundations.Program
