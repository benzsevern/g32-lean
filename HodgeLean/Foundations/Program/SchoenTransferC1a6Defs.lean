import HodgeLean.Foundations.Program.CurveJacobian
import HodgeLean.Foundations.Program.CurveJacobianAPeriods
import HodgeLean.Adapters.HolomorphicOneFormsDefs

/-! Actual scheme-form dual and its specified period quotient.
The form identification is an explicit input from the period-pairing stage.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry Manifold
open HodgeLean.Adapters
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
/-- Precomposition identifies the B3 functionals with scheme-form functionals.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4; period evaluation. -/
def s4_c1a6_dualMap (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [Module ℂ (GlobalHolomorphicForm Y 1)]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y)) :
    b3_linearDual ℂ (ComplexPoint Y) →ₗ[ℂ] Module.Dual ℂ (GlobalHolomorphicForm Y 1) :=
  (LinearMap.dualMap φ.toLinearMap).comp b3A_toDual

example := @s4_c1a6_dualMap

/-- The complexified period evaluated on an actual global scheme form.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4; period evaluation. -/
def s4_c1a6_periodMap (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [Module ℂ (GlobalHolomorphicForm Y 1)]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y)) :
    (ℂ ⊗[ℤ] b3_periodLattice ℂ (ComplexPoint Y)) →ₗ[ℂ]
      Module.Dual ℂ (GlobalHolomorphicForm Y 1) :=
  (s4_c1a6_dualMap Y φ).comp
    ((b3_cplxPeriod ℂ (ComplexPoint Y)).codRestrict _ b3A_cplxPeriod_mem_linearDual)

example := @s4_c1a6_periodMap

/-- The specified integral period image in the scheme-form dual.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4; period evaluation. -/
def s4_c1a6_periodEmbedding (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [Module ℂ (GlobalHolomorphicForm Y 1)]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y)) :
    b3_periodLattice ℂ (ComplexPoint Y) →+
      Module.Dual ℂ (GlobalHolomorphicForm Y 1) :=
  { toFun := fun l => s4_c1a6_dualMap Y φ ⟨l.val, b3A_lattice_mem_linearDual l⟩
    map_zero' := by exact map_zero (s4_c1a6_dualMap Y φ)
    map_add' := fun l m => by
      ext θ
      change (l + m).val (φ θ) = l.val (φ θ) + m.val (φ θ)
      rfl }

example := @s4_c1a6_periodEmbedding

/-- The dual of actual global forms modulo the specified integral period image.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §2.4, period quotient. -/
abbrev s4_c1a6_periodTorus (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom]
    [Module ℂ (GlobalHolomorphicForm Y 1)]
    [ChartedSpace ℂ (ComplexPoint Y)] [IsManifold 𝓘(ℂ, ℂ) ω (ComplexPoint Y)]
    (φ : GlobalHolomorphicForm Y 1 ≃ₗ[ℂ] b3_HolForm ℂ (ComplexPoint Y)) :=
  Module.Dual ℂ (GlobalHolomorphicForm Y 1) ⧸ (s4_c1a6_periodEmbedding Y φ).range

example := @s4_c1a6_periodTorus

end HodgeLean.Foundations.Program
