import HodgeLean.Foundations.IntegralHomology.Defs
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralMap
import HodgeLean.Foundations.Program.CurveJacobian

/-! Integral evaluation and transport of actual periods to a specified dual of forms.
The constructions retain the existing coefficient normalization.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Manifold
open HodgeLean.Foundations.Program
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.IntegralHomology.StageThree

/-- Evaluate a boundary-annihilating integral functional after both quotients.
Source: Hatcher, Algebraic Topology, §3.1; C1a6IntegralDescent. -/
def pairing (S : ShortComplex (ModuleCat ℤ)) (u : S.X₂ →ₗ[ℤ] ℂ)
    (hu : u.comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ)) := s4_c1a6_boundaryTorsionDesc S u hu

example (S : ShortComplex (ModuleCat ℤ)) (u : S.X₂ →ₗ[ℤ] ℂ)
    (hu : u.comp S.f.hom = (0 : S.X₁ →ₗ[ℤ] ℂ)) (z : S.cycles) :
    pairing S u hu (Submodule.Quotient.mk (S.homologyπ z)) = u (S.iCycles z) :=
  s4_c1a6_boundaryTorsionDesc_cycle S u hu z

/-- Actual complex cocycle evaluation on the integral torsion quotient.
Source: Hatcher, Algebraic Topology, §3.1; C1a6IntegralCoefficients. -/
def cocyclePairing (X : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) (1 : ℕ)) :
    Lattice X →ₗ[ℤ] ℂ := s4_c1a6_integralCocyclePairing X ψ

example (X : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj X) (1 : ℕ))
    (z : (ZChains X).cycles (1 : ℕ)) :
    cocyclePairing X ψ (Submodule.Quotient.mk ((ZChains X).homologyπ (1 : ℕ) z)) =
      ψ.val (s4_c1a6_zToCChainGroup X (1 : ℕ) ((ZChains X).iCycles (1 : ℕ) z)) :=
  s4_c1a6_integralCocyclePairing_cycle X ψ z

/-- Transport an integral family of linear functionals through a specified form equivalence.
Source: Bourbaki, Algebra, chapter II, §2, dual maps. -/
def transport {A F G : Type} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (j : A →ₗ[ℤ] Module.Dual ℂ G) (φ : F ≃ₗ[ℂ] G) :
    A →ₗ[ℤ] Module.Dual ℂ F :=
  ((φ.toLinearMap.dualMap).restrictScalars ℤ).comp j

example {A F G : Type} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup F] [Module ℂ F] [AddCommGroup G] [Module ℂ G]
    (j : A →ₗ[ℤ] Module.Dual ℂ G) (φ : F ≃ₗ[ℂ] G) (a : A) (θ : F) :
    transport j φ a θ = j a (φ θ) := rfl

/-- B3's integral periods as actual linear functionals.
Source: Forster, Lectures on Riemann Surfaces, §21; b3A_lattice_mem_linearDual and b3A_toDual. -/
def surfacePeriod {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] :
    b3_periodLattice E C →ₗ[ℤ] Module.Dual ℂ (b3_HolForm E C) where
  toFun l := b3A_toDual ⟨l.val, b3A_lattice_mem_linearDual l⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

example {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (γ : b3_SmoothLoop E C) (θ : b3_HolForm E C) :
    surfacePeriod (b3_latticePeriod E C γ) θ = b3_pathIntegral E C γ.val θ := rfl
end HodgeLean.Foundations.IntegralHomology.StageThree
