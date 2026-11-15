import HodgeLean.Adapters.CycleClassFlatPullbackDefs
import HodgeLean.Adapters.GagaMaps
import HodgeLean.Papers.G32DominanceDefs
import HodgeLean.Papers.G34BoundaryDefs

/-! # Shared program vocabulary: definitions -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Papers HodgeLean.RealDefs
open scoped CategoryTheory.MonObj

namespace HodgeLean.Foundations.Program

/-- A smooth proper commutative group scheme whose geometric fibres are integral.
Source: Mumford, *Abelian Varieties*, Ch. 6; Faltings--Chai, *Degeneration of Abelian
Varieties*, Ch. I, §1. -/
structure RelativeAbelianScheme (S : Scheme) where
  total : Over S
  smooth : Smooth total.hom
  proper : IsProper total.hom
  group : GrpObj total
  commutative : IsCommMonObj total
  geometricallyIntegral : GeometricallyIntegral total.hom

example (S : Scheme) (A : Over S) [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [IsCommMonObj A] [GeometricallyIntegral A.hom] : RelativeAbelianScheme S :=
  ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- A matrix algebraic group presented by polynomial equations inside the invertible matrices.
Source: Borel, *Linear Algebraic Groups*, Ch. I, §1. -/
structure MatrixAlgGroup (k : Type*) [Field k] (n : ℕ) where
  equations : Ideal (MvPolynomial (Fin n × Fin n) k)
  carrier : Subgroup (Matrix.GeneralLinearGroup (Fin n) k)
  equations_iff : ∀ g, g ∈ carrier ↔
    ∀ f ∈ equations, MvPolynomial.eval (fun ij ↦ (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2) f = 0

example (k : Type*) [Field k] (n : ℕ) : MatrixAlgGroup k n where
  equations := ⊥
  carrier := ⊤
  equations_iff := by simp

/-- The common analytic fields of the G32 and G34 period-map interfaces.
Source: Griffiths, *Periods of integrals on algebraic manifolds III*, Publ. Math. IHES 38. -/
structure FamilyPeriodMap (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B] where
  domain : Set A
  isOpen_domain : IsOpen domain
  domain_nonempty : domain.Nonempty
  period : A → B
  analytic : AnalyticOnNhd ℂ period domain
  target : Set B
  mapsTo : Set.MapsTo period domain target

example {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] : FamilyPeriodMap A B where
  domain := Set.univ
  isOpen_domain := isOpen_univ
  domain_nonempty := Set.univ_nonempty
  period := 0
  analytic := analyticOnNhd_const
  target := Set.univ
  mapsTo := Set.mapsTo_univ _ _

end HodgeLean.Foundations.Program
