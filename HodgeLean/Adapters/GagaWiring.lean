import HodgeLean.Adapters.GagaMaps
import HodgeLean.Adapters.AbelianEndomorphisms3

/-! # GAGA wiring for abelian endomorphisms -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Manifold ContDiff CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A lattice-preserving complex-linear map is induced by an abelian endomorphism, using GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., Proposition 1.2.1 and §1.2. -/
theorem gagaw_spec_exists_abelianEnd_of_lattice [IsCommMonObj X]
    (A : (Fin (dim X.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X) :
    ∃ f : AbelianEnd X, ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v)) :=
  spec_exists_abelianEnd_of_lattice X (gagam_hAlg X) A hA

/-- The analytic representation has precisely the lattice-preserving range, using GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Birkenhake–Lange, *Complex Abelian
Varieties*, 2nd ed., Proposition 1.2.1 and §1.2. -/
theorem gagaw_spec_analyticRepresentation_range [IsCommMonObj X] :
    ∃ ρa : AbelianEnd X →+* Module.End ℂ (Fin (dim X.left) → ℂ),
      (∀ f v, Additive.toMul (complexExponential X (dim X.left) (ρa f v)) =
        Point.map f.hom (Additive.toMul (complexExponential X (dim X.left) v))) ∧
      Function.Injective ρa ∧
      Set.range ρa = {A | ∀ l ∈ abelianPeriodLattice X, A l ∈ abelianPeriodLattice X} :=
  spec_analyticRepresentation_range X (gagam_hAlg X)

/-- A rational Hodge endomorphism has a positive integral multiple induced by an abelian
endomorphism, using GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Mumford, *Abelian Varieties*, §19. -/
theorem gagaw_spec_exists_abelianEnd_of_hodge [IsCommMonObj X]
    (T : Module.End ℚ (HQ X 1))
    (hT : (complexHolomorphicH1 X).map (T.baseChange ℂ) ≤ complexHolomorphicH1 X) :
    ∃ N : ℕ, 0 < N ∧ ∃ f : AbelianEnd X, abelianEndAction X f = (N : ℚ) • T :=
  spec_exists_abelianEnd_of_hodge X (gagam_hAlg X) T hT

/-- The rational abelian-endomorphism action has the Hodge endomorphisms as its range, using
GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Mumford, *Abelian Varieties*, §19 and §22. -/
theorem gagaw_spec_abelianEnd0Action_range [IsCommMonObj X] :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧ Function.Injective ρ ∧
        ρ.range = (hodgeEndH1 X).op :=
  spec_abelianEnd0Action_range X (gagam_hAlg X)

/-- The Hodge-Lie commutant is the image of the rational abelian-endomorphism action, using
GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Moonen, *An introduction to Mumford–Tate
groups* (2004), §1–2. -/
theorem gagaw_spec_centralizer_hodgeLieAlgebra_eq [IsCommMonObj X]
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) :
    ∃ ρ : AbelianEnd0 X →ₐ[ℚ] (Module.End ℚ (HQ X 1))ᵐᵒᵖ,
      (∀ f, ρ (1 ⊗ₜ f) = MulOpposite.op (abelianEndAction X f)) ∧
        Subalgebra.centralizer ℚ
            (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
          ρ.range.unop :=
  spec_centralizer_hodgeLieAlgebra_eq X (gagam_hAlg X) hH

/-- A singly generated rational endomorphism algebra gives the corresponding commutant
description, using GAGA.
Source: Serre, GAGA (1956), §3, Proposition 13; Moonen, *An introduction to Mumford–Tate
groups* (2004), §1–2. -/
theorem gagaw_spec_centralizer_eq_adjoin_of_adjoin_eq_top [IsCommMonObj X]
    (hH : DirectSum.IsInternal (latticeHodgePieces X)) (j : AbelianEnd X)
    (hK : Algebra.adjoin ℚ {(1 : ℚ) ⊗ₜ[ℤ] j} = (⊤ : Subalgebra ℚ (AbelianEnd0 X))) :
    Subalgebra.centralizer ℚ
        (hodgeLieAlgebra (latticeHodgePieces X) hH : Set (Module.End ℚ (HQ X 1))) =
      Algebra.adjoin ℚ {abelianEndAction X j} :=
  spec_centralizer_eq_adjoin_of_adjoin_eq_top X (gagam_hAlg X) hH j hK

/-- info: 'HodgeLean.Adapters.gagaw_spec_exists_abelianEnd_of_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_exists_abelianEnd_of_lattice

/-- info: 'HodgeLean.Adapters.gagaw_spec_analyticRepresentation_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_analyticRepresentation_range

/-- info: 'HodgeLean.Adapters.gagaw_spec_exists_abelianEnd_of_hodge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_exists_abelianEnd_of_hodge

/-- info: 'HodgeLean.Adapters.gagaw_spec_abelianEnd0Action_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_abelianEnd0Action_range

/-- info: 'HodgeLean.Adapters.gagaw_spec_centralizer_hodgeLieAlgebra_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_centralizer_hodgeLieAlgebra_eq

/-- info: 'HodgeLean.Adapters.gagaw_spec_centralizer_eq_adjoin_of_adjoin_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms gagaw_spec_centralizer_eq_adjoin_of_adjoin_eq_top

end HodgeLean.Adapters
