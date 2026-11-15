import HodgeLean.Adapters.CyclePushforward

/-! # Geometric witness selection operations

Open refinement retains the original morphisms and cycle carrier.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.WitnessSelection

/-- The branch-free parameter open.
Source: Hartshorne, Algebraic Geometry, I.1, Zariski topology. -/
def branchComplement {T : Type*} [TopologicalSpace T] (B : Set T) (hB : IsClosed B) :
    Opens T := ⟨Bᶜ, hB.isOpen_compl⟩

example : (1 : ℝ) ∈ branchComplement ({0} : Set ℝ) isClosed_singleton := by
  simp [branchComplement]

/-- Refine an old parameter open without changing any geometric data.
Source: Hartshorne, Algebraic Geometry, I.1, intersection of open subsets. -/
def reselectedOpen {T : Type*} [TopologicalSpace T] (V U : Opens T) : Opens T := V ⊓ U

example : (1 : ℝ) ∈ reselectedOpen (branchComplement ({0} : Set ℝ) isClosed_singleton) ⊤ := by
  simp [reselectedOpen, branchComplement]

/-- Restrict the original comparison map, retaining its scheme morphism.
Source: Hartshorne, Algebraic Geometry, II.2, restriction to open subschemes. -/
def retainedComparison {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) := f ∣_ U

example {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens) :
    retainedComparison f U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := morphismRestrict_ι f U

/-- Structure map on the branch-free part of the original cover.
Source: Hartshorne, Algebraic Geometry, III.10, composition of smooth morphisms. -/
def originalCoverMap {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) (U : Y.Opens) :=
  retainedComparison f U ≫ U.ι ≫ s

example {X Y S : Scheme} (f : X ⟶ Y) (s : Y ⟶ S) (U : Y.Opens) :
    originalCoverMap f s U = (f ⁻¹ᵁ U).ι ≫ f ≫ s := by
  rw [originalCoverMap, ← Category.assoc, retainedComparison, morphismRestrict_ι,
    Category.assoc]

/-- Push the actual rational cycle, including residue degrees and cancellations.
Source: Fulton, Intersection Theory, second edition, §1.4. -/
def pushedCycle {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f]
    (c : AlgebraicCycle X ℚ) : AlgebraicCycle Y ℚ :=
  HodgeLean.Adapters.a1p_pushforward f c

example {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [DecidableEq X] [DecidableEq Y]
    (x : X) : pushedCycle f (Function.locallyFinsuppWithin.single x (2 : ℚ)) =
      Function.locallyFinsuppWithin.single (f x)
        ((2 : ℚ) * HodgeLean.Adapters.a1p_degree f x) :=
  HodgeLean.Adapters.a1p_pushforward_single f x 2

end HodgeLean.WitnessSelection
