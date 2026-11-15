import HodgeLean.Foundations.Program.SchoenProjectiveSourceNeighborhoods
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A selected invariant affine neighborhood for each point of a projective scheme. -/
def s2_projectiveInvariantAffineOpen
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x : X) : X.Opens :=
  (s2_projective_invariantAffineNeighborhood K X s G ρ x).choose

/-- The selected neighborhood is affine, contains its point, and is invariant. -/
theorem s2_projectiveInvariantAffineOpen_spec
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x : X) :
    let U := s2_projectiveInvariantAffineOpen K X s G ρ x
    IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U :=
  (s2_projective_invariantAffineNeighborhood K X s G ρ x).choose_spec

/-- The selected invariant neighborhoods form an actual scheme open cover. -/
def s2_projectiveInvariantAffineCover
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) : X.OpenCover :=
  X.openCoverOfIsOpenCover (s2_projectiveInvariantAffineOpen K X s G ρ) (by
    apply le_antisymm le_top
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨x, (s2_projectiveInvariantAffineOpen_spec K X s G ρ x).2.1⟩)

/-- Every chart of the invariant source cover is an affine scheme. -/
theorem s2_projectiveInvariantAffineCover_isAffine
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x : X) :
    IsAffine ((s2_projectiveInvariantAffineCover K X s G ρ).X x) :=
  (s2_projectiveInvariantAffineOpen_spec K X s G ρ x).1

/-- Intersections of the selected invariant source charts are affine and invariant. -/
theorem s2_projectiveInvariantAffineOpen_inf_spec
    (K : Type) [Field K] [CharZero K] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of K)) [IsProjective s]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) (x y : X) :
    let U := s2_projectiveInvariantAffineOpen K X s G ρ x ⊓
      s2_projectiveInvariantAffineOpen K X s G ρ y
    IsAffineOpen U ∧ ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U := by
  haveI : IsAffine (CategoryTheory.Limits.terminal (Scheme.{0})) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso
      CategoryTheory.Limits.terminalIsTerminal).inv
  haveI : IsSeparated (CategoryTheory.Limits.terminal.from X) := by
    rw [← CategoryTheory.Limits.terminal.comp_from s]
    infer_instance
  have hx := s2_projectiveInvariantAffineOpen_spec K X s G ρ x
  have hy := s2_projectiveInvariantAffineOpen_spec K X s G ρ y
  refine ⟨hx.1.inf hy.1, ?_⟩
  intro g
  change (ρ g).asIso.hom ⁻¹ᵁ
    (s2_projectiveInvariantAffineOpen K X s G ρ x ⊓
      s2_projectiveInvariantAffineOpen K X s G ρ y) = _
  rw [Scheme.Hom.preimage_inf, hx.2.2 g, hy.2.2 g]

end HodgeLean.Foundations.Program
