import HodgeLean.Foundations.Program.UniversalFamily

/-! # B6-0c: geometric Hermitian spaces

The implication from polarized Weil membership to coverage uses the actual rational
cohomology and its polarization. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
namespace HodgeLean.Foundations.Program

/-- The quadratic-field generator on rational cohomology.
Source: G32 v0.16, Definition 2.1. -/
def b60c_J (P : g32t_Sixfold) :
    {J : Module.End ℚ (HQ P.X 1) // J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨P.W.J, P.W.J_sq⟩

example (P : g32t_Sixfold) : (b60c_J P).1 = P.W.J := rfl

/-- The Hermitian space underlying a member, before choosing a basis.
Source: van Geemen, LNM 1594, §5.2; `WeilHermitian.WithJ`. -/
abbrev b60c_V (P : g32t_Sixfold) := WithJ (HQ P.X 1) (b60c_J P)

example (P : g32t_Sixfold) : Module (QuadraticAlgebra ℚ (-3) 0) (b60c_V P) :=
  inferInstance

/-- The Hermitian form determined by the given polarization, with the repository's
normalization `E(x,Jy) + ω E(x,y)`.
Source: van Geemen, LNM 1594, §5.2; `WeilHermitian.weilHermitian`. -/
def b60c_H (P : g32t_Sixfold) (hP : g32t_IsMember P) :=
  weilHermitian (polarizationForm (torusCohomology_cupProductOf P.X) hP.nondegenerate)
    (b60c_J P)
    (by simpa [polarizationForm, b60c_J] using
      (isRosatiSkew_iff_dualForm hP.nondegenerate P.W.J).1 hP.rosati)

example (P : g32t_Sixfold) (hP : g32t_IsMember P) : b60c_H P hP 0 0 = 0 := by
  simp only [map_zero, LinearMap.zero_apply]

/-- The Hodge (1,0) subspace in complexified rational cohomology.
Source: van Geemen, LNM 1594, §§5.1–5.3; the abelian Hodge decomposition. -/
def b60c_F (P : g32t_Sixfold) : Submodule ℂ (ℂ ⊗[ℚ] HQ P.X 1) :=
  letI := (torusCohomology_cupProductOf P.X).finite
  (abelianVarietyCohomologyOf (finiteBetti_abelian P.X)
    (spec_bettiDeRhamIso_abelian P.X) (hodgeDecomposition_of_abelian P.X)
    (torusCohomology_cupProductOf P.X)).weight1.H (1, 0)

example (P : g32t_Sixfold) : (0 : ℂ ⊗[ℚ] HQ P.X 1) ∈ b60c_F P :=
  Submodule.zero_mem _

end HodgeLean.Foundations.Program
