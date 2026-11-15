import HodgeLean.Foundations.Program.SchoenCycleProjCoordinateImmersion
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # The standard coordinate inclusion for the initial flag -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Coordinate projection over the actual coefficient ring. -/
def pairedC3GradedCoordinateProjection {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    homogeneousSubmodule ι A →+*ᵍ homogeneousSubmodule κ A where
  __ := (MvPolynomial.killCompl (R := A) e.injective).toRingHom
  map_mem := by
    classical
    intro d p hp
    change (MvPolynomial.killCompl (R := A) e.injective p).IsHomogeneous d
    dsimp only [MvPolynomial.killCompl]
    have hh (j : ι) :
        (if h : j ∈ Set.range e then
          (X ((Equiv.ofInjective e e.injective).symm ⟨j, h⟩) : MvPolynomial κ A)
        else 0).IsHomogeneous 1 := by
      split_ifs
      · exact isHomogeneous_X _ _
      · exact isHomogeneous_zero κ A 1
    simpa only [one_mul] using hp.aeval _ hh

/-- Inclusion of the retained homogeneous coordinates. -/
def pairedC3GradedCoordinateSection {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    homogeneousSubmodule κ A →+*ᵍ homogeneousSubmodule ι A where
  __ := (MvPolynomial.rename e).toRingHom
  map_mem := fun h => h.rename_isHomogeneous

/-- Coordinate projection is split by coordinate inclusion. -/
theorem paired_c3_graded_coordinate_retraction {A ι κ : Type} [CommRing A] (e : κ ↪ ι)
    (p : MvPolynomial κ A) :
    pairedC3GradedCoordinateProjection e (pairedC3GradedCoordinateSection e p) = p :=
  MvPolynomial.killCompl_rename_app e.injective p

/-- The projective coordinate inclusion over the coefficient ring. -/
def pairedC3PolynomialCoordinateInclusion {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    Proj (homogeneousSubmodule κ A) ⟶ Proj (homogeneousSubmodule ι A) :=
  Proj.map (pairedC3GradedCoordinateProjection e)
    (s2e_irrelevant_le_map_of_graded_retraction _ _
      (pairedC3GradedCoordinateProjection e) (pairedC3GradedCoordinateSection e)
      (paired_c3_graded_coordinate_retraction e))

/-- The projective coordinate inclusion is a scheme closed immersion. -/
theorem paired_c3_polynomial_coordinate_inclusion_immersion
    {A ι κ : Type} [CommRing A] (e : κ ↪ ι) :
    IsClosedImmersion (pairedC3PolynomialCoordinateInclusion (A := A) e) :=
  s2e_proj_map_isClosedImmersion_of_graded_retraction _ _
    (pairedC3GradedCoordinateProjection e) (pairedC3GradedCoordinateSection e)
    (paired_c3_graded_coordinate_retraction e) _

/-- The retained coordinates are the first k+1 of the k+r coordinates. -/
def pairedC3InitialCoordinateEmbedding (k r : ℕ) (hr : 0 < r) : Fin (k + 1) ↪ Fin (k + r) :=
  ⟨fun i => ⟨i.val, by omega⟩,
    fun i j h => Fin.ext (congrArg (fun x : Fin (k + r) => x.val) h)⟩

/-- The standard inclusion has precisely the original parameter source
and the full-fibre target of the geometric flag. -/
def pairedC3InitialCoordinateInclusion (k r : ℕ) (hr : 0 < r) :
    pairedC3Proj k ⟶ ProjectiveSpace (Fin (k + r)) (Spec ↧ℂ) :=
  pairedC3PolynomialCoordinateInclusion (A := ℂ) (pairedC3InitialCoordinateEmbedding k r hr) ≫
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + r))).hom

/-- The standard initial inclusion is a closed immersion. -/
theorem paired_c3_initial_coordinate_inclusion_immersion (k r : ℕ) (hr : 0 < r) :
    IsClosedImmersion (pairedC3InitialCoordinateInclusion k r hr) := by
  letI := paired_c3_polynomial_coordinate_inclusion_immersion
    (A := ℂ) (pairedC3InitialCoordinateEmbedding k r hr)
  dsimp only [pairedC3InitialCoordinateInclusion]
  infer_instance

/-- Retaining every coordinate gives the identity graded homomorphism. -/
theorem paired_c3_graded_coordinate_projection_refl {A ι : Type} [CommRing A] :
    pairedC3GradedCoordinateProjection (A := A) (Function.Embedding.refl ι) =
      GradedRingHom.id _ := by
  ext p : 1
  change MvPolynomial.killCompl (R := A) (Function.injective_id) p = p
  simpa only [MvPolynomial.rename_id_apply] using
    (MvPolynomial.killCompl_rename_app (R := A) (f := id) Function.injective_id p)

/-- With no discarded coordinates the initial inclusion is exactly the
polynomial comparison isomorphism. -/
theorem paired_c3_initial_coordinate_inclusion_one (k : ℕ) :
    pairedC3InitialCoordinateInclusion k 1 (by omega) =
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom := by
  have he : pairedC3InitialCoordinateEmbedding k 1 (by omega) =
      Function.Embedding.refl (Fin (k + 1)) := by
    ext i
    rfl
  unfold pairedC3InitialCoordinateInclusion pairedC3PolynomialCoordinateInclusion
  simp only [he, paired_c3_graded_coordinate_projection_refl, Proj.map_id, Category.id_comp]

end HodgeLean.Foundations.Program.G32Native
