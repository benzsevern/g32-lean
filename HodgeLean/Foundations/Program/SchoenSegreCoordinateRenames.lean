import HodgeLean.Foundations.Program.TorusAlgebraizationB54Immersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MvPolynomial AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual graded polynomial coordinate rename induced by a permutation of tuple factors. -/
def s2_segreCoordinateRename (R : Type) [CommRing R] (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    homogeneousSubmodule (Fin n → Fin (d + 1)) R →+*ᵍ
      homogeneousSubmodule (Fin n → Fin (d + 1)) R :=
  { (MvPolynomial.rename (fun b i => b (σ i))).toRingHom with
    map_mem := by
      intro m p hp
      rw [mem_homogeneousSubmodule] at hp ⊢
      exact hp.rename_isHomogeneous }

/-- The actual graded Segre coordinate rename has its prescribed value on every polynomial variable. -/
theorem s2_segreCoordinateRename_X (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) (b : Fin n → Fin (d + 1)) :
    s2_segreCoordinateRename R d n σ (X b) = X (fun i => b (σ i)) := by
  change MvPolynomial.rename (fun b i => b (σ i)) (X b) = _
  exact MvPolynomial.rename_X _ _

/-- Every actual graded Segre coordinate permutation is surjective on the polynomial ring. -/
theorem s2_segreCoordinateRename_surjective (R : Type) [CommRing R] (d n : ℕ)
    (σ : Equiv.Perm (Fin n)) : Function.Surjective (s2_segreCoordinateRename R d n σ) := by
  intro p
  refine ⟨MvPolynomial.rename (fun b i => b (σ.symm i)) p, ?_⟩
  change MvPolynomial.rename (fun b i => b (σ i))
    (MvPolynomial.rename (fun b i => b (σ.symm i)) p) = p
  simp only [MvPolynomial.rename_rename, Function.comp_def, Equiv.symm_apply_apply]
  change MvPolynomial.rename (id : (Fin n → Fin (d + 1)) → (Fin n → Fin (d + 1))) p = p
  exact MvPolynomial.rename_id_apply p

/-- The actual Proj scheme morphism induced by a permutation of Segre tuple coordinates. -/
def s2_segreCoordinateMap (R : Type) [CommRing R] (d n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Proj (homogeneousSubmodule (Fin n → Fin (d + 1)) R) ⟶
      Proj (homogeneousSubmodule (Fin n → Fin (d + 1)) R) :=
  Proj.map (s2_segreCoordinateRename R d n σ)
    (b54_irrelevant_le_map_of_surjective _ (s2_segreCoordinateRename_surjective R d n σ))

end HodgeLean.Foundations.Program
