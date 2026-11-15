import HodgeLean.Foundations.Program.SchoenCycleS3CotangentCoordinates
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Bases for conormal modules of coordinate ideals -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The conormal coordinate maps are linear over the quotient coordinate ring. -/
def s2e_cotangentCoordinateQuotient {R σ : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (i : σ) :
    I.Cotangent →ₗ[MvPolynomial σ R ⧸ I] MvPolynomial σ R ⧸ I where
  toFun := s2e_cotangentCoordinate I i
  map_add' := (s2e_cotangentCoordinate I i).map_add
  map_smul' a x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change s2e_cotangentCoordinate I i (a • x) = a • s2e_cotangentCoordinate I i x
    exact (s2e_cotangentCoordinate I i).map_smul a x

/-- Distinct polynomial coordinates have independent classes in the conormal module. -/
theorem s2e_coordinate_classes_independent {R σ τ : Type*} [CommRing R]
    (I : Ideal (MvPolynomial σ R)) (e : τ ↪ σ) (he : ∀ j, X (e j) ∈ I) :
    LinearIndependent (MvPolynomial σ R ⧸ I)
      (fun j => I.toCotangent ⟨X (e j), he j⟩) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha j hj
  have h := congrArg (s2e_cotangentCoordinateQuotient I (e j)) ha
  simp only [map_sum, map_smul, map_zero] at h
  simp only [s2e_cotangentCoordinateQuotient, LinearMap.coe_mk, AddHom.coe_mk,
    s2e_cotangentCoordinate_variable] at h
  simpa only [EmbeddingLike.apply_eq_iff_eq, smul_eq_mul, mul_ite, mul_zero,
    mul_one, Finset.sum_ite_eq', ite_eq_left hj] using h

/-- The classes of ideal generators span its conormal module over the quotient ring. -/
theorem s2e_cotangent_generators_span {A τ : Type*} [CommRing A]
    (f : τ → A) :
    let I := Ideal.span (Set.range f)
    ⊤ ≤ Submodule.span (A ⧸ I)
      (Set.range (fun j => I.toCotangent ⟨f j, Ideal.subset_span ⟨j, rfl⟩⟩)) := by
  dsimp only
  let I := Ideal.span (Set.range f)
  let N := Submodule.span (A ⧸ I)
    (Set.range (fun j => I.toCotangent ⟨f j, Ideal.subset_span ⟨j, rfl⟩⟩))
  intro z hz
  clear hz
  obtain ⟨⟨a, ha⟩, rfl⟩ := I.toCotangent_surjective z
  change I.toCotangent ⟨a, ha⟩ ∈ N
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    exact Submodule.subset_span ⟨j, rfl⟩
  | zero =>
    exact N.zero_mem
  | add a b ha hb hia hib =>
    change I.toCotangent (⟨a, ha⟩ + ⟨b, hb⟩) ∈ N
    rw [map_add]
    exact N.add_mem hia hib
  | smul c a ha hi =>
    change I.toCotangent (c • ⟨a, ha⟩) ∈ N
    rw [map_smul]
    exact N.smul_mem (Ideal.Quotient.mk I c) hi

/-- The coordinate generators give a basis of the affine coordinate conormal module. -/
def s2e_coordinateCotangentBasis {R σ τ : Type*} [CommRing R]
    (e : τ ↪ σ) :
    let I := Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))
    Module.Basis τ (MvPolynomial σ R ⧸ I) I.Cotangent :=
  Module.Basis.mk
    (s2e_coordinate_classes_independent
      (Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R))))
      e (fun j => Ideal.subset_span ⟨j, rfl⟩))
    (s2e_cotangent_generators_span (fun j => (X (e j) : MvPolynomial σ R)))

/-- This basis consists of the actual coordinate classes, with multiplicity one. -/
theorem s2e_coordinateCotangentBasis_apply {R σ τ : Type*} [CommRing R]
    (e : τ ↪ σ) (j : τ) :
    s2e_coordinateCotangentBasis (R := R) e j =
      (Ideal.span (Set.range (fun j => (X (e j) : MvPolynomial σ R)))).toCotangent
        ⟨X (e j), Ideal.subset_span ⟨j, rfl⟩⟩ :=
  Module.Basis.mk_apply _ _ _

end HodgeLean.Foundations.Program
