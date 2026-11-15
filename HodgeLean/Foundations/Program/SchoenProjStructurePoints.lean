import Mathlib.RingTheory.Ideal.Quotient.Basic
import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The scheme chart map agrees on points with the locally ringed-space construction. -/
theorem s2_proj_basicOpenToSpec_apply {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : A) (x : (Proj.basicOpen 𝒜 f).toScheme) :
    Proj.basicOpenToSpec 𝒜 f x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x := by
  apply PrimeSpectrum.ext
  rfl

/-- The structure morphism of Proj contracts a homogeneous prime to degree zero. -/
theorem s2_proj_toSpecZero_mem {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ (Proj.toSpecZero 𝒜 x).asIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal := by
  let y := (Scheme.isoOfEq (Proj 𝒜) (Proj.basicOpen_one 𝒜)).inv
    ((Scheme.topIso (Proj 𝒜)).inv x)
  have h : HomogeneousLocalization.fromZeroRingHom 𝒜 _ a ∈
      ((Proj.basicOpenToSpec 𝒜 1) y).asIdeal ↔ (a : A) ∈ y.1.asHomogeneousIdeal := by
    rw [s2_proj_basicOpenToSpec_apply]
    exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 y
      ⟨0, a, ⟨1, SetLike.one_mem_graded 𝒜⟩, ⟨0, by simp⟩⟩
  have hy : y.1 = x := by
    change (Proj.basicOpen 𝒜 (1 : A)).ι y = x
    dsimp only [y]
    rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι,
      ← Scheme.Hom.comp_apply, Scheme.toIso_inv_ι]
    rfl
  rw [hy] at h
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) y).asIdeal ↔ (a : A) ∈ x.asHomogeneousIdeal
  exact h

/-- The structure map of polynomial Proj expressed over its coefficient ring. -/
def s2_polynomialProj_toBaseRing (R σ : Type) [CommRing R] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
    Proj (MvPolynomial.homogeneousSubmodule σ R) ⟶ Spec (CommRingCat.of R) :=
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom (ProjectiveSpace.degreeZeroEquiv σ R).symm.toRingHom)

/-- Contraction along polynomial Proj's structure map tests membership of constants. -/
theorem s2_polynomialProj_toBaseRing_mem (R σ : Type) [CommRing R] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
    ∀ (x : Proj (MvPolynomial.homogeneousSubmodule σ R)) (r : R),
      r ∈ (s2_polynomialProj_toBaseRing R σ x).asIdeal ↔
        MvPolynomial.C r ∈ x.asHomogeneousIdeal := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  intro x r
  exact s2_proj_toSpecZero_mem (MvPolynomial.homogeneousSubmodule σ R) x
    ((ProjectiveSpace.degreeZeroEquiv σ R).symm r)

/-- A compatible map to a field spectrum forces constants to inject at each
homogeneous prime reached by a scheme morphism. -/
theorem s2_polynomialProj_constants_injective_of_structure
    (R K σ : Type) [CommRing R] [Field K] (φ : R →+* K)
    (hφ : Function.Injective φ) (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of K)) :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
    ∀ f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R),
      f ≫ s2_polynomialProj_toBaseRing R σ = s ≫ Spec.map (CommRingCat.ofHom φ) →
      ∀ x : X, Function.Injective
        ((Ideal.Quotient.mk (f x).asHomogeneousIdeal.toIdeal).comp MvPolynomial.C) := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  intro f hcomm x
  apply (injective_iff_map_eq_zero _).mpr
  intro r hr
  have hm : MvPolynomial.C r ∈ (f x).asHomogeneousIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hr
  have hm' := (s2_polynomialProj_toBaseRing_mem R σ (f x) r).mpr hm
  have he := congrArg (fun k : X ⟶ Spec (CommRingCat.of R) => k x) hcomm
  change s2_polynomialProj_toBaseRing R σ (f x) =
    Spec.map (CommRingCat.ofHom φ) (s x) at he
  rw [he] at hm'
  change φ r ∈ (s x).asIdeal at hm'
  haveI : (s x).asIdeal.IsPrime := (s x).isPrime
  rw [Ideal.eq_bot_of_prime (s x).asIdeal] at hm'
  apply hφ
  simpa only [Ideal.mem_bot, map_zero] using hm'

end HodgeLean.Foundations.Program
