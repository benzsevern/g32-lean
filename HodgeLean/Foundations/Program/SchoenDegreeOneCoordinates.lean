import HodgeLean.Foundations.Program.TorusAlgebraizationB54Projective
import HodgeLean.Foundations.Program.SchoenHomogeneousGeneratorIdeal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program

/-- Homogeneous polynomial evaluation respects a degree-one additive-subgroup grading. -/
theorem s2_eval₂_mem_grade {A R ι : Type} [CommRing A] [CommRing R]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (c : R →+* A) (hc : ∀ r, c r ∈ 𝒜 0) (v : ι → A) (hv : ∀ i, v i ∈ 𝒜 1)
    {n : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂Hom c v p ∈ 𝒜 n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => exact (𝒜 n).zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using (𝒜 n).add_mem ihp ihq
  | monomial d r hd =>
    rw [MvPolynomial.eval₂Hom_monomial]
    have h := SetLike.prod_pow_mem_graded 𝒜 (fun _ : ι => 1) v d
      (fun i (_ : i ∈ d.support) => hv i)
    have hp : (d.prod fun i k => v i ^ k) ∈ 𝒜 n := by
      simpa [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, Pi.one_apply] using hd ▸ h
    simpa only [zero_add] using SetLike.mul_mem_graded (hc r) hp

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Integer polynomial coordinates for an actual degree-one additive-subgroup grading. -/
def s2_integralGradedCoordinates {A ι : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (hv : ∀ i, v i ∈ 𝒜 1) :
    homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ 𝒜 :=
  { eval₂Hom ((Int.castRingHom A).comp ULift.ringEquiv.toRingHom) v with
    map_mem := s2_eval₂_mem_grade 𝒜 _ (by
      intro c
      change (c.down : A) ∈ 𝒜 0
      have h := map_intCast (algebraMap (𝒜 0) A) c.down
      rw [← h]
      exact (c.down : 𝒜 0).property) v hv }

/-- Degree-one generators give the irrelevant-ideal bound for the actual integer coordinates. -/
theorem s2_integralCoordinates_irrelevant {A ι : Type} [CommRing A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (hv : ∀ i, v i ∈ 𝒜 1)
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    HomogeneousIdeal.irrelevant 𝒜 ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule ι (ULift.{0} ℤ))).map
        (s2_integralGradedCoordinates 𝒜 v hv) := by
  apply (s2_irrelevant_le_span_homogeneous_generators 𝒜 v
    (fun i => ⟨1, zero_lt_one, hv i⟩) hgen).trans
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  have hX : s2_integralGradedCoordinates 𝒜 v hv (X i) = v i := by
    simp [s2_integralGradedCoordinates]
  rw [← hX]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _
    zero_lt_one (isHomogeneous_X _ i))

end HodgeLean.Foundations.Program
