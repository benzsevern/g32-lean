import Mathlib.RingTheory.Ideal.Quotient.Basic
import HodgeLean.Foundations.Program.SchoenPolynomialAvoidance
import HodgeLean.Foundations.Program.SchoenProjectiveAffineNeighborhoods

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The irrelevant ideal of a polynomial ring is contained in the ideal of its variables. -/
theorem s2_mvPolynomial_irrelevant_le_span_X
    (K σ : Type*) [CommRing K] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  rw [HomogeneousIdeal.irrelevant_eq_span]
  apply Ideal.span_le.mpr
  intro f hf
  obtain ⟨d, hf⟩ := Set.mem_iUnion.mp hf
  obtain ⟨hd, hf⟩ := Set.mem_iUnion.mp hf
  rw [← Set.image_univ]
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro m hm
  suffices ∃ j, m j ≠ 0 by simpa using this
  by_contra! h
  have hm0 : m = 0 := by ext j; exact h j
  subst m
  have hhom : f.IsHomogeneous d := hf
  have hz := hhom.coeff_eq_zero (show (0 : σ →₀ ℕ).degree ≠ d by simpa using hd.ne)
  exact (MvPolynomial.mem_support_iff.mp hm) hz


/-- A relevant homogeneous prime of a polynomial ring misses a coordinate variable. -/
theorem s2_polynomialProj_exists_variable_not_mem (R σ : Type*) [CommRing R] :
    letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
    ∀ x : Proj (MvPolynomial.homogeneousSubmodule σ R),
      ∃ j : σ, MvPolynomial.X j ∉ x.asHomogeneousIdeal := by
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  intro x
  by_contra! h
  apply x.not_irrelevant_le
  apply (s2_mvPolynomial_irrelevant_le_span_X R σ).trans
  exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact h j)

/-- Finite families of polynomial Proj points over an infinite coefficient ring
have a common affine open when constants inject into their prime quotients. -/
theorem s2_polynomialProj_commonAffineOpen_of_constants_injective
    (R : Type*) [CommRing R] [Infinite R] (n : ℕ) (ι : Type*) [Finite ι] :
    letI := MvPolynomial.gradedAlgebra (σ := Fin n) (R := R)
    ∀ x : ι → Proj (MvPolynomial.homogeneousSubmodule (Fin n) R),
      (∀ i, Function.Injective
        ((Ideal.Quotient.mk (x i).asHomogeneousIdeal.toIdeal).comp MvPolynomial.C)) →
      ∃ f : MvPolynomial (Fin n) R, f.IsHomogeneous 1 ∧
        IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) f) ∧
        ∀ i, x i ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) f := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := Fin n) (R := R)
  intro x hinj
  let B (i : ι) := MvPolynomial (Fin n) R ⧸ (x i).asHomogeneousIdeal.toIdeal
  letI (i : ι) : CommRing (B i) := inferInstance
  letI (i : ι) : (x i).asHomogeneousIdeal.toIdeal.IsPrime := (x i).isPrime
  letI (i : ι) : IsDomain (B i) := by dsimp [B]; infer_instance
  let φ (i : ι) : R →+* B i :=
    (Ideal.Quotient.mk (x i).asHomogeneousIdeal.toIdeal).comp MvPolynomial.C
  let c (i : ι) (j : Fin n) : B i := Ideal.Quotient.mk _ (MvPolynomial.X j)
  have hc (i : ι) : ∃ j, c i j ≠ 0 := by
    obtain ⟨j, hj⟩ := s2_polynomialProj_exists_variable_not_mem R (Fin n) (x i)
    exact ⟨j, fun hz => hj (Ideal.Quotient.eq_zero_iff_mem.mp hz)⟩
  obtain ⟨t, ht⟩ := s2_powerWeighted_sum_simultaneous_ne_zero R ι B φ hinj n c hc
  let f : MvPolynomial (Fin n) R := ∑ j : Fin n, MvPolynomial.C (t ^ j.val) * MvPolynomial.X j
  have hf : f.IsHomogeneous 1 := by
    change f ∈ MvPolynomial.homogeneousSubmodule (Fin n) R 1
    apply Submodule.sum_mem
    intro j _
    exact (MvPolynomial.isHomogeneous_X R j).C_mul (t ^ j.val)
  refine ⟨f, hf, Proj.isAffineOpen_basicOpen _ f hf Nat.zero_lt_one, ?_⟩
  intro i hi
  apply ht i
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  simpa only [f, map_sum, map_mul, map_pow, φ, c, RingHom.comp_apply, mul_comm] using hz

end HodgeLean.Foundations.Program
