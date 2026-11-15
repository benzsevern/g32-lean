import HodgeLean.Foundations.Program.TorusAlgebraizationB54Immersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace HodgeLean.Foundations.Program

universe u
variable {R A ι : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (G : ℕ → Submodule R A) [GradedRing G]

theorem b54_aeval_mem_grade (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    {n : ℕ} {p : MvPolynomial ι R} (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval v p ∈ G n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simpa using (G n).add_mem ihp ihq
  | monomial d r hd =>
    rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
    apply (G n).smul_mem
    have h := SetLike.prod_pow_mem_graded G (fun _ : ι ↦ 1) v d
      (fun i (_ : i ∈ d.support) ↦ hv i)
    simpa [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, Pi.one_apply] using hd ▸ h

theorem b54_eval₂_mem_grade {R' : Type u} [CommRing R'] (c : R' →+* A) (hc : ∀ r, c r ∈ G 0)
    (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    {n : ℕ} {p : MvPolynomial ι R'} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂Hom c v p ∈ G n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simpa using (G n).add_mem ihp ihq
  | monomial d r hd =>
    rw [MvPolynomial.eval₂Hom_monomial]
    have h := SetLike.prod_pow_mem_graded G (fun _ : ι ↦ 1) v d
      (fun i (_ : i ∈ d.support) ↦ hv i)
    have hp : (d.prod fun i k ↦ v i ^ k) ∈ G n := by
      simpa [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, Pi.one_apply] using hd ▸ h
    simpa using SetLike.mul_mem_graded (hc r) hp

attribute [local instance] MvPolynomial.gradedAlgebra

def b54_gradedAeval (v : ι → A) (hv : ∀ i, v i ∈ G 1) :
    MvPolynomial.homogeneousSubmodule ι R →+*ᵍ G :=
  { (MvPolynomial.aeval v).toRingHom with
    map_mem := b54_aeval_mem_grade G v hv }

theorem b54_polynomial_proj_immersion (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hsurj : Function.Surjective (MvPolynomial.aeval (R := R) v)) :
    IsClosedImmersion (Proj.map (b54_gradedAeval G v hv)
      (b54_irrelevant_le_map_of_surjective (b54_gradedAeval G v hv) hsurj)) :=
  b54_proj_map_isClosedImmersion _ _ hsurj

theorem b54_pad_generators [Fintype ι] (v : ι → A) (hv : ∀ i, v i ∈ G 1)
    (hgen : Algebra.adjoin R (Set.range v) = ⊤) :
    ∃ w : Fin (Fintype.card ι + 1) → A,
      (∀ i, w i ∈ G 1) ∧ Algebra.adjoin R (Set.range w) = ⊤ := by
  classical
  let e : Option ι ≃ Fin (Fintype.card ι + 1) := Fintype.equivFinOfCardEq (by simp)
  let w : Fin (Fintype.card ι + 1) → A := fun i ↦ (e.symm i).elim 0 v
  refine ⟨w, ?_, ?_⟩
  · intro i
    dsimp [w]
    cases e.symm i with
    | none => exact (G 1).zero_mem
    | some j => exact hv j
  · apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨e (some i), by simp [w]⟩

end HodgeLean.Foundations.Program
