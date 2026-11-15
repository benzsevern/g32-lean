import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
open scoped BigOperators
open MvPolynomial
namespace HodgeLean.Foundations.Program

/-- An invertible linear coefficient change, followed by a translation, gives polynomial coordinates. -/
theorem s2v_l1b_matrix_affine_coordinates
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι R) (hMN : M * N = 1) (hNM : N * M = 1) (p : ι → R) :
    ∃ e : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R,
      ∀ i, e (X i) = (∑ j, C (M i j) * X j) + C (p i) := by
  let L (A : Matrix ι ι R) (v : ι → MvPolynomial ι R) (i : ι) :=
    ∑ j, C (A i j) * v j
  have hLL (A B : Matrix ι ι R) (v : ι → MvPolynomial ι R) :
      L A (L B v) = L (A * B) v := by
    funext i
    simp only [L, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hLone (v : ι → MvPolynomial ι R) : L 1 v = v := by
    funext i
    simp [L, Matrix.one_apply]
  let F : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    aeval (L M X + fun i => C (p i))
  let G : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
    aeval (L N ((fun i => X i - C (p i))))
  have hmap (H : MvPolynomial ι R →ₐ[R] MvPolynomial ι R)
      (A : Matrix ι ι R) (v : ι → MvPolynomial ι R) (i : ι) :
      H (L A v i) = L A (fun j => H (v j)) i := by
    simp only [L, map_sum, map_mul, show ∀ r, H (C r) = C r from H.commutes]
  have hFG : F.comp G = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change F (G (X i)) = X i
    rw [show G (X i) = L N ((fun i => X i - C (p i))) i from aeval_X _ i, hmap]
    have hv : (fun j => F (((fun i => X i - C (p i))) j)) = L M X := by
      funext j
      change F (X j - C (p j)) = L M X j
      rw [map_sub, show F (X j) = L M X j + C (p j) from aeval_X _ j,
        show F (C (p j)) = C (p j) from F.commutes _]
      exact add_sub_cancel_right _ _
    rw [hv, hLL, hNM, hLone]
  have hGF : G.comp F = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    change G (F (X i)) = X i
    rw [show F (X i) = L M X i + C (p i) from aeval_X _ i,
      map_add, hmap, show G (C (p i)) = C (p i) from G.commutes _]
    have hv : (fun j => G (X j)) = L N ((fun i => X i - C (p i))) := by
      funext j
      exact aeval_X _ j
    rw [hv, hLL, hMN, hLone]
    exact sub_add_cancel _ _
  exact ⟨AlgEquiv.ofAlgHom F G hFG hGF, fun i => aeval_X _ i⟩

end HodgeLean.Foundations.Program
