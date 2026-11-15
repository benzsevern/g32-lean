import HodgeLean.Blocks.Weil.RationalKernel

/-! # Kernels of diagonal operators -/

noncomputable section

namespace HodgeBlocks

/-- A diagonal operator has no generalized zero eigenvectors beyond its kernel. -/
theorem apply_eq_zero_of_apply_apply_eq_zero_of_basis
    {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype ι]
    (b : Module.Basis ι K E) (T : E →ₗ[K] E) (c : ι → K)
    (hT : ∀ i, T (b i) = c i • b i) (x : E) (hx : T (T x) = 0) :
    T x = 0 := by
  classical
  have hcoord (y : E) (i : ι) : b.repr (T y) i = c i * b.repr y i := by
    let f : E →ₗ[K] K := (b.coord i).comp T
    let g : E →ₗ[K] K := c i • b.coord i
    have hfg : f = g := by
      apply b.ext
      intro j
      by_cases h : j = i
      · subst j; simp [f, g, hT]
      · simp [f, g, hT, Module.Basis.coord_apply, Finsupp.single_apply, h, Ne.symm h]
    exact DFunLike.congr_fun hfg y
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply, hcoord]
  have hi := congrArg (fun y => b.repr y i) hx
  rw [hcoord, hcoord, map_zero, Finsupp.zero_apply] at hi
  rcases mul_eq_zero.mp hi with h | h
  · rw [h, zero_mul]
  · exact h

#print axioms apply_eq_zero_of_apply_apply_eq_zero_of_basis

end HodgeBlocks
