import HodgeLean.Adapters.IntersectionProductMovingRobertsFinite

/-! # A specified projective coordinate avoiding a finite support -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A prescribed row of a general projection does not vanish at a relevant
homogeneous prime. This permits one fixed affine target chart at finite supports.
Source: HodgeLean, `a3r_generic_of_ne_zero`; Hartshorne, Algebraic Geometry,
II.2, homogeneous coordinates and projective standard opens. -/
theorem s2e_u1_generic_projection_coordinate_notMem
    {ρ σ : Type} [Fintype ρ] [Fintype σ] [DecidableEq ρ] [DecidableEq σ]
    (i : ρ) (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime]
    (hrel : ∃ j, X j ∉ P) :
    a3r_Generic {a : ρ × σ → ℂ | a3r_lin (a3r_mat a) (X i) ∉ P} := by
  classical
  let K := P.ResidueField
  let r := algebraMap (MvPolynomial σ ℂ) K
  let G : MvPolynomial (ρ × σ) K := ∑ j : σ, C (r (X j)) * X (i, j)
  obtain ⟨j, hj⟩ := hrel
  have hj' : r (X j) ≠ 0 := by
    intro h
    exact hj (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hG : G ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun u : ρ × σ =>
      if u = (i, j) then (1 : K) else 0)) h
    have he' : r (X j) = 0 := by
      simpa [G, Prod.mk.injEq] using he
    exact hj' he'
  refine (a3r_generic_of_ne_zero G hG).mono ?_
  intro a ha hmem
  have he : MvPolynomial.eval (fun u => algebraMap ℂ K (a u)) G =
      r (a3r_lin (a3r_mat a) (X i)) := by
    simp only [G, map_sum, map_mul, eval_C, eval_X, a3r_lin_X, a3r_mat,
      Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro j _
    change r (X j) * algebraMap ℂ K (a (i, j)) = r (C (a (i, j))) * r (X j)
    rw [show r (C (a (i, j))) = algebraMap ℂ K (a (i, j)) from
      (IsScalarTower.algebraMap_apply ℂ (MvPolynomial σ ℂ) K _).symm]
    exact mul_comm _ _
  change MvPolynomial.eval (fun u => algebraMap ℂ K (a u)) G ≠ 0 at ha
  rw [he] at ha
  exact ha (Ideal.algebraMap_residueField_eq_zero.mpr hmem)

end HodgeLean.Foundations.Program
