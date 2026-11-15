import HodgeLean.Foundations.Abdulali.ExteriorMatrixCoefficient

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Polynomial fixedness on a matrix group implies annihilation by its tangent
space on exterior powers of standard copies. No connectedness is required. -/
theorem exterior_fixed_killed_by_matrix_tangent
    {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℂ V) (G : MatrixAlgGroup ℂ d)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V))
    (hv : ∀ g ∈ G.carrier, exteriorPower.map n
      (m2_diagonalEnd r (Matrix.toLin b b (g : Matrix (Fin d) (Fin d) ℂ))) v = v)
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X ∈ g1_lieAlgebra G) :
    InvariantsExterior.exteriorDer n (m2_diagonalEnd r (Matrix.toLin b b X)) v = 0 := by
  classical
  apply ((m2_piBasis b r).exteriorPower n).repr.injective
  rw [map_zero]
  ext i
  change ((m2_piBasis b r).exteriorPower n).repr
    (InvariantsExterior.exteriorDer n (m2_diagonalEnd r (Matrix.toLin b b X)) v) i = 0
  rw [← differential_exteriorMatrixCoefficient]
  let a := ((m2_piBasis b r).exteriorPower n).repr v i
  have hf : exteriorMatrixCoefficient b r n v i - MvPolynomial.C a ∈
      g1_vanishingIdeal G := by
    apply g1_mem_vanishingIdealSet_iff.mpr
    intro g hg
    rw [map_sub, MvPolynomial.eval_C]
    have hc : g1_coords g = (fun ij : Fin d × Fin d =>
        (g : Matrix (Fin d) (Fin d) ℂ) ij.1 ij.2) := rfl
    rw [hc, eval_exteriorMatrixCoefficient b r n v i (g : Matrix (Fin d) (Fin d) ℂ), hv g hg]
    exact sub_self _
  have hz := (g1_mem_lieOfSet_iff.mp hX) _ hf
  change g1_diffAt X (exteriorMatrixCoefficient b r n v i - MvPolynomial.C a) = 0 at hz
  simpa only [map_sub, g1_diffAt_apply, g1_differential_C, sub_zero] using hz

end HodgeLean.Foundations.Abdulali
