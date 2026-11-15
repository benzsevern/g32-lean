import HodgeLean.Foundations.Abdulali.SpecialOrthogonalConnected
import HodgeLean.Foundations.Abdulali.ExteriorConnectedComparison
import HodgeLean.Foundations.Program.MilneTensorSymmetricStandardCoordinates

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Orthonormal coordinates for a nondegenerate complex symmetric bilinear form. -/
theorem symmetric_bilinear_orthonormal_basis
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (hs : B.IsSymm) :
    ∃ b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V,
      LinearMap.toMatrix₂ b b B = 1 := by
  obtain ⟨e, he⟩ := m1b_symmetric_standard_coordinates B hB hs.eq
  let b := (Pi.basisFun ℂ (Fin (Module.finrank ℂ V))).map e.symm
  refine ⟨b, ?_⟩
  ext i j
  have h := congrArg (fun F : LinearMap.BilinForm ℂ (Fin (Module.finrank ℂ V) → ℂ) =>
    F (Pi.single i 1) (Pi.single j 1)) he
  simpa [b, Module.Basis.map_apply, LinearMap.toMatrix₂_apply, LinearMap.compl₁₂_apply,
    Pi.basisFun_apply, Matrix.toBilin'_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using h

/-- A vector annihilated by every intrinsic skew operator is fixed by every
actual determinant-one isometry on its exterior power of standard copies. -/
theorem special_orthogonal_exterior_fixed_of_killed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (r n : ℕ) (v : ⋀[ℂ]^n (Fin r → V))
    (hv : ∀ X : Module.End ℂ V, (∀ x y, B (X x) y + B x (X y) = 0) →
      InvariantsExterior.exteriorDer n (m1b_copies r X) v = 0)
    (u : Module.End ℂ V) (hu : u ∈ m1b_isometries B) (hdet : LinearMap.det u = 1) :
    exteriorPower.map n (m1b_copies r u) v = v := by
  obtain ⟨b, hb⟩ := symmetric_bilinear_orthonormal_basis B hB hs
  let d := Module.finrank ℂ V
  let G := specialOrthogonalMatrixGroup (1 : Matrix (Fin d) (Fin d) ℂ)
  have hkill : ∀ X ∈ g1_lieAlgebra G,
      InvariantsExterior.exteriorDer n (m1b_copies r (Matrix.toLin b b X)) v = 0 := by
    intro X hX
    have hm := ((lie_specialOrthogonalMatrixGroup 1 X).mp hX).1
    let T := Matrix.toLin b b X
    have hF : B.compl₁₂ T LinearMap.id + B.compl₁₂ LinearMap.id T = 0 := by
      apply (LinearMap.toMatrix₂ b b).injective
      simp only [map_add, map_zero, LinearMap.toMatrix₂_compl₁₂ b b b b,
        LinearMap.toMatrix_id, Matrix.transpose_one, mul_one, one_mul]
      rw [hb, show LinearMap.toMatrix b b T = X from LinearMap.toMatrix_toLin b b X]
      simpa only [mul_one, one_mul] using hm
    apply hv T
    intro x y
    exact congrArg (fun F : LinearMap.BilinForm ℂ V => F x y) hF
  let g : Matrix.GeneralLinearGroup (Fin d) ℂ :=
    Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom hu.1.unit
  have hgu : (g : Matrix (Fin d) (Fin d) ℂ) = LinearMap.toMatrix b b u := by
    change LinearMap.toMatrix b b (↑hu.1.unit) = LinearMap.toMatrix b b u
    rw [hu.1.unit_spec]
  have hg : g ∈ G.carrier := by
    rw [mem_specialOrthogonalMatrixGroup, hgu]
    constructor
    · have he : B.compl₁₂ u u = B := by ext x y; exact hu.2 x y
      have hm := congrArg (LinearMap.toMatrix₂ b b) he
      simpa only [LinearMap.toMatrix₂_compl₁₂ b b b b, hb] using hm
    · rw [LinearMap.det_toMatrix]
      exact hdet
  have hf := exterior_fixed_of_connected_tangent_killed b G
    (specialOrthogonal_standard_isConnected d) r n v hkill g hg
  rw [hgu, Matrix.toLin_toMatrix] at hf
  exact hf

end HodgeLean.Foundations.Abdulali
