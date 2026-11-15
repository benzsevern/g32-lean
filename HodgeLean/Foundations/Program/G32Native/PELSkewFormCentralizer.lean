import HodgeLean.Foundations.Program.G32Native.PELSkewMatrixCentralizer
import Mathlib.LinearAlgebra.Matrix.BilinearForm

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- In orthonormal coordinates of dimension at least three, the commutant
of all skew endomorphisms consists of scalar endomorphisms. -/
theorem pel_skew_form_centralizer_scalar
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (B : LinearMap.BilinForm ℂ V)
    (hb : LinearMap.toMatrix₂ b b B = 1)
    (third : ∀ i j : ι, ∃ l, l ≠ i ∧ l ≠ j)
    (T : Module.End ℂ V)
    (hT : ∀ Y : Module.End ℂ V,
      (∀ x y, B (Y x) y + B x (Y y) = 0) → T * Y = Y * T)
    (o : ι) : ∃ c : ℂ, T = c • LinearMap.id := by
  let M := LinearMap.toMatrix b b T
  have hM (i j : ι) : M * (Matrix.single i j 1 - Matrix.single j i 1) =
      (Matrix.single i j 1 - Matrix.single j i 1) * M := by
    let K : Matrix ι ι ℂ := Matrix.single i j 1 - Matrix.single j i 1
    let Y := Matrix.toLin b b K
    have hK : K.transpose + K = 0 := by
      simp only [K, Matrix.transpose_sub, Matrix.transpose_single]
      abel
    have hY : ∀ x y, B (Y x) y + B x (Y y) = 0 := by
      have hz : B.compl₁₂ Y LinearMap.id + B.compl₁₂ LinearMap.id Y = 0 := by
        apply (LinearMap.toMatrix₂ b b).injective
        simpa only [map_add, LinearMap.toMatrix₂_compl₁₂ b b b b, hb,
          LinearMap.toMatrix_id, Y, LinearMap.toMatrix_toLin, Matrix.transpose_one,
          mul_one, one_mul, map_zero] using hK
      intro x y
      exact LinearMap.congr_fun₂ hz x y
    have h := congrArg (LinearMap.toMatrix b b) (hT Y hY)
    simpa only [LinearMap.toMatrix_mul, Y, LinearMap.toMatrix_toLin] using h
  have he := pel_skew_matrix_centralizer_scalar third M hM o
  refine ⟨M o o, ?_⟩
  apply (LinearMap.toMatrix b b).injective
  simpa only [map_smul, LinearMap.toMatrix_id] using he

/-- A skew endomorphism centralizing every skew endomorphism vanishes in
orthonormal dimension at least three. -/
theorem pel_skew_form_center_eq_zero
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) (B : LinearMap.BilinForm ℂ V)
    (hb : LinearMap.toMatrix₂ b b B = 1)
    (third : ∀ i j : ι, ∃ l, l ≠ i ∧ l ≠ j)
    (T : Module.End ℂ V)
    (hskew : ∀ x y, B (T x) y + B x (T y) = 0)
    (hT : ∀ Y : Module.End ℂ V,
      (∀ x y, B (Y x) y + B x (Y y) = 0) → T * Y = Y * T)
    (o : ι) : T = 0 := by
  obtain ⟨c, hc⟩ := pel_skew_form_centralizer_scalar b B hb third T hT o
  have hbo : B (b o) (b o) = 1 := by
    have h := congrArg (fun M : Matrix ι ι ℂ => M o o) hb
    simpa only [LinearMap.toMatrix₂_apply, Matrix.one_apply_eq] using h
  have h := hskew (b o) (b o)
  rw [hc] at h
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
    LinearMap.smul_apply, hbo, smul_eq_mul, mul_one] at h
  have hz : c = 0 := by linear_combination (1 / 2 : ℂ) * h
  rw [hc, hz, zero_smul]

#print axioms pel_skew_form_center_eq_zero
#print axioms pel_skew_form_centralizer_scalar
end HodgeLean.Foundations.Program.GeneralTypeIII
