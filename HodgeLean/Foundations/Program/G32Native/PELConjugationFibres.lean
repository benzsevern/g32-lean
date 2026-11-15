import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent
import HodgeLean.Foundations.MatrixAlgGroupLieElem
import HodgeLean.Foundations.Program.G32Native.PELNormalIntersection

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations.Program.GeneralTypeIII
open MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

/-- The equation intertwining two fixed invertible matrices is polynomial
in the variable matrix. -/
theorem pel_isClosed_intertwiner (x y : Matrix.GeneralLinearGroup (Fin n) k) :
    @IsClosed _ (g1_zariski k n) {g : Matrix.GeneralLinearGroup (Fin n) k |
      x * g = g * y} := by
  let p : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
    (x : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n -
      g1_varMatrix k n * (y : Matrix (Fin n) (Fin n) k).map C
  have heval (g : Matrix.GeneralLinearGroup (Fin n) k) :
      (eval (g1_coords g)).mapMatrix p =
        (x : Matrix (Fin n) (Fin n) k) * g - g * y := by
    simp only [p, map_sub, map_mul, g1_mapMatrix_eval_varMatrix]
    congr 2 <;> ext i j <;> simp only [RingHom.mapMatrix_apply, Matrix.map_apply, eval_C]
  apply (g1_isClosed_iff _).mpr
  refine ⟨Set.range (fun ij : Fin n × Fin n => p ij.1 ij.2), ?_⟩
  ext g
  change x * g = g * y ↔ ∀ f ∈ Set.range (fun ij : Fin n × Fin n => p ij.1 ij.2),
    eval (g1_coords g) f = 0
  constructor
  · intro h f hf
    obtain ⟨ij, rfl⟩ := hf
    have hm : (eval (g1_coords g)).mapMatrix p = 0 := by
      rw [heval, ← Units.val_mul, ← Units.val_mul, h, sub_self]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) k => M ij.1 ij.2) hm
  · intro h
    apply Units.ext
    apply sub_eq_zero.mp
    rw [Units.val_mul, Units.val_mul]
    rw [← heval]
    ext i j
    exact h (p i j) ⟨(i, j), rfl⟩

/-- Fibres of conjugation are Zariski closed, without invoking a topology
on a product of algebraic groups. -/
theorem pel_isClosed_conjugation_fibre (x y : Matrix.GeneralLinearGroup (Fin n) k) :
    @IsClosed _ (g1_zariski k n) {g : Matrix.GeneralLinearGroup (Fin n) k |
      g⁻¹ * x * g = y} := by
  convert pel_isClosed_intertwiner x y using 1
  ext g
  change g⁻¹ * x * g = y ↔ x * g = g * y
  constructor
  · intro h
    have hh := congrArg (fun z => g * z) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  · intro h
    have hh := congrArg (fun z => g⁻¹ * z) h
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hh

#print axioms pel_isClosed_intertwiner
#print axioms pel_isClosed_conjugation_fibre
end HodgeLean.Foundations.Program.GeneralTypeIII
