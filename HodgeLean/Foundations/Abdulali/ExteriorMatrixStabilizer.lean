import HodgeLean.Foundations.Abdulali.ExteriorMatrixCoefficient
import HodgeLean.Foundations.Program.MilneTensorCopiesRepresentation

noncomputable section
set_option maxHeartbeats 200000
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}

/-- The exterior representation of invertible matrices on repeated standard copies. -/
def exteriorMatrixRepresentation (b : Module.Basis (Fin d) ℂ V) (r n : ℕ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin d) ℂ) (⋀[ℂ]^n (Fin r → V)) where
  toFun g := exteriorPower.map n (m1b_copies r (Matrix.toLin b b ↑g))
  map_one' := by
    change exteriorPower.map n (m1b_copies r (Matrix.toLin b b 1)) = 1
    rw [Matrix.toLin_one]
    have h : m1b_copies (V := V) r LinearMap.id = LinearMap.id := by ext w j; rfl
    rw [h, exteriorPower.map_id]
    rfl
  map_mul' g h := by
    change exteriorPower.map n (m1b_copies r (Matrix.toLin b b
      ((g : Matrix (Fin d) (Fin d) ℂ) * (h : Matrix (Fin d) (Fin d) ℂ)))) =
      (exteriorPower.map n (m1b_copies r (Matrix.toLin b b ↑g))).comp
        (exteriorPower.map n (m1b_copies r (Matrix.toLin b b ↑h)))
    rw [Matrix.toLin_mul b b b]
    have hc (A D : Module.End ℂ V) : m1b_copies r (A.comp D) =
        (m1b_copies r A).comp (m1b_copies r D) := by ext w j; rfl
    rw [hc, exteriorPower.map_comp]

/-- The stabilizer of an exterior vector, presented by its actual polynomial
coordinate equations on invertible matrices. -/
def exteriorMatrixStabilizer (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → V)) : MatrixAlgGroup ℂ d := by
  classical
  let ρ := exteriorMatrixRepresentation b r n
  let H : Subgroup (Matrix.GeneralLinearGroup (Fin d) ℂ) :=
    { carrier := {g | ρ g v = v}
      one_mem' := by
        change ρ 1 v = v
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro g h hg hh
        change ρ (g*h) v = v
        change ρ g v = v at hg
        change ρ h v = v at hh
        rw [map_mul, Module.End.mul_apply, hh, hg]
      inv_mem' := by
        intro g hg
        calc ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := congrArg (ρ g⁻¹) hg.symm
             _ = v := by
               change (ρ g⁻¹ * ρ g) v = v
               rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let c := (m2_piBasis b r).exteriorPower n
  let p := fun i => exteriorMatrixCoefficient b r n v i - MvPolynomial.C (c.repr v i)
  refine g1_ofEquations (Set.range p) H ?_
  intro g
  have hc : g1_coords g = (fun ij : Fin d × Fin d =>
      (g : Matrix (Fin d) (Fin d) ℂ) ij.1 ij.2) := rfl
  constructor
  · intro hg f hf
    obtain ⟨i, rfl⟩ := hf
    change MvPolynomial.eval (g1_coords g)
      (exteriorMatrixCoefficient b r n v i - MvPolynomial.C (c.repr v i)) = 0
    rw [map_sub, MvPolynomial.eval_C, hc, eval_exteriorMatrixCoefficient]
    change c.repr (ρ g v) i - c.repr v i = 0
    rw [hg, sub_self]
  · intro hg
    change ρ g v = v
    apply c.repr.injective
    ext i
    have hi := hg (p i) ⟨i, rfl⟩
    change MvPolynomial.eval (g1_coords g)
      (exteriorMatrixCoefficient b r n v i - MvPolynomial.C (c.repr v i)) = 0 at hi
    rw [map_sub, MvPolynomial.eval_C, hc, eval_exteriorMatrixCoefficient] at hi
    exact sub_eq_zero.mp hi

@[simp] theorem mem_exteriorMatrixStabilizer (b : Module.Basis (Fin d) ℂ V) (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → V)) (g : Matrix.GeneralLinearGroup (Fin d) ℂ) :
    g ∈ (exteriorMatrixStabilizer b r n v).carrier ↔
      exteriorPower.map n (m1b_copies r (Matrix.toLin b b ↑g)) v = v := Iff.rfl

end HodgeLean.Foundations.Abdulali
