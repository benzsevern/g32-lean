import HodgeLean.Foundations.Abdulali.OrthogonalDeterminant
import HodgeLean.Foundations.Abdulali.OrthogonalCharacter
import HodgeLean.Foundations.Program.MilneTensorDefs

noncomputable section
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations.Program

/-- The reflection in the first coordinate of a positive-dimensional standard
orthogonal space.
Source: Weyl, The Classical Groups, Chapter II, §9. -/
def standardReflection (d : ℕ) (hd : 0 < d) : Module.End ℂ (Fin d → ℂ) :=
  LinearMap.pi (fun i => (if i = ⟨0, hd⟩ then (-1 : ℂ) else 1) • LinearMap.proj i)

example (d : ℕ) (hd : 0 < d) (v : Fin d → ℂ) :
    standardReflection d hd v ⟨0, hd⟩ = -v ⟨0, hd⟩ := by
  simp [standardReflection]

/-- This explicit reflection is an orthogonal involution of determinant
minus one, retaining the component outside SO.
Source: Weyl, The Classical Groups, Chapter II, §9. -/
theorem standardReflection_properties (d : ℕ) (hd : 0 < d) :
    standardReflection d hd * standardReflection d hd = 1 ∧
    standardReflection d hd ∈ m1b_isometries (1 : Matrix (Fin d) (Fin d) ℂ).toBilin' ∧
    (standardReflection d hd).det = -1 := by
  classical
  let c : Fin d → ℂ := fun i => if i = ⟨0, hd⟩ then -1 else 1
  have hc (i : Fin d) : c i * c i = 1 := by
    dsimp only [c]
    split_ifs <;> norm_num
  have hsq : standardReflection d hd * standardReflection d hd = 1 := by
    apply LinearMap.ext
    intro v
    ext i
    change c i * (c i * v i) = v i
    rw [← mul_assoc, hc, one_mul]
  refine ⟨hsq, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨⟨standardReflection d hd, standardReflection d hd, hsq, hsq⟩, rfl⟩
  · intro x y
    simp only [Matrix.toBilin'_apply', Matrix.one_mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    change (c i * x i) * (c i * y i) = x i * y i
    calc _ = (c i * c i) * (x i * y i) := by ring
         _ = _ := by rw [hc, one_mul]
  · have hm : LinearMap.toMatrix' (standardReflection d hd) = Matrix.diagonal c := by
      ext i j
      change c i * ((Pi.single j (1 : ℂ) : Fin d → ℂ) i) = if i = j then c i else 0
      by_cases hij : i = j
      · subst j; simp
      · simp [Pi.single_apply, hij, Ne.symm hij]
    rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (⟨0, hd⟩ : Fin d)]
    · simp [c]
    · intro i _ hi
      simp [c, hi]
    · simp

end HodgeLean.Foundations.Abdulali
