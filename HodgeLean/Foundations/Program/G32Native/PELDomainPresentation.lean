import HodgeLean.Foundations.Program.G32Native.PELIsometryGroup
import HodgeLean.Foundations.Program.G32Native.PELSplitReference

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- A centralizer can be tested on any rational basis. -/
theorem pel_commutes_basis_iff {V : Type*} [AddCommGroup V] [Module ℚ V]
    {ι : Type*} (b : Module.Basis ι ℚ V) {n : ℕ}
    (f : V →ₗ[ℚ] Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    (∀ i, g * f (b i) = f (b i) * g) ↔ ∀ x, g * f x = f x * g := by
  constructor
  · intro h
    let F := (LinearMap.mulRight ℚ g - LinearMap.mulLeft ℚ g).comp f
    have hF : F = 0 := by
      apply b.ext
      intro i
      exact sub_eq_zero.mpr (h i).symm
    intro x
    exact (sub_eq_zero.mp (LinearMap.congr_fun hF x)).symm
  · intro h i
    exact h (b i)

/-- Changing a basis or presentation of the same operator space preserves
its connected polarization-isometry centralizer. -/
theorem pelGenericGroup_eq_of_operator_range
    {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    {ι κ : Type*} (b : Module.Basis ι ℚ V) (c : Module.Basis κ ℚ W) {n : ℕ}
    (f : V →ₗ[ℚ] Matrix (Fin n) (Fin n) ℂ)
    (h : W →ₗ[ℚ] Matrix (Fin n) (Fin n) ℂ)
    (he : Set.range f = Set.range h) (Ω : Matrix (Fin n) (Fin n) ℂ) :
    pelGenericGroup Ω (Set.range fun i => f (b i)) =
      pelGenericGroup Ω (Set.range fun i => h (c i)) := by
  have hc (g : Matrix (Fin n) (Fin n) ℂ) :
      (∀ i, g * f (b i) = f (b i) * g) ↔ ∀ i, g * h (c i) = h (c i) * g := by
    rw [pel_commutes_basis_iff, pel_commutes_basis_iff]
    constructor
    · intro hf x
      obtain ⟨y, hy⟩ := he.symm ▸ Set.mem_range_self x
      rw [← hy]
      exact hf y
    · intro hh x
      obtain ⟨y, hy⟩ := he ▸ Set.mem_range_self x
      rw [← hy]
      exact hh y
  have hg : ((pelIsometryGroup Ω (Set.range fun i => f (b i))).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) =
      ((pelIsometryGroup Ω (Set.range fun i => h (c i))).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
    ext g
    change ((g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * g = Ω ∧
      ∀ T ∈ Set.range (fun i => f (b i)), (g : Matrix (Fin n) (Fin n) ℂ) * T = T * g) ↔
      ((g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω * g = Ω ∧
      ∀ T ∈ Set.range (fun i => h (c i)), (g : Matrix (Fin n) (Fin n) ℂ) * T = T * g)
    simp only [Set.forall_mem_range]
    exact and_congr_right (fun _ => hc g)
  unfold pelGenericGroup g1_identityComponent
  rw [hg]

/-- The entire rational endomorphism action in reference complex coordinates. -/
def pelEnd0Matrix (R : PELSplitReference) :
    HodgeLean.Adapters.AbelianEnd0 R.B.X →ₗ[ℚ] Matrix (Fin 12) (Fin 12) ℂ where
  toFun d := (LinearMap.toMatrix R.basis R.basis
    (HodgeLean.Adapters.abelianEnd0Action R.B.X d).unop).map (algebraMap ℚ ℂ)
  map_add' := by intro x y; ext i j; simp
  map_smul' := by
    intro r x
    simp only [map_smul, MulOpposite.unop_smul]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def]
    simp only [map_mul, RingHom.id_apply]

/-- The connected centralizer is independent of the exact quaternion presentation. -/
theorem pelGenericGroup_presentation (R : PELSplitReference) (b : ℚ)
    (e : ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] HodgeLean.Adapters.AbelianEnd0 R.B.X) :
    pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) =
    pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 => pelEnd0Matrix R
        (e (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))) := by
  let f := (pelEnd0Matrix R).comp R.end0.toAlgHom.toLinearMap
  let h := (pelEnd0Matrix R).comp e.toAlgHom.toLinearMap
  have he : Set.range f = Set.range h := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨e.symm (R.end0 d), by simp [f, h]⟩
    · rintro ⟨d, rfl⟩
      exact ⟨R.end0.symm (e d), by simp [f, h]⟩
  exact pelGenericGroup_eq_of_operator_range
    (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b)
    (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b) f h he _

#print axioms pelGenericGroup_eq_of_operator_range
#print axioms pelGenericGroup_presentation
end HodgeLean.Foundations.Program.GeneralTypeIII
