import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Realification
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Real coordinates on complex polynomial carriers.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
open Topology
namespace HodgeLean.Foundations.ComplexTopology

def complexRealCoordinates (n : ℕ) : (Fin n → ℂ) ≃ₜ (Fin n ⊕ Fin n → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun w i := Complex.equivRealProdCLM.symm (w (.inl i), w (.inr i))
  left_inv z := by funext i; rfl
  right_inv w := by funext i; cases i <;> rfl
  continuous_toFun := continuous_pi fun i => by
    cases i with
    | inl i => exact Complex.continuous_re.comp (continuous_apply i)
    | inr i => exact Complex.continuous_im.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i =>
    Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_apply (Sum.inl i : Fin n ⊕ Fin n)).prodMk (continuous_apply (Sum.inr i : Fin n ⊕ Fin n)))

def complexEuclideanCoordinates (n : ℕ) :
    (Fin n → ℂ) ≃ₜ EuclideanSpace ℝ (Fin (n + n)) :=
  (complexRealCoordinates n).trans
    ((Homeomorph.piCongrLeft (Y := fun _ => ℝ) finSumFinEquiv).trans
      (EuclideanSpace.equiv (Fin (n + n)) ℝ).symm.toHomeomorph)

lemma real_equations_in_euclidean_coordinates {n m : ℕ}
    (p : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ a b : Fin m → MvPolynomial (Fin (n + n)) ℝ,
      ∀ z : Fin n → ℂ, z ∈ zeroSet p ↔
        (∀ j, MvPolynomial.eval (complexEuclideanCoordinates n z) (a j) = 0) ∧
        (∀ j, MvPolynomial.eval (complexEuclideanCoordinates n z) (b j) = 0) := by
  obtain ⟨a, b, hab⟩ := finite_real_equations p
  refine ⟨fun j => MvPolynomial.rename finSumFinEquiv (a j),
    fun j => MvPolynomial.rename finSumFinEquiv (b j), ?_⟩
  intro z
  simp only [MvPolynomial.eval_rename]
  have he : (fun i => complexEuclideanCoordinates n z (finSumFinEquiv i)) =
      Sum.elim (fun i => (z i).re) (fun i => (z i).im) := by
    funext i
    change (Homeomorph.piCongrLeft (Y := fun _ => ℝ) finSumFinEquiv)
      (complexRealCoordinates n z) (finSumFinEquiv i) = _
    rw [Homeomorph.piCongrLeft_apply_apply]
    rfl
  simpa only [Function.comp_def, he] using hab z

lemma zeroSet_real_model {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ) :
    ∃ a b : Fin m → MvPolynomial (Fin (n + n)) ℝ,
      Nonempty (zeroSet p ≃ₜ
        {y : EuclideanSpace ℝ (Fin (n + n)) |
          (∀ j, MvPolynomial.eval y (a j) = 0) ∧
          (∀ j, MvPolynomial.eval y (b j) = 0)}) := by
  obtain ⟨a, b, hab⟩ := real_equations_in_euclidean_coordinates p
  refine ⟨a, b, ⟨(complexEuclideanCoordinates n).sets ?_⟩⟩
  ext z
  exact hab z

end HodgeLean.Foundations.ComplexTopology
