import HodgeLean.Foundations.Program.TorusAlgebraizationB52ThetaAction
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

theorem b52_thetaTranslate_linearIndependent {ι : Type*} (k : ℕ)
    (d : b5_V Λ F) (e : ι → b5_V Λ F) (f : b5_V Λ F → ℂ) (hf : f ≠ 0)
    (a : ℂ) (heig : b52_thetaTranslate Λ F hF Q k d f = a • f)
    (hchar : Function.Injective (fun i ↦ Complex.exp ((k : ℂ) * Real.pi *
      (b5_H Λ F hF Q d (e i) - b5_H Λ F hF Q (e i) d)))) :
    LinearIndependent ℂ (fun i ↦ b52_thetaTranslate Λ F hF Q k (e i) f) := by
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, zero_smul] at heig
    apply hf
    apply b52_thetaTranslate_injective Λ F hF Q k d
    simpa using heig
  let χ : ι → ℂ := fun i ↦ Complex.exp ((k : ℂ) * Real.pi *
    (b5_H Λ F hF Q d (e i) - b5_H Λ F hF Q (e i) d))
  apply Module.End.eigenvectors_linearIndependent' (b52_thetaTranslate Λ F hF Q k d)
    (fun i ↦ χ i * a) (fun i j h ↦ hchar (mul_right_cancel₀ ha h))
  intro i
  constructor
  · apply Module.End.mem_eigenspace_iff.mpr
    have h := LinearMap.congr_fun (b52_thetaTranslate_commutator Λ F hF Q k d (e i)) f
    change b52_thetaTranslate Λ F hF Q k d (b52_thetaTranslate Λ F hF Q k (e i) f) =
      χ i • b52_thetaTranslate Λ F hF Q k (e i) (b52_thetaTranslate Λ F hF Q k d f) at h
    rw [heig, map_smul, smul_smul] at h
    exact h
  · intro h
    apply hf
    apply b52_thetaTranslate_injective Λ F hF Q k (e i)
    simpa using h

theorem b52_exists_theta_eigen_section
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (k : ℕ) [Module.Finite ℂ (b5_sections Λ F hF Q k)] (d : b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (k : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (s₀ : b5_sections Λ F hF Q k) (hs₀ : s₀ ≠ 0) :
    ∃ a : ℂ, ∃ s : b5_sections Λ F hF Q k, a ≠ 0 ∧ s.val ≠ 0 ∧
      b52_thetaTranslate Λ F hF Q k d s.val = a • s.val := by
  letI : Nontrivial (b5_sections Λ F hF Q k) := ⟨⟨s₀, 0, hs₀⟩⟩
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue
    (b52_sectionTranslation Λ F hF Q hherm k d hd)
  obtain ⟨s, hs⟩ := ha.exists_hasEigenvector
  have he := congrArg (fun t : b5_sections Λ F hF Q k ↦ t.val) hs.apply_eq_smul
  change b52_thetaTranslate Λ F hF Q k d s.val = a • s.val at he
  have hval : s.val ≠ 0 := by
    intro h
    exact hs.2 (Subtype.ext h)
  refine ⟨a, s, ?_, hval, he⟩
  intro ha
  rw [ha, zero_smul] at he
  apply hval
  apply b52_thetaTranslate_injective Λ F hF Q k d
  simpa using he

theorem b52_theta_commutator_card_le_finrank {ι : Type*} [Fintype ι]
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (k : ℕ) [Module.Finite ℂ (b5_sections Λ F hF Q k)]
    (d : b5_V Λ F) (e : ι → b5_V Λ F)
    (hd : ∀ l : Λ, ∃ n : ℤ, (k : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) d).im = n)
    (he : ∀ i l, ∃ n : ℤ, (k : ℝ) * (b5_H Λ F hF Q (b5_lattice Λ F l) (e i)).im = n)
    (hchar : Function.Injective (fun i ↦ Complex.exp ((k : ℂ) * Real.pi *
      (b5_H Λ F hF Q d (e i) - b5_H Λ F hF Q (e i) d))))
    (s₀ : b5_sections Λ F hF Q k) (hs₀ : s₀ ≠ 0) :
    Fintype.card ι ≤ Module.finrank ℂ (b5_sections Λ F hF Q k) := by
  obtain ⟨a, s, _, hs, ha⟩ := b52_exists_theta_eigen_section Λ F hF Q hherm k d hd s₀ hs₀
  have hi := b52_thetaTranslate_linearIndependent Λ F hF Q k d e s.val hs a ha hchar
  have hlin : LinearIndependent ℂ (fun i ↦
      b52_sectionTranslation Λ F hF Q hherm k (e i) (he i) s) :=
    LinearIndependent.of_comp (b5_sections Λ F hF Q k).subtype hi
  exact hlin.fintype_card_le_finrank

end HodgeLean.Foundations.Program
