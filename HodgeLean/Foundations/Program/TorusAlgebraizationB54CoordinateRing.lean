import HodgeLean.Foundations.Program.TorusAlgebraizationB54ThetaIncidence
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Evaluation
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Presentation

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ) {ι : Type}

def b54_basisGenerator (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (i : ι) : b5_S Λ F hF Q :=
  DirectSum.of (fun n => b5_sections Λ F hF Q (3 * n)) 1 (b i)

theorem b54_eval_basis_polynomial
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (p : MvPolynomial ι ℂ) (z : b5_V Λ F) :
    b5_eval Λ F hF Q z (MvPolynomial.aeval (b54_basisGenerator Λ F hF Q b) p) =
      MvPolynomial.eval (b54_sectionCoordinates Λ F hF Q b z) p := by
  have hh : (b5_eval Λ F hF Q z).comp
      (MvPolynomial.aeval (b54_basisGenerator Λ F hF Q b)).toRingHom =
        MvPolynomial.eval (b54_sectionCoordinates Λ F hF Q b z) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa using b54_eval_scalar Λ F hF Q z c
    · intro i
      simp [b54_basisGenerator, b5_eval, b54_sectionCoordinates]
  exact RingHom.congr_fun hh p

theorem b54_basis_polynomial_eq_zero
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (p : MvPolynomial ι ℂ) (d : ℕ) (hp : p.IsHomogeneous d)
    (hz : ∀ z, MvPolynomial.eval (b54_sectionCoordinates Λ F hF Q b z) p = 0) :
    MvPolynomial.aeval (b54_basisGenerator Λ F hF Q b) p = 0 := by
  apply b54_homogeneous_eq_zero_of_eval Λ F hF Q d
  · exact b54_aeval_mem_grade (b5_grade Λ F hF Q)
      (b54_basisGenerator Λ F hF Q b) (fun i => ⟨b i, rfl⟩) hp
  · intro z
    rw [b54_eval_basis_polynomial]
    exact hz z

theorem b54_theta_cone_relations (n : ℕ)
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      (∀ i, MvPolynomial.aeval (b54_basisGenerator Λ F hF Q b) (P i) = 0) ∧
      Prod.snd '' b54_thetaIncidence Λ F hF Q b =
        {v | ∀ i, MvPolynomial.eval v (P i) = 0} := by
  obtain ⟨m, d, P, hP, heq⟩ := b54_theta_cone_algebraic Λ F hF Q n b
  refine ⟨m, d, P, hP, ?_, heq⟩
  intro i
  apply b54_basis_polynomial_eq_zero Λ F hF Q b (P i) (d i) (hP i)
  intro z
  have hz : b54_sectionCoordinates Λ F hF Q b z ∈
      Prod.snd '' b54_thetaIncidence Λ F hF Q b := by
    refine ⟨(b2_torusCover Λ F z, b54_sectionCoordinates Λ F hF Q b z), ?_, rfl⟩
    refine ⟨(z, b54_sectionCoordinates Λ F hF Q b z), ?_, rfl⟩
    intro j k
    change _ * _ - _ * _ = (0 : ℂ)
    ring
  rw [heq] at hz
  exact hz i

theorem b54_algHom_coordinates_mem_cone (n : ℕ)
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3))
    (q : b5_S Λ F hF Q →ₐ[ℂ] ℂ) :
    (fun i => q (b54_basisGenerator Λ F hF Q b i)) ∈
      Prod.snd '' b54_thetaIncidence Λ F hF Q b := by
  obtain ⟨m, d, P, _, hrel, heq⟩ := b54_theta_cone_relations Λ F hF Q n b
  rw [heq]
  intro i
  have hh := congrArg q (hrel i)
  rw [MvPolynomial.comp_aeval_apply] at hh
  simpa [MvPolynomial.aeval_def] using hh

theorem b54_basis_generates [Fintype ι]
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (hgen : Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤) :
    Algebra.adjoin ℂ (Set.range (b54_basisGenerator Λ F hF Q b)) = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  rintro _ ⟨s, rfl⟩
  rw [← b.sum_repr s, map_sum]
  apply sum_mem
  intro i _
  rw [map_smul]
  apply Subalgebra.smul_mem
  exact Algebra.subset_adjoin (Set.mem_range_self i)

theorem b54_basis_generates_over_gradeZero [Fintype ι]
    (b : Module.Basis ι ℂ (b5_sections Λ F hF Q 3))
    (hgen : Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤) :
    Algebra.adjoin (b5_grade Λ F hF Q 0) (Set.range (b54_basisGenerator Λ F hF Q b)) = ⊤ := by
  apply top_unique
  intro x hxTop
  clear hxTop
  have hx : x ∈ Algebra.adjoin ℂ (Set.range (b54_basisGenerator Λ F hF Q b)) := by
    rw [b54_basis_generates Λ F hF Q b hgen]
    trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap c =>
    exact (Algebra.adjoin (b5_grade Λ F hF Q 0)
      (Set.range (b54_basisGenerator Λ F hF Q b))).algebraMap_mem
        (algebraMap ℂ (b5_grade Λ F hF Q 0) c)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

end HodgeLean.Foundations.Program
