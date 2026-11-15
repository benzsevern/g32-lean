import HodgeLean.Foundations.Program.TorusAlgebraizationB54CoordinateRing
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Normalize
import HodgeLean.Foundations.Program.TorusAlgebraizationB54PointCharts

noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem b54_proj_point_is_thetaEvaluation (n : ℕ)
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3))
    (hbase : ∀ z, ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0)
    (hgen : Algebra.adjoin ℂ (b5_grade Λ F hF Q 1 : Set (b5_S Λ F hF Q)) = ⊤)
    (hscalar : Function.Surjective (algebraMap ℂ (b5_grade Λ F hF Q 0)))
    (htop : ∀ z, (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    (p : ComplexPoint (b5_model Λ F hF Q)) :
    ∃ z, p.left = Proj.fromOfGlobalSections (b5_grade Λ F hF Q)
      (b5_evalGlobal Λ F hF Q z) (htop z) := by
  let G := b5_grade Λ F hF Q
  let v := b54_basisGenerator Λ F hF Q b
  have hv (i : Fin n) : v i ∈ G 1 := ⟨b i, rfl⟩
  have hg : Algebra.adjoin (G 0) (Set.range v) = ⊤ :=
    b54_basis_generates_over_gradeZero Λ F hF Q b hgen
  obtain ⟨i, φ, hφ⟩ := b54_complexPoint_in_chart G v hv
    (b54_irrelevant_le_span_generators G v hv hg) p.left
  have hφscalar (a : ℂ) : φ (fromZeroRingHom G (.powers (v i))
      (algebraMap ℂ (G 0) a)) = a :=
    b54_chartPoint_scalar G (algebraMap ℂ (G 0)) p (hv i) φ hφ a
  let q : b5_S Λ F hF Q →ₐ[ℂ] ℂ :=
    { φ.comp (b54_awayNormalize G (hv i)) with
      commutes' := by
        intro a
        change φ (b54_awayNormalize G (hv i)
          (algebraMap (G 0) (b5_S Λ F hF Q) (algebraMap ℂ (G 0) a))) = a
        rw [b54_awayNormalize_fromZero]
        exact hφscalar a }
  have hqi : q (v i) = 1 := by
    change φ (b54_awayNormalize G (hv i) (v i)) = 1
    rw [b54_awayNormalize_self, map_one]
  obtain ⟨z, c, hc⟩ := (b54_theta_cone_mem_iff Λ F hF Q b hbase _).mp
    (b54_algHom_coordinates_mem_cone Λ F hF Q n b q)
  have hci : 1 = c * (b i).val z := by
    have hh := congrFun hc i
    change q (v i) = c * (b i).val z at hh
    rwa [hqi] at hh
  have hsi : (b i).val z ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hci
    exact one_ne_zero hci
  have heval (j : Fin n) : b5_eval Λ F hF Q z (v j) = (b j).val z := by
    simp [v, b54_basisGenerator, b5_eval]
  have hu : IsUnit (b5_eval Λ F hF Q z (v i)) := Ne.isUnit (by rwa [heval])
  have heq : φ = b54_awayEvaluation (G := G) (b5_eval Λ F hF Q z) (v i) hu := by
    apply b54_away_ringHom_ext G (hv i) v hv hg
    · intro a
      obtain ⟨a, rfl⟩ := hscalar a
      rw [HomogeneousLocalization.algebraMap_eq, hφscalar, b54_awayEvaluation_fromZero]
      exact (b54_eval_scalar Λ F hF Q z a).symm
    · intro j
      rw [b54_awayEvaluation_mk, heval, heval]
      have hj : φ (Away.mk G (hv i) 1 (v j) (by simpa using hv j)) = c * (b j).val z := by
        have hh := congrFun hc j
        change φ (b54_awayNormalize G (hv i) (v j)) = c * (b j).val z at hh
        rwa [b54_awayNormalize_homogeneous G (hv i) 1 (v j) (hv j)] at hh
      rw [hj, pow_one]
      have hc' : c = ((b i).val z)⁻¹ := by
        apply mul_right_cancel₀ hsi
        rw [inv_mul_cancel₀ hsi]
        exact hci.symm
      rw [hc', mul_comm]
  refine ⟨z, hφ.symm.trans ?_⟩
  rw [heq]
  exact (b54_fromOfGlobalSections_eq_awayEvaluation (b5_eval Λ F hF Q z) (hv i)
    zero_lt_one hu (htop z)).symm

end HodgeLean.Foundations.Program
