import HodgeLean.Foundations.Program.CodifferentialComparisonChartProofs
import HodgeLean.Foundations.Program.CodifferentialComparisonDefs


noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


theorem b66f_multiplication_transport_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q r : Fin 3 → b66f_primitiveForms D t)
    (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z) :
    b66f_multiplicationMatrix D t (b66f_reframe D t q P) (b66f_reframe D t r R) S v =
      b66e_productChange P R * b66f_multiplicationMatrix D t q r S v := by
  have hmul : ∀ i j, b66f_multiply D t (b66f_reframe D t q P i) (b66f_reframe D t r R j) =
      ∑ ab : Fin 3 × Fin 3, (P ab.1 i * R ab.2 j) • b66f_multiply D t (q ab.1) (r ab.2) := by
    intro i j
    have hprod : b66f_product D (b66f_reframe D t q P i).val (b66f_reframe D t r R j).val =
        ∑ ab : Fin 3 × Fin 3, (P ab.1 i * R ab.2 j) •
          b66f_product D (q ab.1).val (r ab.2).val := by
      funext a x
      simp only [b66f_reframe, b66f_product, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [b66f_multiply, hprod, map_sum, map_smul]
  ext u j
  rw [Matrix.mul_apply]
  simp only [b66f_multiplicationMatrix, hmul]
  have h := b66f_gen_b66e_residueSum_sum D t (S j) (v j) (hmero j) Finset.univ
    (fun ab : Fin 3 × Fin 3 => P ab.1 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u).1 *
      R ab.2 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u).2)
    (fun ab => b66f_multiply D t (q ab.1) (r ab.2))
    (fun ab => (b66f_gen_b66g_average_product D t (q ab.1).property.1 (r ab.2).property.1).1)
  rw [h]
  rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp]
  refine Fintype.sum_congr _ _ fun ab => ?_
  simp only [b66e_productChange, Equiv.symm_apply_apply]

end HodgeLean.Foundations.Program
