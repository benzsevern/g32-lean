import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPrismPointWeights
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Barycentric support on a face of an independent vertex family. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_face_weight_support {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (v : ι → E) (hv : AffineIndependent ℝ v) (I : Finset ι)
    (w : ι → ℝ) (hw : ∑ i, w i = 1)
    (hx : (∑ i, w i • v i) ∈ convexHull ℝ (v '' (↑I : Set ι))) :
    ∀ i, i ∉ I → w i = 0 := by
  classical
  rw [← Finset.coe_image] at hx
  obtain ⟨c, hc, hc1, hcx⟩ := Finset.mem_convexHull'.mp hx
  rw [Finset.sum_image (fun i _ j _ hij => hv.injective hij)] at hc1 hcx
  let a : ι → ℝ := fun i => if i ∈ I then c (v i) else 0
  have ha1 : (∑ i, a i) = 1 := by
    simpa only [a, Finset.sum_ite_mem, Finset.univ_inter] using hc1
  have hax : (∑ i, a i • v i) = ∑ i, w i • v i := by
    simpa only [a, ite_smul, zero_smul, Finset.sum_ite_mem,
      Finset.univ_inter] using hcx
  intro i hi
  have he := hv.eq_of_sum_eq_sum (hw.trans ha1.symm) hax.symm i (Finset.mem_univ i)
  simpa only [a, hi, ite_false] using he

end HodgeLean.Foundations.Program
