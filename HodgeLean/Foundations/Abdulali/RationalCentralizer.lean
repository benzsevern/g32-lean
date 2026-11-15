import HodgeLean.Foundations.Abdulali.QuaternionCentralizer
import HodgeLean.Foundations.Abdulali.ComplexCentralizerComparison

noncomputable section
open scoped TensorProduct Quaternion
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations

private theorem form_nondegenerate_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) :
    (E.baseChange ℂ).Nondegenerate := by
  let b := Module.finBasis ℚ V
  have hm : LinearMap.BilinForm.toMatrix (b.baseChange ℂ) (E.baseChange ℂ) =
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply]
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℂ)).mpr
  rw [hm]
  change ((algebraMap ℚ ℂ).mapMatrix (LinearMap.BilinForm.toMatrix b E)).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ ℂ)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hE)

private theorem form_alternating_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hAlt : E.IsAlt) : ∀ z, E.baseChange ℂ z z = 0 := by
  have hskew (z w : ℂ ⊗[ℚ] V) : E.baseChange ℂ z w = -E.baseChange ℂ w z := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', neg_add]
    | tmul c x =>
      induction w using TensorProduct.inductionOn with
      | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw', neg_add]
      | tmul d y =>
        simp only [LinearMap.BilinForm.baseChange_tmul]
        rw [← hAlt.neg_eq x y]
        simp only [neg_smul, neg_neg]
        rw [mul_comm]
  intro z
  have h2 : (2 : ℂ) * E.baseChange ℂ z z = 0 := by linear_combination hskew z z
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- A twelve-dimensional rational quaternion representation with retained
Rosati equation has a six-dimensional orthogonal multiplicity normal form.
The rational skew-centralizer is complexified, rather than replaced by a
new complex centralizer assumption. The quadratic generator is retained.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2 and §4, p. 923. -/
theorem rational_quaternion_skew_centralizer
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (hdim : Module.finrank ℚ V = 12) (b : ℚ) (hb : b ≠ 0)
    (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V)
    (E : LinearMap.BilinForm ℚ V) (hAlt : E.IsAlt) (hnd : E.Nondegenerate)
    (hadj : ∀ q z w, E (ρ q z) w = E z (ρ (star q) w)) :
    ∃ (s : ℂ) (a : ℍ[ℂ, -3, 0, (b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V))
      (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)),
      s ^ 2 = -3 ∧ (∀ q, a (star q) = (a q).adjugate) ∧
      a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s] ∧ B.IsSymm ∧ B.Nondegenerate ∧
      (∀ q z, quaternionComplexAction b ρ q (e z) =
        e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z)) ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin 6 → ℂ),
        E.baseChange ℂ (e (x ⊗ₜ[ℂ] u)) (e (y ⊗ₜ[ℂ] v)) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ (ℂ ⊗[ℚ] V),
        X ∈ complexSpan (skewCentralizerOfFamily E
          (fun i => ρ (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))) ↔
        ∃! T : Module.End ℂ (Fin 6 → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  obtain ⟨s, a, n, e, B, hs, ha, hI, hsym, hB, he, hform, hcentral⟩ :=
    complex_quaternion_skew_centralizer (b : ℂ) hbC (ℂ ⊗[ℚ] V)
      (quaternionComplexAction b ρ) (E.baseChange ℂ) (form_alternating_baseChange E hAlt)
      (form_nondegenerate_baseChange E hnd) (quaternionComplexAction_rosati b ρ E hadj)
  have hn : n = 6 := by
    have h := e.finrank_eq
    simp only [Module.finrank_tensorProduct, Module.finrank_pi, Module.finrank_self,
      Fintype.card_fin, Module.finrank_baseChange, hdim, mul_one] at h
    omega
  subst n
  refine ⟨s, a, e, B, hs, ha, hI, hsym, hB, he, hform, ?_⟩
  intro X
  rw [quaternion_skew_centralizer_baseChange, ← hcentral X]
  have hcomm : (∀ q, X * quaternionComplexAction b ρ q = quaternionComplexAction b ρ q * X) ↔
      ∀ q z, X (quaternionComplexAction b ρ q z) = quaternionComplexAction b ρ q (X z) := by
    constructor
    · intro h q z; exact LinearMap.congr_fun (h q) z
    · intro h q; exact LinearMap.ext (h q)
  rw [hcomm, and_comm]

end HodgeLean.Foundations.Abdulali
