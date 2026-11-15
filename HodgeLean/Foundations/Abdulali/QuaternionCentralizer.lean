import HodgeLean.Foundations.Abdulali.RepresentationCentralizer
import HodgeLean.Foundations.Abdulali.QuaternionInvolution

noncomputable section
open scoped TensorProduct Quaternion
namespace HodgeLean.Foundations.Abdulali

/-- Normal form of a complex quaternion representation with its retained
Rosati equation. The same splitting retains the chosen quadratic generator,
the action, the polarization, and the unique skew multiplicity operators.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.1–3.2 and §4, p. 923. -/
theorem complex_quaternion_skew_centralizer
    (b : ℂ) (hb : b ≠ 0)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : ℍ[ℂ, -3, 0, b] →ₐ[ℂ] Module.End ℂ V)
    (E : LinearMap.BilinForm ℂ V) (halt : ∀ z, E z z = 0) (hnd : E.Nondegenerate)
    (hadj : ∀ q z w, E (ρ q z) w = E z (ρ (star q) w)) :
    ∃ (s : ℂ) (a : ℍ[ℂ, -3, 0, b] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (n : ℕ) (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] V)
      (B : LinearMap.BilinForm ℂ (Fin n → ℂ)),
      s ^ 2 = -3 ∧ (∀ q, a (star q) = (a q).adjugate) ∧
      a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s] ∧
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ q z, ρ q (e z) = e ((Matrix.toLin' (a q)).rTensor (Fin n → ℂ) z)) ∧
      (∀ (x y : Fin 2 → ℂ) (u v : Fin n → ℂ),
        E (e (x ⊗ₜ[ℂ] u)) (e (y ⊗ₜ[ℂ] v)) =
          (x 0 * y 1 - x 1 * y 0) * B u v) ∧
      ∀ X : Module.End ℂ V,
        ((∀ q z, X (ρ q z) = ρ q (X z)) ∧
          ∀ z w, E (X z) w + E z (X w) = 0) ↔
        ∃! T : Module.End ℂ (Fin n → ℂ),
          (∀ u v, B (T u) v + B u (T v) = 0) ∧
          e.symm.conj X = T.lTensor (Fin 2 → ℂ) := by
  obtain ⟨s, hs, a, ha, hI⟩ := quaternion_split_with_involution b hb
  let τ := ρ.comp a.symm.toAlgHom
  have hτ (m : Matrix (Fin 2) (Fin 2) ℂ) z w :
      E (τ m z) w = E z (τ m.adjugate w) := by
    have hstar : star (a.symm m) = a.symm m.adjugate := by
      apply a.injective
      simpa only [a.apply_symm_apply] using ha (a.symm m)
    change E (ρ (a.symm m) z) w = E z (ρ (a.symm m.adjugate) w)
    rw [hadj, hstar]
  obtain ⟨n, e, B, hsym, hB, he, hform, hcentral⟩ :=
    polarized_matrix_representation_normal_form V τ E halt hnd hτ
  refine ⟨s, a, n, e, B, hs, ha, hI, hsym, hB, ?_, hform, ?_⟩
  · intro q z
    simpa only [τ, AlgHom.comp_apply, AlgEquiv.coe_algHom, a.symm_apply_apply] using he (a q) z
  · intro X
    rw [← hcentral X]
    constructor
    · rintro ⟨hc, hsk⟩
      exact ⟨fun m z => hc (a.symm m) z, hsk⟩
    · rintro ⟨hc, hsk⟩
      refine ⟨?_, hsk⟩
      intro q z
      simpa only [τ, AlgHom.comp_apply, AlgEquiv.coe_algHom, a.symm_apply_apply] using hc (a q) z

end HodgeLean.Foundations.Abdulali
