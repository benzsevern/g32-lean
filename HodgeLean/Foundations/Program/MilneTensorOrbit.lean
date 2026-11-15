import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import HodgeLean.Foundations.Program.MilneTensorTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_formTransport (B : LinearMap.BilinForm ℂ V) (e : V ≃ₗ[ℂ] V) :
    LinearMap.BilinForm ℂ V :=
  B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap

theorem m1b_formTransport_trans (B : LinearMap.BilinForm ℂ V)
    (e d : V ≃ₗ[ℂ] V) :
    m1b_formTransport (m1b_formTransport B e) d = m1b_formTransport B (e.trans d) := by
  ext x y
  rfl

theorem m1b_formTransport_same_isometry (B : LinearMap.BilinForm ℂ V)
    (e d : V ≃ₗ[ℂ] V) (h : m1b_formTransport B e = m1b_formTransport B d) :
    (e.trans d.symm).toLinearMap ∈ m1b_isometries B := by
  refine ⟨(Module.End.isUnit_iff _).mpr (e.trans d.symm).bijective, ?_⟩
  intro x y
  have he := LinearMap.congr_fun (LinearMap.congr_fun h (e x)) (e y)
  simpa only [m1b_formTransport, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply] using he.symm

theorem m1b_multilinear_transport_independent (B : LinearMap.BilinForm ℂ V)
    {r n : ℕ} (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (e d : V ≃ₗ[ℂ] V) (h : m1b_formTransport B e = m1b_formTransport B d) :
    f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap) =
      f.compLinearMap (fun _ => (m1b_copiesEquiv d r).symm.toLinearMap) := by
  apply MultilinearMap.ext
  intro v
  have hi := hf (e.trans d.symm).toLinearMap
    (m1b_formTransport_same_isometry B e d h)
    (fun j => (m1b_copiesEquiv e r).symm (v j))
  change f (fun j i => e.symm (v j i)) = f (fun j i => d.symm (v j i))
  change f (fun j i => d.symm (e (e.symm (v j i)))) =
    f (fun j i => e.symm (v j i)) at hi
  simpa only [LinearEquiv.apply_symm_apply] using hi.symm

def m1b_orbitExtension (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (Q : Set.range (m1b_formTransport B)) :
    MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ :=
  f.compLinearMap (fun _ =>
    (m1b_copiesEquiv (Classical.choose Q.property) r).symm.toLinearMap)

theorem m1b_orbitExtension_eval (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (Q : Set.range (m1b_formTransport B)) (e : V ≃ₗ[ℂ] V)
    (he : m1b_formTransport B e = Q.val) :
    m1b_orbitExtension B f Q =
      f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap) := by
  exact m1b_multilinear_transport_independent B f hf _ e
    ((Classical.choose_spec Q.property).trans he.symm)

def m1b_orbitTransport (B : LinearMap.BilinForm ℂ V) (d : V ≃ₗ[ℂ] V)
    (Q : Set.range (m1b_formTransport B)) : Set.range (m1b_formTransport B) :=
  ⟨m1b_formTransport Q.val d,
    ⟨(Classical.choose Q.property).trans d, by
      rw [← m1b_formTransport_trans, Classical.choose_spec Q.property]⟩⟩

theorem m1b_orbitExtension_equivariant (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (Q : Set.range (m1b_formTransport B)) (d : V ≃ₗ[ℂ] V)
    (v : Fin n → Fin r → V) :
    m1b_orbitExtension B f (m1b_orbitTransport B d Q)
      (fun j => m1b_copiesEquiv d r (v j)) = m1b_orbitExtension B f Q v := by
  let e := Classical.choose Q.property
  have he : m1b_formTransport B e = Q.val := Classical.choose_spec Q.property
  have hed : m1b_formTransport B (e.trans d) = (m1b_orbitTransport B d Q).val := by
    change m1b_formTransport B (e.trans d) = m1b_formTransport Q.val d
    rw [← m1b_formTransport_trans, he]
  rw [m1b_orbitExtension_eval B f hf _ (e.trans d) hed,
    m1b_orbitExtension_eval B f hf Q e he]
  change f (fun j i => e.symm (d.symm (d (v j i)))) = f (fun j i => e.symm (v j i))
  simp only [LinearEquiv.symm_apply_apply]

theorem m1b_orbitExtension_base (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v) :
    m1b_orbitExtension B f ⟨B, ⟨LinearEquiv.refl ℂ V, rfl⟩⟩ = f := by
  rw [m1b_orbitExtension_eval B f hf _ (LinearEquiv.refl ℂ V) rfl]
  apply MultilinearMap.ext
  intro v
  rfl

theorem m1b_orbitExtension_unique (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (g : Set.range (m1b_formTransport B) → MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hg : ∀ Q d v, g (m1b_orbitTransport B d Q)
      (fun j => m1b_copiesEquiv d r (v j)) = g Q v)
    (hbase : g ⟨B, ⟨LinearEquiv.refl ℂ V, rfl⟩⟩ = f) :
    g = m1b_orbitExtension B f := by
  funext Q
  apply MultilinearMap.ext
  intro v
  let e := Classical.choose Q.property
  let Q₀ : Set.range (m1b_formTransport B) := ⟨B, ⟨LinearEquiv.refl ℂ V, rfl⟩⟩
  have hQ : m1b_orbitTransport B e Q₀ = Q :=
    Subtype.ext (Classical.choose_spec Q.property)
  have h := hg Q₀ e (fun j => (m1b_copiesEquiv e r).symm (v j))
  rw [hQ, hbase] at h
  change g Q (fun j i => e (e.symm (v j i))) = f (fun j i => e.symm (v j i)) at h
  change g Q v = f (fun j i => e.symm (v j i))
  simpa only [LinearEquiv.apply_symm_apply] using h

theorem m1b_symmetric_forms_same_orbit [FiniteDimensional ℂ V]
    (B C : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hsB : ∀ x y, B x y = B y x) (hsC : ∀ x y, C x y = C y x) :
    C ∈ Set.range (m1b_formTransport B) := by
  have hb : B.toQuadraticMap.associated = B := QuadraticMap.associated_left_inverse ℂ hsB
  have hc : C.toQuadraticMap.associated = C := QuadraticMap.associated_left_inverse ℂ hsC
  obtain ⟨e⟩ := QuadraticForm.equivalent_of_isAlgClosed B.toQuadraticMap C.toQuadraticMap
    (by rw [hb]; exact hB.1) (by rw [hc]; exact hC.1)
  have he : C.toQuadraticMap.comp e.toLinearEquiv.toLinearMap = B.toQuadraticMap := by
    ext x
    exact e.map_app x
  have heB := congrArg (QuadraticMap.associatedHom ℂ) he
  rw [QuadraticMap.associated_comp, hc, hb] at heB
  refine ⟨e.toLinearEquiv, ?_⟩
  ext x y
  have h := LinearMap.congr_fun (LinearMap.congr_fun heB (e.toLinearEquiv.symm x))
    (e.toLinearEquiv.symm y)
  simpa only [m1b_formTransport, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using h.symm

end HodgeLean.Foundations.Program
