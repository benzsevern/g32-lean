import HodgeLean.Foundations.Program.MilneTensorInvariantTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def m1b_totalOrbitExtension (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (Q : LinearMap.BilinForm ℂ V) : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ := by
  classical
  exact if h : Q ∈ Set.range (m1b_formTransport B) then m1b_orbitExtension B f ⟨Q, h⟩ else 0

theorem m1b_totalOrbitExtension_on_orbit (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (Q : Set.range (m1b_formTransport B)) :
    m1b_totalOrbitExtension B f Q.val = m1b_orbitExtension B f Q := by
  simp only [m1b_totalOrbitExtension, dite_eq_left Q.property]

theorem m1b_totalOrbitExtension_eval (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (e : V ≃ₗ[ℂ] V) :
    m1b_totalOrbitExtension B f (m1b_formTransport B e) =
      f.compLinearMap (fun _ => (m1b_copiesEquiv e r).symm.toLinearMap) := by
  rw [m1b_totalOrbitExtension_on_orbit B f ⟨m1b_formTransport B e, ⟨e, rfl⟩⟩]
  exact m1b_orbitExtension_eval B f hf _ e rfl

theorem m1b_formTransport_mem_orbit_iff (B Q : LinearMap.BilinForm ℂ V)
    (d : V ≃ₗ[ℂ] V) :
    m1b_formTransport Q d ∈ Set.range (m1b_formTransport B) ↔
      Q ∈ Set.range (m1b_formTransport B) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans d.symm, ?_⟩
    rw [← m1b_formTransport_trans, he]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q (d.symm (d x)) (d.symm (d y)) = Q x y
    simp only [LinearEquiv.symm_apply_apply]
  · rintro ⟨e, rfl⟩
    exact ⟨e.trans d, (m1b_formTransport_trans B e d).symm⟩

theorem m1b_totalOrbitExtension_equivariant (B : LinearMap.BilinForm ℂ V) {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → V) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (Q : LinearMap.BilinForm ℂ V) (d : V ≃ₗ[ℂ] V)
    (v : Fin n → Fin r → V) :
    m1b_totalOrbitExtension B f (m1b_formTransport Q d)
      (fun j c => d (v j c)) = m1b_totalOrbitExtension B f Q v := by
  classical
  by_cases hQ : Q ∈ Set.range (m1b_formTransport B)
  · have hQd := (m1b_formTransport_mem_orbit_iff B Q d).mpr hQ
    rw [m1b_totalOrbitExtension_on_orbit B f ⟨Q, hQ⟩,
      m1b_totalOrbitExtension_on_orbit B f ⟨m1b_formTransport Q d, hQd⟩]
    exact m1b_orbitExtension_equivariant B f hf ⟨Q, hQ⟩ d v
  · have hQd : m1b_formTransport Q d ∉ Set.range (m1b_formTransport B) :=
      fun h => hQ ((m1b_formTransport_mem_orbit_iff B Q d).mp h)
    simp only [m1b_totalOrbitExtension, dite_eq_right hQ, dite_eq_right hQd,
      MultilinearMap.zero_apply]

end HodgeLean.Foundations.Program
