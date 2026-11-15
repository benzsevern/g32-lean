import HodgeLean.Foundations.Program.RigidStartingSystemPeripheralClasses
import HodgeLean.Foundations.Program.RigidStartingSystemPeripheralPresentation

noncomputable section
open Set
namespace HodgeLean.Foundations.Program

theorem b65r_source_peripheral_presentation (x : b65r_sourceDomain)
    (M : FundamentalGroup b65r_sourceDomain x →*
      ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hM : ∀ p : Path x x, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
      b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val)) :
    ∃ δ : Fin 4 → FundamentalGroup b65r_sourceDomain x, (List.ofFn δ).prod = 1 ∧
      (∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
        ∃! φ : FundamentalGroup b65r_sourceDomain x →* G, ∀ i, φ (δ i) = v i) ∧
      ∀ i, IsConj (b65r_printedOperatorHom (b4b_generators i)) (M (δ i)) := by
  have ht := RiemannRochTop_positive_basis_outer_at b65r_sourcePoles
    b65r_sourcePoles_finite (show b65r_sourcePoles.Nonempty from ⟨0,by simp [b65r_sourcePoles]⟩)
    b65r_sourcePoles_re_inj
  have hp : (fun z : ℂ ↦ z ∉ b65r_sourcePoles) = b65r_sourceDomain := b65r_sourcePoles_domain
  rw [hp] at ht
  obtain ⟨γ,hgeom,hout,hu⟩ := ht x
  obtain ⟨n,e,R,L,hR,hRL,hbound,he,y,k,d,hd,hclass⟩ := hout
  apply b65r_reorder_peripheral_presentation e b65r_punctureLabelEquiv γ hu M
    (fun i ↦ b65r_printedOperatorHom (b4b_generators i))
  intro a
  cases a with
  | none =>
    have hb : b65r_punctureLabelEquiv.symm none = 3 := by
      apply b65r_punctureLabelEquiv.injective
      rw [Equiv.apply_symm_apply]
      rfl
    rw [hb]
    exact b65r_infinite_peripheral_class x M hM _ R L hR hRL hbound y k d hd hclass
  | some a =>
    obtain ⟨i,rfl⟩ := b65r_sourcePole_bijective.surjective a
    have hb : b65r_punctureLabelEquiv.symm (some (b65r_sourcePole i)) = i.castSucc := by
      apply b65r_punctureLabelEquiv.injective
      rw [Equiv.apply_symm_apply]
      fin_cases i <;> rfl
    rw [hb]
    exact b65r_finite_peripheral_class x M hM i _ (hgeom (b65r_sourcePole i))

end HodgeLean.Foundations.Program
