import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Open local sections with exact inverse-image ranges identify a scheme map
as an open immersion, including its injectivity and all stalk isomorphisms.
Source: Mathlib, `IsOpenImmersion.iff_isIso_stalkMap`. -/
theorem s2v_i2a_open_immersion_of_local_sections
    {X Y : Scheme.{0}} (g : X ⟶ Y)
    (hlocal : ∀ q : X, ∃ (V : Scheme.{0}) (u : V ⟶ Y) (f : V ⟶ X),
      IsOpenImmersion u ∧ IsOpenImmersion f ∧ f ≫ g = u ∧
      Set.range f = g ⁻¹' Set.range u ∧ q ∈ Set.range f) :
    IsOpenImmersion g := by
  have hinj : Function.Injective g := by
    intro q₁ q₂ hq
    obtain ⟨V, u, f, hu, hf, hfg, hrange, hq₁⟩ := hlocal q₁
    letI : IsOpenImmersion u := hu
    obtain ⟨v₁, rfl⟩ := hq₁
    have hq₂ : q₂ ∈ Set.range f := by
      rw [hrange]
      change g q₂ ∈ Set.range u
      rw [← hq]
      exact ⟨v₁, (congrArg (fun h : V ⟶ Y => h v₁) hfg).symm⟩
    obtain ⟨v₂, rfl⟩ := hq₂
    have hv : u v₁ = u v₂ := by
      simpa only [← Scheme.Hom.comp_apply, hfg] using hq
    exact congrArg f (u.isOpenEmbedding.injective hv)
  have hopen : IsOpenMap g := by
    intro O hO
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨q, hqO, rfl⟩
    obtain ⟨V, u, f, hu, hf, hfg, hrange, hq⟩ := hlocal q
    letI : IsOpenImmersion u := hu
    obtain ⟨v, rfl⟩ := hq
    have ho : IsOpen (u '' (f ⁻¹' O)) :=
      u.isOpenEmbedding.isOpenMap _ (hO.preimage f.continuous)
    have hp : g (f v) ∈ u '' (f ⁻¹' O) :=
      ⟨v, hqO, (congrArg (fun h : V ⟶ Y => h v) hfg).symm⟩
    apply Filter.mem_of_superset (ho.mem_nhds hp)
    rintro _ ⟨v', hv', rfl⟩
    exact ⟨f v', hv', congrArg (fun h : V ⟶ Y => h v') hfg⟩
  haveI (q : X) : IsIso (g.stalkMap q) := by
    obtain ⟨V, u, f, hu, hf, hfg, hrange, hq⟩ := hlocal q
    letI : IsOpenImmersion u := hu
    letI : IsOpenImmersion f := hf
    obtain ⟨v, rfl⟩ := hq
    haveI : IsOpenImmersion (f ≫ g) := hfg.symm ▸ hu
    haveI : IsIso (g.stalkMap (f v) ≫ f.stalkMap v) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right (f := f.stalkMap v) (g.stalkMap (f v))
  exact IsOpenImmersion.of_isIso_stalkMap g
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap g.continuous hinj hopen)

end HodgeLean.Foundations.Program
