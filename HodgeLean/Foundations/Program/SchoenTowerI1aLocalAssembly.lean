import Mathlib.AlgebraicGeometry.OpenImmersion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_openImmersion_of_local_charts
    {X Y : Scheme} (f : X ⟶ Y) (hinj : Function.Injective f)
    (hlocal : ∀ x : X, ∃ (T : Scheme) (u : T ⟶ X),
      IsOpenImmersion u ∧ IsOpenImmersion (u ≫ f) ∧ ∃ t : T, u t = x) :
    IsOpenImmersion f := by
  have hopen : IsOpenMap f := by
    intro O hO
    apply isOpen_iff_forall_mem_open.mpr
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨T, u, hu, huf, t, ht⟩ := hlocal x
    letI := hu
    letI := huf
    refine ⟨(u ≫ f) '' (u ⁻¹' O), ?_, ?_, ?_⟩
    · rintro z ⟨s, hs, rfl⟩
      exact ⟨u s, hs, rfl⟩
    · exact (Scheme.Hom.isOpenEmbedding (u ≫ f)).isOpenMap _ (hO.preimage u.continuous)
    · exact ⟨t, by change u t ∈ O; rw [ht]; exact hx, congrArg f ht⟩
  haveI (x : X) : IsIso (f.stalkMap x) := by
    obtain ⟨T, u, hu, huf, t, rfl⟩ := hlocal x
    letI := hu
    letI := huf
    haveI : IsIso (f.stalkMap (u t) ≫ u.stalkMap t) := by
      rw [← Scheme.Hom.stalkMap_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right (f.stalkMap (u t)) (u.stalkMap t)
  exact IsOpenImmersion.of_isIso_stalkMap f
    (isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨f.continuous, hinj, hopen⟩)

end HodgeLean.Foundations.Program
