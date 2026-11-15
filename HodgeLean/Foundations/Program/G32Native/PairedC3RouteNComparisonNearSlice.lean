import HodgeLean.Foundations.AlgebraicGeometry.ConormalLocalIsomorphism

/-! # Detecting an ideal comparison only near the retained slice -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A map invertible on ambient neighborhoods of every point of the image
becomes invertible on the source. No neighborhood away from that image
is needed.
Source: Hartshorne, Algebraic Geometry, II.5, locality of sheaf morphisms. -/
lemma paired_module_pullback_isIso_near_image
    {Q V : Scheme.{0}} (i : Q ⟶ V) {M N : V.Modules} (m : M ⟶ N)
    (h : ∀ x : Q, ∃ U : V.Opens, i x ∈ U ∧
      IsIso ((Scheme.Modules.pullback U.ι).map m)) :
    IsIso ((Scheme.Modules.pullback i).map m) := by
  apply Conormal.moduleMap_isIso_of_open_neighborhoods
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  letI := hU
  let W := i ⁻¹ᵁ U
  have h₁ : IsIso ((Scheme.Modules.pullback (i ∣_ U)).map
      ((Scheme.Modules.pullback U.ι).map m)) := inferInstance
  have h₂ : IsIso ((Scheme.Modules.pullback ((i ∣_ U) ≫ U.ι)).map m) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp (i ∣_ U) U.ι) m).mp h₁
  have h₃ : IsIso ((Scheme.Modules.pullback (W.ι ≫ i)).map m) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U)) m).mp h₂
  refine ⟨W, hx, ?_⟩
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp W.ι i) m).mpr h₃

#print axioms paired_module_pullback_isIso_near_image
end HodgeLean.Foundations.Program.G32Native
