import HodgeLean.Foundations.Program.SchoenCycleAffineCurveParameter

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A unit in the actual marked stalk has an exact unit representative
on an arbitrarily small affine neighbourhood of that same point. -/
theorem s2e_c1_affine_unit_germ_representative
    (X : Scheme) (p : X) (U : X.Opens) (hp : p ∈ U)
    (u : (X.presheaf.stalk p)ˣ) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : V ≤ U) (hV : p ∈ V)
      (v : Γ(X, V)ˣ), (X.presheaf.germ V p hV).hom (v : Γ(X, V)) = u := by
  obtain ⟨W, hW, hWU, hpW, s, hs⟩ := s2e_affine_germ_representative X p U hp (u : X.presheaf.stalk p)
  have hpV : p ∈ X.basicOpen s := (X.mem_basicOpen s p hpW).mpr (hs ▸ u.isUnit)
  obtain ⟨v, hv⟩ := X.toRingedSpace.isUnit_res_basicOpen s
  refine ⟨X.basicOpen s, hW.basicOpen s, (X.basicOpen_le s).trans hWU, hpV, v, ?_⟩
  rw [hv]
  change (X.presheaf.map (X.basicOpen_le s).hom.op ≫
    X.presheaf.germ (X.basicOpen s) p hpV).hom s = u
  rw [X.presheaf.germ_res]
  exact hs

end HodgeLean.Foundations.Program
