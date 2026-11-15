import HodgeLean.Foundations.DolbeaultCurve3Defs

/-! Transport of the existing soft-sheaf condition through actual sheaf isomorphisms.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Softness is retained by an actual isomorphism of sheaves of abelian groups.
Source: Bredon, Sheaf Theory, second edition, II.9; softness under sheaf isomorphisms.
HC no distance; AV milestone no distance.
-/
theorem isSoft_of_sheaf_iso {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (e : F ≅ G) (hF : IsSoft F) : IsSoft G := by
  intro K U hK hKU s
  obtain ⟨V, hV, hKV, t, ht⟩ := hF K U hK hKU (e.inv.hom.app (Opposite.op U) s)
  refine ⟨V, hV, hKV, e.hom.hom.app (Opposite.op ⊤) t, ?_⟩
  have htop := ConcreteCategory.congr_hom
    (e.hom.hom.naturality (homOfLE (show V ≤ ⊤ from le_top)).op) t
  have hU := ConcreteCategory.congr_hom
    (e.hom.hom.naturality (homOfLE hV).op) (e.inv.hom.app (Opposite.op U) s)
  simp only [ConcreteCategory.comp_apply] at htop hU
  have hcancel := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (Opposite.op U)) e.inv_hom_id) s
  change e.hom.hom.app (Opposite.op U) (e.inv.hom.app (Opposite.op U) s) = s at hcancel
  exact htop.symm.trans ((congrArg (e.hom.hom.app (Opposite.op V)) ht).trans
    (hU.trans (congrArg (G.obj.map (homOfLE hV).op) hcancel)))

#print axioms isSoft_of_sheaf_iso
end HodgeLean.Foundations.RationalHomologyManifold
