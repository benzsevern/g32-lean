import HodgeLean.Foundations.Program.SchoenCycleFixedStalkAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fixed-stalk pullback fixes the image of the actual base stalk. -/
theorem s2v_l1b_divisor_fixed_base_stalk
    {X Y : Scheme.{0}} (q : X ⟶ Y) (f : X ⟶ X) (h : f ≫ q = q)
    (p : X) (hf : f p = p) (c : Y.presheaf.stalk (q p)) :
    s2e_fixed_point_stalkPullback X f p hf ((q.stalkMap p).hom c) =
      (q.stalkMap p).hom c := by
  let E := X.presheaf.stalkCongr (.of_eq hf)
  let D := Y.presheaf.stalkCongr (.of_eq (congrArg q hf))
  have hs : q.stalkMap p ≫ E.inv = D.inv ≫ q.stalkMap (f p) := by
    apply (cancel_epi D.hom).mp
    rw [← Category.assoc, ← q.stalkMap_congr_point (f p) p hf,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hc : q.stalkMap p ≫ E.inv ≫ f.stalkMap p = q.stalkMap p := by
    rw [← Category.assoc, hs, Category.assoc, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom (f ≫ q) q h p]
    change D.inv ≫ D.hom ≫ q.stalkMap p = q.stalkMap p
    exact D.inv_hom_id_assoc _
  exact congrArg (fun k : Y.presheaf.stalk (q p) ⟶ X.presheaf.stalk p => k.hom c) hc

end HodgeLean.Foundations.Program
