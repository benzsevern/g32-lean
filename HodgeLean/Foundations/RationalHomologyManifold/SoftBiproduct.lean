import HodgeLean.Foundations.RationalHomologyManifold.SoftSheafTransport
import Mathlib.CategoryTheory.Sites.Abelian

/-! Finite biproducts of the existing soft sheaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An equality of restricted sections persists on a smaller open set.
Source: Mathlib, CategoryTheory.Sites.Sheaf; functoriality of restriction maps.
HC no distance; AV milestone no distance.
-/
theorem section_restriction_eq_of_le {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {U V W : Opens X} (hV : V ≤ U) (hW : W ≤ V)
    (t : F.obj.obj (Opposite.op ⊤)) (s : F.obj.obj (Opposite.op U))
    (h : F.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op t =
      F.obj.map (homOfLE hV).op s) :
    F.obj.map (homOfLE (show W ≤ ⊤ from le_top)).op t =
      F.obj.map (homOfLE (hW.trans hV)).op s := by
  have hw := congrArg (F.obj.map (homOfLE hW).op) h
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using hw

#print axioms section_restriction_eq_of_le
/-- The biproduct of two soft sheaves of abelian groups is soft.
Source: Bredon, Sheaf Theory, second edition, II.9; extending the two component sections on a common neighborhood.
HC no distance; AV milestone no distance.
-/
theorem isSoft_biprod {X : TopCat.{0}} (A B : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hA : IsSoft A) (hB : IsSoft B) : IsSoft (A ⊞ B) := by
  let F := A ⊞ B
  let ia : A ⟶ F := biprod.inl
  let ib : B ⟶ F := biprod.inr
  let pa : F ⟶ A := biprod.fst
  let pb : F ⟶ B := biprod.snd
  have hsplit (U : Opens X) (s : F.obj.obj (Opposite.op U)) :
      ia.hom.app (Opposite.op U) (pa.hom.app (Opposite.op U) s) +
        ib.hom.app (Opposite.op U) (pb.hom.app (Opposite.op U) s) = s := by
    have h := congrArg (fun f : F ⟶ F => f.hom.app (Opposite.op U))
      (show pa ≫ ia + pb ≫ ib = 𝟙 F from biprod.total)
    exact ConcreteCategory.congr_hom h s
  intro K U hK hKU s
  obtain ⟨Va, hva, hKVa, ta, ha⟩ := hA K U hK hKU (pa.hom.app (Opposite.op U) s)
  obtain ⟨Vb, hvb, hKVb, tb, hb⟩ := hB K U hK hKU (pb.hom.app (Opposite.op U) s)
  let V := Va ⊓ Vb
  have hVa : V ≤ Va := inf_le_left
  have hVb : V ≤ Vb := inf_le_right
  have hVU : V ≤ U := hVa.trans hva
  have ha' := section_restriction_eq_of_le A hva hVa ta _ ha
  have hb' := section_restriction_eq_of_le B hvb hVb tb _ hb
  refine ⟨V, hVU, (fun x hx => ⟨hKVa hx, hKVb hx⟩),
    ia.hom.app (Opposite.op ⊤) ta + ib.hom.app (Opposite.op ⊤) tb, ?_⟩
  rw [map_add]
  have hia := ConcreteCategory.congr_hom
    (ia.hom.naturality (homOfLE (show V ≤ ⊤ from le_top)).op) ta
  have hib := ConcreteCategory.congr_hom
    (ib.hom.naturality (homOfLE (show V ≤ ⊤ from le_top)).op) tb
  simp only [ConcreteCategory.comp_apply] at hia hib
  rw [← hia, ← hib, ha', hb']
  have hpa := ConcreteCategory.congr_hom (pa.hom.naturality (homOfLE hVU).op) s
  have hpb := ConcreteCategory.congr_hom (pb.hom.naturality (homOfLE hVU).op) s
  simp only [ConcreteCategory.comp_apply] at hpa hpb
  rw [← hpa, ← hpb]
  exact hsplit V _

#print axioms isSoft_biprod

end HodgeLean.Foundations.RationalHomologyManifold
