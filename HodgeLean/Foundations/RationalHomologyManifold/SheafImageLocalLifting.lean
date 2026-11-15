import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian

/-! Local primitive sections of actual image sheaves.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A section of an actual image sheaf has local representatives in the source sheaf.
Source: Mathlib, Topology.Sheaves.LocallySurjective, isLocallySurjective_iff_epi.
HC no distance; AV milestone no distance.
-/
theorem sheaf_image_section_locally_lifts (X : TopCat.{0})
    {A B : TopCat.Sheaf AddCommGrpCat.{0} X} (f : A ⟶ B) (U : Opens X)
    (s : (image f).obj.obj (Opposite.op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U) (t : A.obj.obj (Opposite.op V)), x ∈ V ∧
      f.hom.app (Opposite.op V) t = (image.ι f).hom.app (Opposite.op V)
        ((image f).obj.map (homOfLE hV).op s) := by
  let g := factorThruImage f
  have hg : Epi g := by infer_instance
  have hsurj := (TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr hg
  obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp hsurj U s x hx
  refine ⟨V, hV, t, hxV, ?_⟩
  have hf := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (Opposite.op V)) (image.fac f)) t
  change (image.ι f).hom.app (Opposite.op V) (g.hom.app (Opposite.op V) t) =
    f.hom.app (Opposite.op V) t at hf
  exact hf.symm.trans (congrArg ((image.ι f).hom.app (Opposite.op V)) ht)

#print axioms sheaf_image_section_locally_lifts
end HodgeLean.Foundations.RationalHomologyManifold
