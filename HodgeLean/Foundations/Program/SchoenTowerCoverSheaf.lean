import HodgeLean.Foundations.Program.SchoenTowerSheafDefs
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

theorem s2v_coverPresheaf_isSheaf {X E : TopCat} (f : X ⟶ E) :
    TopCat.Presheaf.IsSheaf (s2c_coverPresheaf f) := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro ι U sf hsf
  change (∀ i : ι, LocallyConstant {x : X // f x ∈ U i} ℂ) at sf
  let V : Opens X := (Opens.map f).obj (iSup U)
  have hex (x : V) : ∃ i, f x.val ∈ U i := Opens.mem_iSup.mp x.property
  choose idx hidx using hex
  let g : V → ℂ := fun x => sf (idx x) ⟨x.val, hidx x⟩
  have hg (i : ι) (x : X) (hx : f x ∈ U i) :
      g ⟨x, (le_iSup U i) hx⟩ = sf i ⟨x, hx⟩ := by
    let z : V := ⟨x, (le_iSup U i) hx⟩
    have hh := congrArg (fun s : LocallyConstant {x : X // f x ∈ U (idx z) ⊓ U i} ℂ =>
      s ⟨x, ⟨hidx z, hx⟩⟩) (hsf (idx z) i)
    exact hh
  have hglc : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_exists_open g).mpr
    intro x
    let i := idx x
    let xi : {z : X // f z ∈ U i} := ⟨x.val, hidx x⟩
    let inc : {z : X // f z ∈ U i} → V := fun z => ⟨z.val, (le_iSup U i) z.property⟩
    have hi : Topology.IsOpenEmbedding inc :=
      Opens.isOpenEmbedding_of_le ((Opens.map f).monotone (le_iSup U i))
    obtain ⟨W, hW, hxW, hc⟩ := (sf i).isLocallyConstant.exists_open xi
    refine ⟨inc '' W, hi.isOpenMap _ hW, ⟨xi, hxW, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    rw [show g (inc z) = sf i z from hg i z.val z.property]
    exact (hc z hz).trans (hg i x.val (hidx x)).symm
  let s : LocallyConstant V ℂ := ⟨g, hglc⟩
  refine ⟨s, ?_, ?_⟩
  · intro i
    apply LocallyConstant.ext
    intro x
    exact hg i x.val x.property
  · intro t ht
    change LocallyConstant V ℂ at t
    apply LocallyConstant.ext
    intro x
    have hi := congrArg (fun s : LocallyConstant {z : X // f z ∈ U (idx x)} ℂ =>
      s ⟨x.val, hidx x⟩) (ht (idx x))
    change t x = sf (idx x) ⟨x.val, hidx x⟩
    exact hi

theorem s2v_coverPresheaf_toSheafify_isIso {X E : TopCat} (f : X ⟶ E) :
    IsIso (toSheafify (Opens.grothendieckTopology E) (s2c_coverPresheaf f)) :=
  isIso_toSheafify _ (s2v_coverPresheaf_isSheaf f)

end HodgeLean.Foundations.Program
