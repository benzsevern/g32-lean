import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The actual ideal sequence of a specified subscheme -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace HodgeLean.Foundations.Program.G32Native

/-- The kernel inclusion and actual structure-sheaf restriction form a short
exact sequence for every supplied subscheme immersion. -/
theorem paired_closedImmersion_ideal_shortExact
    {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] :
    (ShortComplex.mk
      (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))
      (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
      (kernel.condition _)).ShortExact := by
  let q := SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hq : Epi q := by
    apply F.epi_of_epi_map
    have h : TopCat.Presheaf.IsLocallySurjective (F.map q).hom := by
      apply (TopCat.Presheaf.isLocallySurjective_iff _).2
      intro U t x hx
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
      refine ⟨V, hVU, ?_, hxV⟩
      exact i.app_surjective V hV _
    letI : CategoryTheory.Sheaf.IsLocallySurjective (F.map q) := h
    infer_instance
  letI := hq
  exact { exact := ShortComplex.exact_kernel q }

end HodgeLean.Foundations.Program.G32Native
