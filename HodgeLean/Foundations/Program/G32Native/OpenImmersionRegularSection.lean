import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! Regular sections remain regular under open immersions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pulling a regular section on an affine open through an open immersion preserves regularity. -/
theorem g32l4_openImmersion_regular_section {X Y : Scheme.{0}}
    (f : Y ⟶ X) [IsOpenImmersion f] (U : X.affineOpens)
    (s : Γ(X, U)) (hs : s ∈ nonZeroDivisors Γ(X, U)) :
    f.app U s ∈ nonZeroDivisors Γ(Y, f ⁻¹ᵁ U.1) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro z hz
  apply TopCat.Presheaf.section_ext Y.sheaf (f ⁻¹ᵁ U.1) z 0
  intro y hy
  change f y ∈ U.1 at hy
  change Y.presheaf.germ _ y hy z = Y.presheaf.germ _ y hy 0
  rw [map_zero]
  have he : IsIso (f.stalkMap y) := inferInstance
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have hreg := map_mem_nonZeroDivisors_of_ringEquiv e
    (Scheme.IdealSheafData.germ_mem_nonZeroDivisors U hy hs)
  change f.stalkMap y (X.presheaf.germ U.1 (f y) hy s) ∈
    nonZeroDivisors (Y.presheaf.stalk y) at hreg
  rw [Scheme.Hom.germ_stalkMap_apply f U.1 y hy s] at hreg
  apply (mem_nonZeroDivisors_iff.mp hreg).1
  have hg := congrArg (fun w => Y.presheaf.germ (f ⁻¹ᵁ U.1) y hy w) hz
  simpa only [map_mul, map_zero] using hg

end HodgeLean.Foundations.Program
