import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import HodgeLean.Adapters.IntersectionProductScaf
import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalFlagRightExact
import HodgeLean.Foundations.Program.G32Native.PairedC3SmoothConormalMono

/-! # The conormal flag of nested smooth closed immersions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Positive coordinate cardinalities give smooth projective spaces.
Source: Hartshorne, Algebraic Geometry, II.8.16. -/
theorem paired_c3_projective_smooth (n : ℕ) (hn : 0 < n) :
    Smooth (ProjectiveSpace.toBase (Fin n) (Spec ↧ℂ)) := by
  cases n with
  | zero => omega
  | succ m => exact HodgeLean.Adapters.IntersectionProductScaf_projective_smooth m

#print axioms paired_c3_projective_smooth

/-- Nested smooth closed immersions have the short exact conormal flag
with the natural ideal-induced maps.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_smooth_conormal_flag_aux
    (Q F X : Scheme.{0})
    (q : Q ⟶ Spec ↧ℂ) (φ : F ⟶ Spec ↧ℂ) (x : X ⟶ Spec ↧ℂ)
    [Smooth q] [Smooth φ] [Smooth x]
    (i : F ⟶ X) (j : Q ⟶ F) (hi : i ≫ x = φ) (hj : j ≫ φ = q)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    let f := Conormal.comparisonMap i (j ≫ i) (𝟙 _) j
      (by rw [Category.comp_id])
    let g := ((Scheme.Modules.pullbackId _).app (Conormal.sheaf (j ≫ i))).inv ≫
      Conormal.comparisonMap (j ≫ i) j i (𝟙 _)
        (by rw [Category.id_comp])
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).ShortExact := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian x
  obtain ⟨w, he, hg⟩ := paired_c3_conormal_flag_right_exact i j
  exact ⟨w, ShortComplex.ShortExact.mk' he
    (paired_c3_smooth_conormal_first_mono_aux Q F X q φ x i j hi hj) hg⟩

#print axioms paired_c3_smooth_conormal_flag_aux

end HodgeLean.Foundations.Program.G32Native
