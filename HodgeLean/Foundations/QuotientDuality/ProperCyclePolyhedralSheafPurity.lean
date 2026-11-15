import HodgeLean.Foundations.QuotientDuality.ProperCyclePolyhedralPurity

/-! # Actual lower supported sheaf vanishing for finite subcomplex supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace Opposite
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual supported cohomology sheaf of a finite geometric subcomplex vanishes below the ambient orientation degree minus the support dimension.
Source: properCycle_finite_subcomplex_relative_vanishes; TopCat.Presheaf.isZero_stalk_of_cofinal_sections; Bredon, Sheaf Theory, second edition, V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_finite_subcomplex_support_sheaf_vanishes {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [LinearOrder E]
    (K D : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (V : Finset E) (hV : ∀ a ∈ K.vertices, a ∈ V)
    (N : ℕ) (hvan : ∀ j : ℕ, j ≠ N → ∀ x : K.space,
      Subsingleton (orientationGroup (TopCat.of K.space) j x))
    (m : ℕ) (hdim : ∀ s ∈ D.faces, s.card ≤ m)
    (n : ℕ) (hbound : n + m ≤ N) :
    IsZero (supportRelativeCohomologySheaf (TopCat.of K.space)
      {z : K.space | z.val ∈ D.space} n) := by
  let X := TopCat.of K.space
  let A : Set X := {z : K.space | z.val ∈ D.space}
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  let P := supportRelativeCohomologyPresheaf X A n
  have hP : IsZero (P.stalk x) := by
    apply TopCat.Presheaf.isZero_stalk_of_cofinal_sections
    intro U hxU
    refine ⟨U, le_rfl, hxU, ?_⟩
    have hz := properCycle_finite_subcomplex_relative_vanishes K D hK hDK V hV
      N hvan m hdim n hbound U
    exact @AddCommGrpCat.isZero_of_subsingleton _ (ModuleCat.subsingleton_of_isZero hz)
  let η := supportRelativeCohomologyToSheaf X A n
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  exact hP.of_iso (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).symm

end HodgeLean.Foundations.QuotientDuality
