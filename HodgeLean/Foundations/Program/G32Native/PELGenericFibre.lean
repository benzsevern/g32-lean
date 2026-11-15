import HodgeLean.Foundations.Program.G32Native.PELContainmentLocus
import HodgeLean.Foundations.Program.G32Native.PELGenericFibreComparison
import HodgeLean.Foundations.Program.G32Native.PELGenericBaire
import HodgeLean.Foundations.Program.G32Native.PELPeriodOpenPatch
import HodgeLean.Foundations.Program.G32Native.PELConjugacyNeighborhood
import HodgeLean.Foundations.Program.G32Native.PELPeriodConjugatesGenerate
import HodgeLean.Foundations.Program.G32Native.PELRationalComplexZeroSet
import HodgeLean.Foundations.Program.G32Native.PELSplitHodgeContainment

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
open scoped Quaternion

/-- A proper rational containment locus has empty interior on the retained domain. -/
theorem pel_hodgeGroup_containment_interior_eq_empty {R : PELSplitReference}
    (F : PELSplitFamily R) (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G) (hproper : ¬ ∀ z, F.hodgeGroup z ⊆ G) :
    interior {z : PELSplitComponent R | F.hodgeGroup z ⊆ G} = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨S, hS⟩ := hG.1
  let s := MvPolynomial.map (algebraMap ℚ ℂ) '' S
  have hGs : G = g1_zeroSet s := hS.trans (pel_ratZeroSet_eq_complexZeroSet S)
  have hp := pel_period_open_patch_equations R _ isOpen_interior z hz s (by
    intro w hw
    rw [← hGs]
    exact (interior_subset hw) (pel_period_matrix_mem_hodgeGroup_aux R F w))
  have hc := pel_conjugacy_equations_of_real_neighborhood
    (R.form.map (algebraMap ℚ ℝ))
    (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℝ))
    (pelPeriodMatrix R z.val) s hp
  have hb := pel_period_conjugates_generate R z G hG (by
    intro g hg
    dsimp only [pelReferenceComplexIsometryGroup] at hg
    rw [pel_reference_complex_isometry_eq R] at hg
    rw [hGs]
    exact hc g hg)
  apply hproper
  intro w
  exact (F.hodgeGroup_subset_isometries w).trans hb

/-- Marked fibre groups attain the family group densely in the retained component. -/
theorem pel_dense_hodge_generic_fibres {R : PELSplitReference} (F : PELSplitFamily R) :
    Dense {z : PELSplitComponent R | F.hodgeGroup z = F.genericGroup} :=
  pel_dense_family_group F.hodgeGroup
    (fun z => g2_isRatAlgSubgroup_hodgeGroup _ _ (F.basis z))
    (fun G hG => pel_hodgeGroup_containment_isClosed F G hG)
    (fun G hG hproper => pel_hodgeGroup_containment_interior_eq_empty F G hG hproper)

/-- A retained fibre contains every marked fibre Hodge group. -/
theorem pel_exists_hodge_generic_fibre {R : PELSplitReference} (F : PELSplitFamily R) :
    ∃ g : PELSplitComponent R, ∀ z, F.hodgeGroup z ⊆ F.hodgeGroup g := by
  letI : Nonempty (PELSplitComponent R) := ⟨pelSplitBasePoint R⟩
  obtain ⟨g, hg⟩ := (pel_dense_hodge_generic_fibres F).nonempty
  refine ⟨g, fun z => ?_⟩
  rw [hg]
  exact F.hodgeGroup_subset_genericGroup z

/-- A selected Hodge-generic fibre, obtained from the existing Baire theorem. -/
def pel_hodgeGenericFibre {R : PELSplitReference} (F : PELSplitFamily R) :
    PELSplitComponent R := Classical.choose (pel_exists_hodge_generic_fibre F)

theorem pel_hodgeGenericFibre_contains {R : PELSplitReference} (F : PELSplitFamily R)
    (z : PELSplitComponent R) : F.hodgeGroup z ⊆ F.hodgeGroup (pel_hodgeGenericFibre F) :=
  Classical.choose_spec (pel_exists_hodge_generic_fibre F) z

#print axioms pel_hodgeGroup_containment_interior_eq_empty
#print axioms pel_dense_hodge_generic_fibres
#print axioms pel_exists_hodge_generic_fibre
end HodgeLean.Foundations.Program.GeneralTypeIII
