import HodgeLean.Foundations.Program.G32Native.PELDomainContainment
import HodgeLean.Foundations.Program.G32Native.PELDomainLocus
import HodgeLean.Foundations.Program.G32Native.PELGenericBaire
import HodgeLean.Foundations.Program.G32Native.PELPeriodOpenPatch
import HodgeLean.Foundations.Program.G32Native.PELConjugacyNeighborhood
import HodgeLean.Foundations.Program.G32Native.PELPeriodConjugatesGenerate
import HodgeLean.Foundations.Program.G32Native.PELRationalComplexZeroSet
import HodgeLean.Foundations.Program.G32Native.PELPeriodGroupGeneration

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations
open scoped Quaternion

/-- A proper rational containment locus has empty interior on the retained domain. -/
theorem pelDomainHodgeGroup_containment_interior_eq_empty {R : PELSplitReference}
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G) (hproper : ¬ ∀ z : PELSplitComponent R, pelDomainHodgeGroup R z.val ⊆ G) :
    interior {z : PELSplitComponent R | pelDomainHodgeGroup R z.val ⊆ G} = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨S, hS⟩ := hG.1
  let s := MvPolynomial.map (algebraMap ℚ ℂ) '' S
  have hGs : G = g1_zeroSet s := hS.trans (pel_ratZeroSet_eq_complexZeroSet S)
  have hp := pel_period_open_patch_equations R _ isOpen_interior z hz s (by
    intro w hw
    rw [← hGs]
    exact (interior_subset hw) (pelDomain_period_mem R w.val))
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
  exact (pelDomainHodgeGroup_subset_isometries R w.val).trans hb

/-- Domain Hodge groups attain their rational algebraic envelope densely. -/
theorem pel_dense_hodge_generic_points (R : PELSplitReference) :
    Dense {z : PELSplitComponent R | pelDomainHodgeGroup R z.val =
      ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ ∀ w : PELSplitComponent R,
        pelDomainHodgeGroup R w.val ⊆ G}} :=
  pel_dense_family_group (fun z : PELSplitComponent R => pelDomainHodgeGroup R z.val)
    (fun z => g2_isRatAlgSubgroup_hodgeGroup _ _ R.basis)
    (fun G hG => pelDomainHodgeGroup_containment_isClosed G hG)
    (fun G hG hp => pelDomainHodgeGroup_containment_interior_eq_empty G hG hp)

/-- A point whose Hodge group contains every point's Hodge group.
Source: Mumford, Families of abelian varieties (1966), §§1–2;
Abdulali, Annals 155 (2002), Proposition 2.3.1. -/
theorem pel_exists_hodge_generic_point (R : PELSplitReference) :
    ∃ g : PELSplitComponent R, ∀ z : PELSplitComponent R,
      pelDomainHodgeGroup R z.val ⊆ pelDomainHodgeGroup R g.val := by
  letI : Nonempty (PELSplitComponent R) := ⟨pelSplitBasePoint R⟩
  obtain ⟨g, hg⟩ := (pel_dense_hodge_generic_points R).nonempty
  refine ⟨g, fun z => ?_⟩
  rw [hg]
  intro x hx G hG
  exact hG.2 z hx

/-- A Hodge-generic point selected by the existing Baire construction. -/
def pel_hodgeGenericPoint (R : PELSplitReference) : PELSplitComponent R :=
  Classical.choose (pel_exists_hodge_generic_point R)

theorem pel_hodgeGenericPoint_contains (R : PELSplitReference) (z : PELSplitComponent R) :
    pelDomainHodgeGroup R z.val ⊆ pelDomainHodgeGroup R (pel_hodgeGenericPoint R).val :=
  Classical.choose_spec (pel_exists_hodge_generic_point R) z

/-- The group of any Hodge-generic domain point is the connected PEL group.
Source: Abdulali, Annals 155 (2002), Proposition 2.3.1. -/
theorem pel_generic_point_hodgeGroup_eq (R : PELSplitReference) (g : PELSplitComponent R)
    (hg : ∀ z : PELSplitComponent R,
      pelDomainHodgeGroup R z.val ⊆ pelDomainHodgeGroup R g.val) :
    pelDomainHodgeGroup R g.val = pelGenericGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
          (algebraMap ℚ ℂ)) := by
  apply Set.Subset.antisymm (pelDomainHodgeGroup_subset_isometries R g.val)
  apply pel_period_matrix_generation_aux R _ (g2_isRatAlgSubgroup_hodgeGroup _ _ R.basis)
  intro z
  exact hg z (pelDomain_period_mem R z.val)

#print axioms pel_exists_hodge_generic_point
#print axioms pel_generic_point_hodgeGroup_eq
end HodgeLean.Foundations.Program.GeneralTypeIII
