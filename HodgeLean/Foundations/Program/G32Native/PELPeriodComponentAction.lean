import HodgeLean.Foundations.Program.G32Native.PELPeriodConjugation
import Mathlib.Topology.Algebra.Group.Units

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The real quaternion-linear polarization isometries, in the reference basis.
Source: Abdulali, Annals 155 (2002), §§2.2, 3.2. -/
def pelRealIsometries (R : PELSplitReference) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℝ) :=
  pelIsometrySubgroup (R.form.map (algebraMap ℚ ℝ))
    (Set.range fun d => (R.operator d).map (algebraMap ℚ ℝ))

/-- The real isometry action on compatible complex structures uses inverse
conjugation, so it is a right action in these coordinates.
Source: Abdulali, Annals 155 (2002), §2.2. -/
def pelRealConjugate (R : PELSplitReference) (g : pelRealIsometries R)
    (z : PELSplitDomain R) : PELSplitDomain R :=
  pelPeriodConjugate R g.val g.property.1
    (fun d => (g.property.2 _ ⟨d, rfl⟩).eq) z

/-- The identity leaves every period point fixed. -/
theorem pelRealConjugate_one (R : PELSplitReference) (z : PELSplitDomain R) :
    pelRealConjugate R 1 z = z := by
  have he : Function.Injective (PELSplitDomain.J (R := R)) := by
    intro a b h
    cases a; cases b
    cases h
    rfl
  apply he
  change (↑((1 : pelRealIsometries R).val)⁻¹ : Matrix (Fin 12) (Fin 12) ℝ) * z.J *
    (↑((1 : pelRealIsometries R).val) : Matrix (Fin 12) (Fin 12) ℝ) = z.J
  simp

/-- Joint continuity uses the ordinary real matrix topology on the domain. -/
theorem pelRealConjugate_continuous (R : PELSplitReference) :
    Continuous (fun p : pelRealIsometries R × PELSplitDomain R =>
      pelRealConjugate R p.1 p.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : pelRealIsometries R × PELSplitDomain R =>
    (↑p.1.val⁻¹ : Matrix (Fin 12) (Fin 12) ℝ) * p.2.J *
      (↑p.1.val : Matrix (Fin 12) (Fin 12) ℝ))
  have hJ : Continuous (PELSplitDomain.J (R := R)) := continuous_induced_dom
  exact ((Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)).mul
    (hJ.comp continuous_snd)).mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))

/-- The real identity component preserves the retained period component.
This supplies the orbit-containment direction without identifying the
component with a homogeneous space.
Source: Abdulali, Annals 155 (2002), §2.2. -/
theorem pelRealConjugate_mem_component (R : PELSplitReference)
    (g : pelRealIsometries R) (hg : g ∈ connectedComponent (1 : pelRealIsometries R))
    (z : PELSplitComponent R) :
    pelRealConjugate R g z.val ∈ connectedComponent (pelSplitReferencePoint R) := by
  have h := (pelRealConjugate_continuous R).image_connectedComponent_subset
    (1, pelSplitReferencePoint R)
  rw [connectedComponent_prod] at h
  have hm := h ⟨(g, z.val), ⟨hg, z.property⟩, rfl⟩
  simpa only [pelRealConjugate_one] using hm

#print axioms pelRealIsometries
#print axioms pelRealConjugate
#print axioms pelRealConjugate_one
#print axioms pelRealConjugate_continuous
#print axioms pelRealConjugate_mem_component
end HodgeLean.Foundations.Program.GeneralTypeIII
