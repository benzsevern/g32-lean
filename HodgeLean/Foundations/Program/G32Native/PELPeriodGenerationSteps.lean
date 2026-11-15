import HodgeLean.Foundations.Program.G32Native.PELReferenceLieSimple
import HodgeLean.Foundations.Program.G32Native.PELAlmostSimpleContainment
import HodgeLean.Foundations.Program.G32Native.PELReferenceNormalization
import HodgeLean.Foundations.Program.G32Native.PELPeriodZariskiNormalization
import HodgeLean.Foundations.Program.G32Native.PELComplexSubgroupClosure
import HodgeLean.Foundations.Program.G32Native.PELPeriodClosureBounds
import HodgeLean.Foundations.Program.G32Native.PELPeriodNoncentral

noncomputable section
open HodgeLean.Foundations
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The reference quaternion-linear isometry group over the complex numbers,
with all four rational quaternion basis operators retained. -/
abbrev pelReferenceComplexIsometryGroup (R : PELSplitReference) : MatrixAlgGroup ℂ 12 :=
  pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
    (Set.range fun i : Fin 4 =>
      (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
        (algebraMap ℚ ℂ))

/-- Normalization of a complex algebraic subgroup extends from the ordinary
real identity component to the complex Zariski identity component.
Source: Borel, Linear Algebraic Groups, second edition, §§2.2, 7.6
(real identity-component density and algebraic normalizers). -/
theorem pel_real_component_normalization_aux (R : PELSplitReference)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hclosed : @IsClosed _ (g1_zariski ℂ 12) (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)))
    (hreal : ∀ g : pelRealIsometries R,
      g ∈ connectedComponent (1 : pelRealIsometries R) →
      ∀ x ∈ H, (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ * x *
        Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ H) :
    ∀ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      ∀ x ∈ H, g⁻¹ * x * g ∈ H := by
  exact pel_reference_real_normalization R H hclosed hreal

/-- A compatible period complex structure belongs to the connected complex
isometry group and has a noncommuting element in that group.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.2, 3.2–3.3;
Humphreys, Linear Algebraic Groups, §27.5 (the rank-three orthogonal
multiplicity representation and its centre). -/
theorem pel_period_noncentral_aux (R : PELSplitReference) (z : PELSplitComponent R) :
    pelPeriodMatrix R z.val ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R) ∧
      ∃ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
        ¬ Commute (pelPeriodMatrix R z.val) g := by
  exact ⟨pelPeriodMatrix_mem_component R z.val, pelPeriodMatrix_noncentral R z.val⟩

/-- A complex algebraic subgroup normalized by the connected rank-three
quaternionic isometry group, with a noncentral element in their intersection,
contains that connected group.
Source: Milne, Algebraic Groups (2017), Chapter 21 and Proposition 24.1;
Humphreys, Linear Algebraic Groups, §27.5 (almost-simplicity of SO(6)). -/
theorem pel_connected_isometry_normal_subgroup_aux (R : PELSplitReference)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hclosed : @IsClosed _ (g1_zariski ℂ 12) (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)))
    (hnormal : ∀ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : Matrix.GeneralLinearGroup (Fin 12) ℂ) (hx : x ∈ H)
    (hxC : x ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R))
    (hnoncentral : ∃ g ∈ g1_identityComponent (pelReferenceComplexIsometryGroup R),
      ¬ Commute x g) :
    g1_identityComponent (pelReferenceComplexIsometryGroup R) ⊆ (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
  letI := pel_reference_tangent_isSimple R
  exact pel_almost_simple_identityComponent_containment
    (pelReferenceComplexIsometryGroup R) H hclosed hnormal x hx hxC hnoncentral

/-- Assembly of the period-generation statement from normalization,
noncentrality and the connected isometry normal-subgroup calculation. -/
theorem pel_period_matrix_generation_of_steps (R : PELSplitReference)
    (G : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    (hG : g2_IsRatAlgSubgroup G)
    (hperiod : ∀ z : PELSplitComponent R, pelPeriodMatrix R z.val ∈ G) :
    g1_identityComponent (pelReferenceComplexIsometryGroup R) ⊆ G := by
  obtain ⟨H, hH⟩ := pelComplexSubgroupClosure (pelPeriodGeneratedSubgroup R)
  have hclosed : @IsClosed _ (g1_zariski ℂ 12) (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
    rw [hH]
    exact @isClosed_closure _ (g1_zariski ℂ 12) _
  have hreal : ∀ g : pelRealIsometries R,
      g ∈ connectedComponent (1 : pelRealIsometries R) →
      ∀ x ∈ H, (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ * x *
        Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ H := by
    intro g hg x hx
    change x ∈ (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) at hx
    change _ ∈ (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    rw [hH] at hx ⊢
    exact pelPeriodZariskiHull_conjugate R g hg x hx
  let z := pelSplitBasePoint R
  obtain ⟨hz, hnoncentral⟩ := pel_period_noncentral_aux R z
  have hx : pelPeriodMatrix R z.val ∈ H := by
    change _ ∈ (H : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))
    rw [hH]
    exact @subset_closure _ (g1_zariski ℂ 12) _ _ (pelPeriodMatrix_mem_generated R z)
  exact (pel_connected_isometry_normal_subgroup_aux R H hclosed
    (pel_real_component_normalization_aux R H hclosed hreal) _ hx hz hnoncentral).trans
      (by rw [hH]; exact pelPeriodComplexClosure_subset R G hG hperiod)

#print axioms pel_real_component_normalization_aux
#print axioms pel_period_noncentral_aux
#print axioms pel_connected_isometry_normal_subgroup_aux
#print axioms pel_period_matrix_generation_of_steps
end HodgeLean.Foundations.Program.GeneralTypeIII
