import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Basic
import HodgeLean.Adapters.NormalConeB4aGysinBridge2RegularWeights

/-! Exact slice lengths on the actual unreduced inverse support. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing RingTheory.Sequence
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- Near an inverse-component generic point, every parameter slice generating
the maximal ideal modulo the nilradical retains the unreduced multiplicity. -/
theorem s4_q3_inverse_component_regular_slice_length
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (q : X ⟶ W) (x : W.left) (η : (ccm3_inverseIdeal q.left x).subscheme)
    (hη : closure ({η} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme) :
    ∃ V : (ccm3_inverseIdeal q.left x).subscheme.Opens, η ∈ V ∧
      ∀ w ∈ V, ∀ rs : List ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w),
        ringKrullDim ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w) = rs.length →
        Ideal.ofList rs ⊔ nilradical ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w) =
          maximalIdeal ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w) →
        Module.length ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w)
          (((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w) ⧸ Ideal.ofList rs) =
            (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) ∧
        IsRegular ((ccm3_inverseIdeal q.left x).subscheme.presheaf.stalk w) rs := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let K := (ccm3_inverseIdeal q.left x).subscheme
  letI : IsLocallyNoetherian K :=
    LocallyOfFiniteType.isLocallyNoetherian (ccm3_inverseIdeal q.left x).subschemeι
  obtain ⟨V, hV, m, hm, hslices⟩ := a3b4g_exists_good_open_regular η hη
  have hmult : (genericMultiplicity q.left x η (ccm3_genericLength_finite_pos q x η hη).2 : ℕ∞) = m :=
    (genericMultiplicity_pos q x η hη).2.trans hm
  refine ⟨V, hV, ?_⟩
  intro w hw rs hdim hgen
  obtain ⟨hlen, hreg⟩ := hslices w hw rs hdim hgen
  refine ⟨hlen.trans hmult.symm, ?_⟩
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr hreg
  intro a ha
  have hle : Ideal.ofList rs ≤ maximalIdeal (K.presheaf.stalk w) := by
    rw [← hgen]
    exact le_sup_left
  exact hle (Ideal.subset_span ha)

end HodgeLean.Foundations.Program
