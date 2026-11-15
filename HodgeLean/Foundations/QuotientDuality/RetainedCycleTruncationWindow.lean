import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.QuasiIso

/-! # Unchanged chain coordinates strictly above the orientation truncation -/

noncomputable section
open CategoryTheory CategoryTheory.Limits ComplexShape
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual good-truncation projection is invertible in every term above its boundary. -/
lemma retained_truncation_projection_component_isIso
    {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℤ)
    (b i : ℤ) (hi : b < i) : IsIso ((K.πTruncGE b).f i) := by
  have hj : (embeddingUpIntGE b).f (i-b).toNat = i := by
    change b + ((i-b).toNat : ℤ) = i
    omega
  dsimp only [CochainComplex.πTruncGE, HomologicalComplex.πTruncGE]
  rw [(embeddingUpIntGE b).isIso_liftExtend_f_iff _ _ hj]
  exact K.isIso_restrictionToTruncGE' (embeddingUpIntGE b) _ (by
    rw [boundaryGE_embeddingUpIntGE_iff]
    omega)

/-- Applying any additive functor retains homology above the unchanged three-term truncation window. -/
lemma retained_functor_truncation_quasiIsoAt
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ)
    (b i : ℤ) (hi : b+1 < i) :
    QuasiIsoAt ((F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE b)) i := by
  let g := (F.mapHomologicalComplex (.up ℤ)).map (K.πTruncGE b)
  have h (j : ℤ) (hj : b < j) : IsIso (g.f j) := by
    change IsIso (F.map ((K.πTruncGE b).f j))
    letI := retained_truncation_projection_component_isIso K b j hj
    infer_instance
  let φ := (HomologicalComplex.shortComplexFunctor D (.up ℤ) i).map g
  haveI : IsIso φ.τ₁ := h ((ComplexShape.up ℤ).prev i) (by rw [CochainComplex.prev]; omega)
  haveI : IsIso φ.τ₂ := h i (by omega)
  haveI : IsIso φ.τ₃ := h ((ComplexShape.up ℤ).next i) (by rw [CochainComplex.next]; omega)
  exact (quasiIsoAt_iff g i).mpr (ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ)

end HodgeLean.Foundations.QuotientDuality
