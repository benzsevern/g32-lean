import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainCapUnit

noncomputable section
open CategoryTheory Limits CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality
universe u v

/-- Extension of canonical degree-zero cap maps is the actual identity cochain. -/
theorem retained_extended_cap_unit {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] (K : ChainComplex C ℕ) :
    retainedExtendedCap K 0 (fun q => (K.XIsoOfEq (Nat.zero_add q)).hom) =
      Cochain.ofHom (𝟙 (K.extend ComplexShape.embeddingDownNat)) := by
  apply Cochain.ext
  intro i j h
  have hij : i = j := by omega
  subst i
  by_cases hj : j ≤ 0
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
    have hi : ComplexShape.embeddingDownNat.f (0 + q) = -(q : ℤ) := by
      simp only [ComplexShape.embeddingDownNat_f, Nat.zero_add]
    rw [retained_extended_cap_component_of_degree K 0 q _ _ hi h, Cochain.ofHom_v]
    change (K.extendXIso ComplexShape.embeddingDownNat hi).hom ≫
      (K.XIsoOfEq (Nat.zero_add q)).hom ≫
      (K.extendXIso ComplexShape.embeddingDownNat (ComplexShape.embeddingDownNat_f q)).inv = 𝟙 _
    rw [HomologicalComplex.XIsoOfEq, eqToIso.hom, ← Category.assoc,
      retained_extend_xiso_transport K hi (ComplexShape.embeddingDownNat_f q) (Nat.zero_add q),
      Iso.hom_inv_id]
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat j (fun q hq => by
      simp only [ComplexShape.embeddingDownNat_f] at hq
      omega)).eq_of_tgt _ _

/-- The shifted morphism of the identity cocycle is the canonical zero-shift map. -/
theorem retained_identity_cocycle_shift_hom {C : Type u} [Category.{v} C] [Preadditive C]
    (K : CochainComplex C ℤ) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom (𝟙 K)) =
      (shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K := by
  apply Cocycle.equivHomShift.injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Cochain.ext
  intro i j h
  have hij : i = j := by omega
  cases hij
  simp only [Cocycle.equivHomShift_apply]
  change (Cochain.ofHom (𝟙 K)).v i i (add_zero i) =
    ((Cochain.ofHom ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K)).rightUnshift 0
      (zero_add 0)).v i i (add_zero i)
  rw [Cochain.rightUnshift_v _ 0 (zero_add 0) i i (add_zero i) i (add_zero i),
    Cochain.ofHom_v, Cochain.ofHom_v, CochainComplex.shiftFunctorZero_inv_app_f]
  simp [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

end HodgeLean.Foundations.QuotientDuality
