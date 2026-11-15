import HodgeLean.Adapters.NormalConeB4aGysinAffineSliceModel

/-! # Field-valued points of residue-preserving comparison models -/

noncomputable section
namespace HodgeLean.Adapters

/-- A rational affine point identifies the residue field of its prime with
the scalar field, retaining evaluation on every affine function. -/
theorem a3b4a_gysin_exists_rational_residue_equiv
    {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    (q : Ideal R) [q.IsPrime] (w : R →ₐ[k] k) (hw : RingHom.ker w = q) :
    ∃ E : q.ResidueField ≃ₐ[k] k,
      ∀ r : R, E (algebraMap R q.ResidueField r) = w r := by
  have hu : q.primeCompl ≤ (IsUnit.submonoid k).comap w.toMonoidHom := by
    intro r hr
    change IsUnit (w r)
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hr (hw ▸ hz)
  let E := Ideal.ResidueField.liftₐ q w (le_of_eq hw.symm) hu
  have hE : Function.Surjective E := fun b => ⟨algebraMap k q.ResidueField b, E.commutes b⟩
  exact ⟨AlgEquiv.ofBijective E ⟨E.injective, hE⟩,
    fun r => Ideal.ResidueField.liftₐ_algebraMap q w _ hu r⟩

/-- A residue-preserving base change lifts a rational point to a rational
point of the comparison base, with its prescribed prime and base evaluation. -/
theorem a3b4a_gysin_exists_rational_comparison_point
    {k D E : Type*} [Field k] [CommRing D] [CommRing E]
    [Algebra k D] [Algebra k E] [Algebra D E] [IsScalarTower k D E]
    (p : Ideal D) [p.IsPrime] (P : Ideal E) [P.IsPrime] [P.LiesOver p]
    (v : D →ₐ[k] k) (hv : RingHom.ker v = p)
    (hres : Function.Bijective (Ideal.ResidueField.mapₐ p P
      (Algebra.ofId D E) (P.over_def p))) :
    ∃ w : E →ₐ[k] k, RingHom.ker w = P ∧
      ∀ d : D, w (algebraMap D E d) = v d := by
  obtain ⟨e, he⟩ := a3b4a_gysin_exists_rational_residue_equiv p v hv
  let a := AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ p P (Algebra.ofId D E) (P.over_def p)) hres
  let eP : P.ResidueField ≃ₐ[k] k := (a.symm.restrictScalars k).trans e
  let w : E →ₐ[k] k := eP.toAlgHom.comp (IsScalarTower.toAlgHom k E P.ResidueField)
  refine ⟨w, ?_, ?_⟩
  · ext r
    change eP (algebraMap E P.ResidueField r) = 0 ↔ r ∈ P
    constructor
    · intro hz
      apply Ideal.algebraMap_residueField_eq_zero.mp
      exact eP.injective (hz.trans (map_zero eP).symm)
    · intro hr
      rw [Ideal.algebraMap_residueField_eq_zero.mpr hr, map_zero]
  · intro d
    change e (a.symm (algebraMap E P.ResidueField (algebraMap D E d))) = v d
    have ha : a (algebraMap D p.ResidueField d) =
        algebraMap E P.ResidueField (algebraMap D E d) := by
      simp [a, IsScalarTower.algebraMap_apply D E P.ResidueField]
    rw [← ha, a.symm_apply_apply]
    exact he d

end HodgeLean.Adapters
