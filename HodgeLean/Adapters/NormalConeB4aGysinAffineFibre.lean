import HodgeLean.Adapters.NormalConeB4aGysinStalkLength

/-! # The affine scheme fibre as the parameter quotient

This isomorphism keeps the scheme structure of the fibre, including nilpotents.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

/-- The actual affine parameter fibre is the spectrum of its parameter quotient.
Source: `pullbackSpecIso` and `a3b2_tensorEvalEquiv`. -/
def a3b4a_gysin_affineFibreIso
    {k R : Type} [Field k] [CommRing R] [Algebra (Polynomial k) R] (s : k) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) R)))
      (a3b2_point k s) ≅
    Spec (CommRingCat.of (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)})) := by
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom s).toAlgebra
  exact pullbackSpecIso (Polynomial k) R k ≪≫
    Scheme.Spec.mapIso (a3b2_tensorEvalEquiv R s rfl).symm.toCommRingCatIso.op


set_option backward.isDefEq.respectTransparency false in
/-- The local ring on the actual affine fibre has the quotient localization length. -/
theorem a3b4a_gysin_affineFibre_stalkLength
    {k R : Type} [Field k] [CommRing R] [Algebra (Polynomial k) R] (s : k)
    (p : PrimeSpectrum (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)})) :
    let F := pullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) R)))
      (a3b2_point k s)
    let y := (a3b4a_gysin_affineFibreIso (R := R) s).inv p
    Module.length (F.presheaf.stalk y) (F.presheaf.stalk y) =
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  let Q := R ⧸ Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}
  let e := a3b4a_gysin_affineFibreIso (R := R) s
  haveI : IsIso e.inv := inferInstance
  have h := a3b2_length_eq_of_ringEquiv (asIso (e.inv.stalkMap p)).commRingCatIsoToRingEquiv
  have h' := a3b2_length_eq_of_ringEquiv
    (Spec.stalkIso (CommRingCat.of Q) p).commRingCatIsoToRingEquiv
  exact h.trans h'


/-- An immersed affine fibre component has its quotient localization coefficient. -/
theorem a3b4a_gysin_affineFibre_imageCycle_coeff
    {k R : Type} [Field k] [CommRing R] [Algebra (Polynomial k) R] (s : k)
    {Z : Scheme.{0}} [IsNoetherian Z]
    (i : pullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) R)))
      (a3b2_point k s) ⟶ Z) [IsClosedImmersion i]
    (p : PrimeSpectrum (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}))
    (hp : p ∈ genericPoints (PrimeSpectrum (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}))) :
    a3b3_imageCycle i inferInstance (i ((a3b4a_gysin_affineFibreIso (R := R) s).inv p)) =
      ((Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat : ℚ) := by
  let e := a3b4a_gysin_affineFibreIso (R := R) s
  have hy : e.inv p ∈ genericPoints _ :=
    (a3b2_homeomorph_mem_genericPoints (Scheme.homeoOfIso e.symm) p).2 hp
  rw [a3b4a_gysin_imageCycle_coeff_stalkLength i _ hy,
    a3b4a_gysin_affineFibre_stalkLength s p]


set_option backward.isDefEq.respectTransparency false in
/-- The quotient chart identifies the fibre inclusion with the quotient ring map. -/
theorem a3b4a_gysin_affineFibreIso_inv_fst
    {k R : Type} [Field k] [CommRing R] [Algebra (Polynomial k) R] (s : k) :
    (a3b4a_gysin_affineFibreIso (R := R) s).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) R)))
        (a3b2_point k s) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}))) := by
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom s).toAlgebra
  let Φ := a3b2_tensorEvalEquiv R s rfl
  change (Spec.map (CommRingCat.ofHom Φ.toRingHom) ≫
    (pullbackSpecIso (Polynomial k) R k).inv) ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) R)))
        (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) k))) = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  ext a
  exact a3b2_tensorEvalEquiv_tmul R s rfl a

end HodgeLean.Adapters
