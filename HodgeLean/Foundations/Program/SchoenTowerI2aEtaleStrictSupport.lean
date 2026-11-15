import HodgeLean.Foundations.Program.SchoenTowerI2aStrictTransformSupport
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Reduced strict branch supports transport through an actual etale chart
commuting with the paired polynomial substitution.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Stacks Project, Tag 01UA, flat morphisms locally of finite presentation are open. -/
theorem s2v_i2a_etale_paired_strict_branch_support
    (A : Type) [CommRing A] [IsDomain A] (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    {U X Y : Scheme} (u : U ⟶ X) [IsOpenImmersion u] (f : X ⟶ Y)
    (c : Y ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A)))
    (v : U ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))) [Etale v]
    (D : Fin n → Y.IdealSheafData) (K : Y.IdealSheafData)
    (hD : ∀ k, (D k).support.carrier = c ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k})
    (hK : K.support.carrier = c ⁻¹'
      PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j})
    (hsq : (u ≫ f) ≫ c = v ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun k => if k = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X k)))) :
    ∀ k, u ⁻¹' ((s2c_strictTransform f (D k) K).support : Set X) =
      if k = i then ∅ else v ⁻¹' PrimeSpectrum.zeroLocus {MvPolynomial.X k} := by
  classical
  intro k
  rw [s2e_strictTransform_support_on_open]
  change closure ((u ≫ f) ⁻¹' ((D k).support.carrier \ K.support.carrier)) = _
  rw [hD k, hK, ← Set.preimage_sdiff]
  have hs : (u ≫ f) ⁻¹' (c ⁻¹'
      (PrimeSpectrum.zeroLocus ({MvPolynomial.X k} : Set (MvPolynomial (Fin n) A)) \
       PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j})) =
      v ⁻¹' (PrimeSpectrum.comap (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun l => if l = j then MvPolynomial.X i * MvPolynomial.X j else MvPolynomial.X l)) ⁻¹'
          (PrimeSpectrum.zeroLocus {MvPolynomial.X k} \
           PrimeSpectrum.zeroLocus {MvPolynomial.X i, MvPolynomial.X j})) := by
    change ((u ≫ f) ≫ c) ⁻¹' _ = (v ≫ Spec.map (CommRingCat.ofHom _)) ⁻¹' _
    rw [hsq]
    rfl
  rw [hs, ← v.isOpenMap.preimage_closure_eq_closure_preimage v.continuous,
    s2v_i2a_paired_polynomial_strict_support i j hij k]
  split_ifs <;> rfl

end HodgeLean.Foundations.Program
