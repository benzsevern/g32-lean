import HodgeLean.Foundations.Program.G32Native.PairedC3EtaleCotangentIndependent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.RingHom.Etale

/-! # Cotangent independence of the original affine coordinate germs -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- Étale affine coordinates retain independent classes in the cotangent
space of the actual scheme stalk, via its affine localization map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8; EGA IV, 17.11.1. -/
theorem paired_c3_affine_cotangent_independent
    {K σ ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι] [DecidableEq σ]
    (X : Scheme.{0}) (U : X.affineOpens) (x : X) (hx : x ∈ U.1)
    (f : K →+* Γ(X, U.1)) (z : σ → Γ(X, U.1))
    (het : (MvPolynomial.eval₂Hom f z).Etale) (v : ι ↪ σ)
    (hm : ∀ i, (X.presheaf.germ U.1 x hx).hom (z (v i)) ∈
      maximalIdeal (X.presheaf.stalk x)) :
    LinearIndependent (ResidueField (X.presheaf.stalk x))
      (fun i => (maximalIdeal (X.presheaf.stalk x)).toCotangent
        ⟨(X.presheaf.germ U.1 x hx).hom (z (v i)), hm i⟩) := by
  let A := Γ(X, U.1)
  let B := X.presheaf.stalk x
  let g := (X.presheaf.germ U.1 x hx).hom
  let F := MvPolynomial.eval₂Hom f z
  letI : Algebra K A := f.toAlgebra
  letI : Algebra (MvPolynomial σ K) A := F.toAlgebra
  letI : IsScalarTower K (MvPolynomial σ K) A := .of_algebraMap_eq fun a => by
    change f a = (MvPolynomial.eval₂Hom f z) (MvPolynomial.C a)
    exact (MvPolynomial.eval₂Hom_C f z a).symm
  letI : Algebra A B := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  letI : Algebra (MvPolynomial σ K) B := (g.comp F).toAlgebra
  letI : Algebra K B := (g.comp f).toAlgebra
  letI : IsScalarTower (MvPolynomial σ K) A B := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K (MvPolynomial σ K) B := .of_algebraMap_eq fun a => by
    change g (f a) = g ((MvPolynomial.eval₂Hom f z) (MvPolynomial.C a))
    exact congrArg g (MvPolynomial.eval₂Hom_C f z a).symm
  let P := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  letI : IsLocalization.AtPrime B P := U.2.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  letI : Algebra.Etale (MvPolynomial σ K) A := het
  letI : Algebra.FormallyEtale (MvPolynomial σ K) B :=
    Algebra.FormallyEtale.comp (MvPolynomial σ K) A B
  have hcoord (j : σ) : algebraMap (MvPolynomial σ K) B (MvPolynomial.X j) = g (z j) := by
    change g ((MvPolynomial.eval₂Hom f z) (MvPolynomial.X j)) = g (z j)
    rw [MvPolynomial.eval₂Hom_X']
  have hm' (i : ι) : algebraMap (MvPolynomial σ K) B (MvPolynomial.X (v i)) ∈ maximalIdeal B := by
    rw [hcoord]
    exact hm i
  have H := paired_c3_etale_cotangent_independent v hm'
  simp_rw [hcoord] at H
  exact H

#print axioms paired_c3_affine_cotangent_independent
end HodgeLean.Foundations.Program.G32Native
