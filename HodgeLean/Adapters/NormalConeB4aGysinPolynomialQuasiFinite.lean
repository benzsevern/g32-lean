import HodgeLean.Adapters.NormalConeB4aGysinPolynomialParameters
import HodgeLean.Adapters.NormalConeB4aGysinAffinePoint
import Mathlib.RingTheory.Length

noncomputable section
namespace HodgeLean.Adapters

/-- A rational point whose coordinate slice has finite length is quasi-finite
over the polynomial parameter space. -/
theorem a3b4a_gysin_polynomial_slice_quasiFinite
    {n : ℕ} {S : Type} [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    [Algebra (MvPolynomial (Fin n) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S]
    (q : Ideal S) [q.IsPrime] (w : S →ₐ[ℂ] ℂ) (hw : RingHom.ker w = q)
    (hzero : ∀ j : Fin n, w (algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X j)) = 0)
    (m : ℕ) (hlen : Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ Ideal.ofList
        (List.ofFn (fun j : Fin n => algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime q) (MvPolynomial.X j)))) = m) :
    Algebra.QuasiFiniteAt (MvPolynomial (Fin n) ℂ) q := by
  let A := MvPolynomial (Fin n) ℂ
  let L := Localization.AtPrime q
  let v : A →ₐ[ℂ] ℂ := MvPolynomial.aeval (0 : Fin n → ℂ)
  let p := RingHom.ker v
  letI : p.IsPrime := RingHom.ker_isPrime v
  have heval : w.comp (IsScalarTower.toAlgHom ℂ A S) =
      MvPolynomial.aeval (0 : Fin n → ℂ) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change w (algebraMap A S (MvPolynomial.X j)) = 0
    exact hzero j
  letI : q.LiesOver p := ⟨by
    change p = q.comap (algebraMap A S)
    rw [← hw]
    change p = (RingHom.ker w.toRingHom).comap (algebraMap A S)
    rw [RingHom.comap_ker]
    exact (congrArg (fun f : A →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) heval).symm⟩
  letI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ A S
  let xs := List.ofFn (fun j : Fin n => (MvPolynomial.X j : A))
  have hspan : Ideal.ofList xs = p := a3b4a_gysin_zero_parameter_ideal n
  have hid : p.map (algebraMap A L) =
      Ideal.ofList (List.ofFn (fun j : Fin n => algebraMap A L (MvPolynomial.X j))) := by
    rw [← hspan, Ideal.map_ofList, List.map_ofFn]
    rfl
  have hlen : Module.length L (L ⧸ p.map (algebraMap A L)) = m := by
    rw [hid]
    exact hlen
  have hfl : IsFiniteLength L (L ⧸ p.map (algebraMap A L)) :=
    Module.length_ne_top_iff.mp (by rw [hlen]; exact ENat.natCast_ne_top m)
  haveI : IsArtinian L (L ⧸ p.map (algebraMap A L)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  haveI : IsArtinianRing (L ⧸ p.map (algebraMap A L)) :=
    isArtinian_of_tower L (inferInstance : IsArtinian L _)
  exact a3b4a_gysin_quasiFiniteAt_of_affine_point p q w hw

end HodgeLean.Adapters
