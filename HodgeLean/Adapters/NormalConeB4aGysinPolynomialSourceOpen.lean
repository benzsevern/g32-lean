import HodgeLean.Adapters.NormalConeB4aGysinPolynomialParameters
import HodgeLean.Adapters.NormalConeB4aGysinAffinePoint
import Mathlib.RingTheory.Length

noncomputable section
namespace HodgeLean.Adapters

/-- A rational point with a finite length regular coordinate slice gives
a flat principal neighborhood over the polynomial parameter space. -/
theorem a3b4a_gysin_polynomial_source_flat_neighborhood
    {n : ℕ} {S : Type} [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    [Algebra (MvPolynomial (Fin n) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) S]
    (q : Ideal S) [q.IsPrime] (w : S →ₐ[ℂ] ℂ) (hw : RingHom.ker w = q)
    (hzero : ∀ j : Fin n, w (algebraMap (MvPolynomial (Fin n) ℂ) S (MvPolynomial.X j)) = 0)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      (List.ofFn (fun j : Fin n => algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime q) (MvPolynomial.X j))))
    (m : ℕ) (hlen : Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ Ideal.ofList
        (List.ofFn (fun j : Fin n => algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime q) (MvPolynomial.X j)))) = m) :
    ∃ f : S, f ∉ q ∧ Module.Flat (MvPolynomial (Fin n) ℂ) (Localization.Away f) := by
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
  letI : Algebra.QuasiFiniteAt A q := a3b4a_gysin_quasiFiniteAt_of_affine_point p q w hw
  apply a3b4a_gysin_exists_flat_source_of_regular_parameters p q xs hspan
  simpa only [xs, List.map_ofFn, Function.comp_def] using hreg.toIsWeaklyRegular

end HodgeLean.Adapters
