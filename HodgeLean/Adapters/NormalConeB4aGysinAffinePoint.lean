import HodgeLean.Adapters.NormalConeB4aGysinResidueAugmentation

/-! # Quasi-finiteness at rational points over an affine base -/

noncomputable section
namespace HodgeLean.Adapters

/-- An Artinian local fibre at a field-valued point of a finite type algebra
is quasi-finite over the original affine base. -/
theorem a3b4a_gysin_quasiFiniteAt_of_affine_point
    {k D R : Type*} [Field k] [CommRing D] [CommRing R]
    [Algebra k D] [Algebra k R] [Algebra D R] [IsScalarTower k D R]
    [Algebra.FiniteType D R]
    (p : Ideal D) [p.IsPrime] (q : Ideal R) [q.IsPrime] [q.LiesOver p]
    (w : R →ₐ[k] k) (hw : RingHom.ker w = q)
    [IsArtinianRing (Localization.AtPrime q ⧸ p.map (algebraMap D (Localization.AtPrime q)))] :
    Algebra.QuasiFiniteAt D q := by
  have hu : ∀ y : q.primeCompl, IsUnit (w y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    exact y.property (hw ▸ hy)
  let L := Localization.AtPrime q
  let wL : L →ₐ[k] k := IsLocalization.liftAlgHom hu
  let I := p.map (algebraMap D L)
  have hI : I ≤ RingHom.ker wL := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro d hd
    change wL (algebraMap D L d) = 0
    rw [IsScalarTower.algebraMap_apply D R L]
    change IsLocalization.lift hu (algebraMap R L (algebraMap D R d)) = 0
    rw [IsLocalization.lift_eq]
    have hdq := (q.mem_of_liesOver p d).mp hd
    exact (show algebraMap D R d ∈ RingHom.ker w from hw.symm ▸ hdq)
  let A := L ⧸ I
  let ε : A →ₐ[k] k := Ideal.Quotient.liftₐ I wL (fun a ha => hI ha)
  have hε : Function.Surjective ε := fun b => ⟨algebraMap k A b, ε.commutes b⟩
  have : Nontrivial A := hε.nontrivial
  have : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have : Module.Finite k A := a3b4a_gysin_artinian_augmented_finite ε
  have : Module.Finite D A := Module.Finite.of_restrictScalars_finite k D A
  have : Algebra.WeaklyQuasiFiniteAt D q := by
    rw [Algebra.weaklyQuasiFiniteAt_iff, ← q.over_def p]
    exact (inferInstance : Algebra.QuasiFinite D A)
  exact Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q

end HodgeLean.Adapters
