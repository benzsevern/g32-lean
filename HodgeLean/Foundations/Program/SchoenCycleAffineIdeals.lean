import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers
import HodgeLean.Foundations.Program.SchoenCycleCartierAlgebra
import HodgeLean.Foundations.Program.SchoenCyclePairedBaseChange

/-! # Affine ideals in the paired slice calculation
Pullback of ideal sheaves corresponds to extension of ideals on affine schemes.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- On affine schemes the ideal of a pulled back sheaf is the extension
of its ideal along the map on global sections. -/
theorem s2e_affine_comap_ideal
    {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.map f.appTop.hom (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  apply eq_of_forall_ge_iff
  intro L
  have hglobal : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ ≤ L ↔
      I.comap f ≤ Scheme.IdealSheafData.ofIdealTop L := by
    constructor
    · intro h
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa using h
    · intro h
      simpa using h ⟨⊤, isAffineOpen_top X⟩
  rw [hglobal, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Ideal.map_le_iff_le_comap]
  have hmap : ((Scheme.IdealSheafData.ofIdealTop L).map f).ideal
      ⟨⊤, isAffineOpen_top Y⟩ = Ideal.comap f.appTop.hom L := by
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    simp
    rfl
  constructor
  · intro h
    simpa only [hmap] using h ⟨⊤, isAffineOpen_top Y⟩
  · intro h
    apply Scheme.IdealSheafData.le_of_isAffine
    rwa [hmap]

/-- A principal centre parameter remains regular on an affine Cartier slice,
using the local ideal-module freeness premise of the slice interface. -/
theorem s2e_affine_cartier_parameter_regular
    {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (K : Y.IdealSheafData) (z : Γ(Y, ⊤))
    (hK : K.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {z})
    (hfree : Nonempty (((K.comap f).ideal ⟨⊤, isAffineOpen_top X⟩) ≃ₗ[Γ(X, ⊤)]
      Γ(X, ⊤))) :
    Function.Injective (fun a : Γ(X, ⊤) => a * f.appTop.hom z) := by
  rw [s2e_affine_comap_ideal, hK, Ideal.map_span, Set.image_singleton] at hfree
  obtain ⟨e⟩ := hfree
  exact s2e_principal_free_ideal_regular (f.appTop.hom z) e

/-- The support of an ideal sheaf in affine spectrum coordinates is the
zero locus of its ideal of global sections. -/
theorem s2e_affine_support_in_spectrum
    {Y : Scheme} [IsAffine Y] (I : Y.IdealSheafData) :
    Y.isoSpec.inv ⁻¹' (I.support : Set Y) =
      PrimeSpectrum.zeroLocus (I.ideal ⟨⊤, isAffineOpen_top Y⟩ : Set Γ(Y, ⊤)) := by
  have h : (I.support : Set Y) =
      Y.zeroLocus (U := ⊤) (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    simpa only [TopologicalSpace.Opens.coe_top, Set.inter_univ] using
      I.coe_support_inter ⟨⊤, isAffineOpen_top Y⟩
  rw [h, ← IsAffineOpen.fromSpec_top, IsAffineOpen.fromSpec_preimage_zeroLocus]

/-- A paired affine Cartier slice misses the reduced branch locus away from
its Cartier centre, including its closure in the ambient affine scheme. -/
theorem s2e_affine_paired_cartier_branch_avoidance
    {Q X : Scheme} [IsAffine Q] [IsAffine X]
    (u : Q ⟶ X) (I J : X.IdealSheafData)
    (hpair : I.comap u = J.comap u)
    (hambient : Nonempty (((I ⊔ J).ideal ⟨⊤, isAffineOpen_top X⟩) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)))
    (hslice : Nonempty ((((I ⊔ J).comap u).ideal ⟨⊤, isAffineOpen_top Q⟩) ≃ₗ[Γ(Q, ⊤)]
      Γ(Q, ⊤))) :
    Disjoint (Set.range u)
      (closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))) := by
  obtain ⟨e⟩ := hambient
  obtain ⟨z, hz, _⟩ := s2e_free_ideal_regular_generator
    ((I ⊔ J).ideal ⟨⊤, isAffineOpen_top X⟩) e
  have hpairRing : Ideal.map u.appTop.hom (I.ideal ⟨⊤, isAffineOpen_top X⟩) =
      Ideal.map u.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top X⟩) := by
    rw [← s2e_affine_comap_ideal, ← s2e_affine_comap_ideal, hpair]
  have hring := s2e_paired_baseChange_strict_branch_avoidance u.appTop.hom
    (I.ideal ⟨⊤, isAffineOpen_top X⟩) (J.ideal ⟨⊤, isAffineOpen_top X⟩) z
    hz hpairRing (s2e_affine_cartier_parameter_regular u (I ⊔ J) z hz hslice)
  have hK : X.isoSpec.inv ⁻¹' ((I ⊔ J).support : Set X) =
      PrimeSpectrum.zeroLocus ({z} : Set Γ(X, ⊤)) := by
    rw [s2e_affine_support_in_spectrum, hz, PrimeSpectrum.zeroLocus_span]
  apply Set.disjoint_left.mpr
  rintro _ ⟨q, rfl⟩ hx
  let p : PrimeSpectrum Γ(Q, ⊤) := Q.isoSpec.hom q
  have hpoint : X.isoSpec.inv (PrimeSpectrum.comap u.appTop.hom p) = u q := by
    change (Spec.map u.appTop ≫ X.isoSpec.inv) p = u q
    rw [Scheme.isoSpec_inv_naturality]
    change u (Q.isoSpec.inv (Q.isoSpec.hom q)) = u q
    congr 1
    exact congrArg (fun g : Q ⟶ Q => g q) Q.isoSpec.hom_inv_id
  have hlocal : PrimeSpectrum.comap u.appTop.hom p ∈
      X.isoSpec.inv ⁻¹' closure ((I.support : Set X) \ ((I ⊔ J).support : Set X)) := by
    change X.isoSpec.inv (PrimeSpectrum.comap u.appTop.hom p) ∈
      closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))
    rwa [hpoint]
  rw [X.isoSpec.inv.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    X.isoSpec.inv.continuous, Set.preimage_sdiff, s2e_affine_support_in_spectrum, hK] at hlocal
  exact Set.disjoint_left.mp hring ⟨p, rfl⟩ hlocal

/-- Affine Cartier charts covering a paired slice give global avoidance
of the reduced branch locus outside the centre. -/
theorem s2e_paired_cartier_branch_avoidance_of_affine_cover
    {A : Type*} {Q X : Scheme} (u : Q ⟶ X) (I J : X.IdealSheafData)
    (hpair : I.comap u = J.comap u)
    (V U : A → Scheme) [∀ a, IsAffine (V a)] [∀ a, IsAffine (U a)]
    (v : ∀ a, V a ⟶ Q) (j : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (j a)]
    (t : ∀ a, V a ⟶ U a)
    (hsq : ∀ a, t a ≫ j a = v a ≫ u)
    (hcover : ∀ q : Q, ∃ (a : A) (p : V a), v a p = q)
    (hambient : ∀ a, Nonempty ((((I ⊔ J).comap (j a)).ideal
      ⟨⊤, isAffineOpen_top (U a)⟩) ≃ₗ[Γ(U a, ⊤)] Γ(U a, ⊤)))
    (hslice : ∀ a, Nonempty (((((I ⊔ J).comap (j a)).comap (t a)).ideal
      ⟨⊤, isAffineOpen_top (V a)⟩) ≃ₗ[Γ(V a, ⊤)] Γ(V a, ⊤))) :
    Disjoint (Set.range u)
      (closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨q, rfl⟩ hx
  obtain ⟨a, p, hp⟩ := hcover q
  have hpair' : (I.comap (j a)).comap (t a) = (J.comap (j a)).comap (t a) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      hsq, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hpair]
  have havoid := s2e_affine_paired_cartier_branch_avoidance (t a)
    (I.comap (j a)) (J.comap (j a)) hpair'
    (by rw [← Scheme.IdealSheafData.comap_sup]; exact hambient a)
    (by rw [← Scheme.IdealSheafData.comap_sup]; exact hslice a)
  have hpoint : j a (t a p) = u q := by
    have h := congrArg (fun g : V a ⟶ X => g p) (hsq a)
    change j a (t a p) = u (v a p) at h
    rwa [hp] at h
  have hlocal : t a p ∈ (j a) ⁻¹' closure
      ((I.support : Set X) \ ((I ⊔ J).support : Set X)) := by
    change j a (t a p) ∈ closure ((I.support : Set X) \ ((I ⊔ J).support : Set X))
    rwa [hpoint]
  rw [(j a).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    (j a).continuous, Set.preimage_sdiff] at hlocal
  have hsupportI := Scheme.IdealSheafData.support_comap I (j a)
  have hsupportK := Scheme.IdealSheafData.support_comap (I ⊔ J) (j a)
  have hlocal' : t a p ∈ closure
      (((I.comap (j a)).support : Set (U a)) \ (((I.comap (j a)) ⊔ (J.comap (j a))).support : Set (U a))) := by
    rw [← Scheme.IdealSheafData.comap_sup, hsupportI, hsupportK]
    exact hlocal
  exact Set.disjoint_left.mp havoid ⟨p, rfl⟩ hlocal'

end HodgeLean.Foundations.Program
