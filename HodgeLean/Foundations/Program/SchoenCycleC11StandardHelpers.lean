import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Localization
import Mathlib.RingTheory.Unramified.LocalStructure
import HodgeLean.Foundations.Program.SchoenCycleC11RootHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.StandardEtale

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Polynomial evaluation is continuous in a complex algebra point and its root variable.
Source: Mathlib, Polynomial.induction_on' and continuity of algebra-homomorphism evaluations. -/
theorem s2e_c11_relativePolynomial_continuous
    {A : Type} [CommRing A] [Algebra ℂ A] (p : Polynomial A) :
    Continuous (fun z : (A →ₐ[ℂ] ℂ) × ℂ => Polynomial.eval₂ z.1.toRingHom z.2 p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z
    exact Polynomial.eval₂_add _ _
  | monomial n a =>
    convert ((continuous_affineAlgebraHom_apply A a).comp continuous_fst).mul
      (continuous_snd.pow n) using 1
    funext z
    exact Polynomial.eval₂_monomial _ _

/-- Algebra-homomorphism evaluation commutes with the actual polynomial relation.
Source: Mathlib, Polynomial.hom_eval₂. -/
theorem s2e_c11_relativePolynomial_map
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (p : Polynomial A) (b : B) (φ : B →ₐ[ℂ] ℂ) :
    Polynomial.eval₂ (φ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom (φ b) p =
      φ (Polynomial.aeval b p) :=
  (Polynomial.hom_eval₂ (p := p) (f := algebraMap A B) (g := φ.toRingHom) b).symm

/-- Root data for an actual standard-etale pair over a complex algebra.
Source: Mathlib, StandardEtalePair.HasMap. -/
abbrev s2e_c11_standardRootData
    {A : Type} [CommRing A] [Algebra ℂ A] (P : StandardEtalePair A) :=
  {z : (A →ₐ[ℂ] ℂ) × ℂ // Polynomial.eval₂ z.1.toRingHom z.2 P.f = 0 ∧
    Polynomial.eval₂ z.1.toRingHom z.2 P.g ≠ 0}

/-- Root data are the open nonvanishing part of the relative polynomial zero locus.
Source: Mathlib, nested subtype topology. -/
def s2e_c11_standardRootOpenHomeomorph
    {A : Type} [CommRing A] [Algebra ℂ A] (P : StandardEtalePair A) :
    s2e_c11_standardRootData P ≃ₜ
      {z : s2e_c11_relativeRootLocus P.f //
        Polynomial.eval₂ z.1.1.toRingHom z.1.2 P.g ≠ 0} where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  invFun z := ⟨z.1.1, z.1.2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Projection from standard-etale root data has analytic local inverses over any complex algebra.
Source: Mathlib, implicit-function theorem and StandardEtalePair.HasMap.isUnit_derivative_f. -/
theorem s2e_c11_standardRoot_projection
    {A : Type} [CommRing A] [Algebra ℂ A] (P : StandardEtalePair A) :
    IsLocalHomeomorph (fun z : s2e_c11_standardRootData P => z.1.1) := by
  let S : Set (s2e_c11_relativeRootLocus P.f) :=
    {z | Polynomial.eval₂ z.1.1.toRingHom z.1.2 P.g ≠ 0}
  have hS : IsOpen S := isOpen_ne.preimage
    ((s2e_c11_relativePolynomial_continuous P.g).comp continuous_subtype_val)
  have hlocal : IsLocalHomeomorphOn (fun z : s2e_c11_relativeRootLocus P.f => z.1.1) S := by
    apply (s2e_c11_relativeRoot_regular_projection P.f).mono
    intro z hz
    letI : Algebra A ℂ := z.1.1.toRingHom.toAlgebra
    have hm : P.HasMap z.1.2 := ⟨z.2, isUnit_iff_ne_zero.mpr hz⟩
    exact isUnit_iff_ne_zero.mp hm.isUnit_derivative_f
  exact (s2e_c11_localHomeomorphOn_open_restrict _ S hS hlocal).comp
    (s2e_c11_standardRootOpenHomeomorph P).isLocalHomeomorph

/-- Read the actual base point and distinguished root from a standard-etale presentation point.
Source: Mathlib, StandardEtalePresentation.hasMap and polynomial evaluation naturality. -/
def s2e_c11_standardPresentation_read
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) (φ : B →ₐ[ℂ] ℂ) : s2e_c11_standardRootData P.P :=
  ⟨(φ.comp (IsScalarTower.toAlgHom ℂ A B), φ P.x), by
    constructor
    · rw [s2e_c11_relativePolynomial_map, P.hasMap.1, map_zero]
    · rw [s2e_c11_relativePolynomial_map]
      exact isUnit_iff_ne_zero.mp (P.hasMap.2.map φ)⟩

/-- The standard-etale universal property reconstructs a point from its base and root.
Source: Mathlib, StandardEtalePair.lift and StandardEtalePresentation.equivRing. -/
def s2e_c11_standardPresentation_lift
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) (z : s2e_c11_standardRootData P.P) : B →ₐ[ℂ] ℂ := by
  letI : Algebra A ℂ := z.1.1.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A ℂ :=
    IsScalarTower.of_algebraMap_eq (fun c => (z.1.1.commutes c).symm)
  have hz : P.P.HasMap z.1.2 := ⟨z.2.1, isUnit_iff_ne_zero.mpr z.2.2⟩
  exact ((P.P.lift z.1.2 hz).comp P.equivRing.toAlgHom).restrictScalars ℂ

/-- Reconstruction preserves both the base point and the specified root.
Source: Mathlib, StandardEtalePair.lift_X and algebra-homomorphism commutation. -/
theorem s2e_c11_standardPresentation_read_lift
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) (z : s2e_c11_standardRootData P.P) :
    s2e_c11_standardPresentation_read P (s2e_c11_standardPresentation_lift P z) = z := by
  letI : Algebra A ℂ := z.1.1.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A ℂ :=
    IsScalarTower.of_algebraMap_eq (fun c => (z.1.1.commutes c).symm)
  have hz : P.P.HasMap z.1.2 := ⟨z.2.1, isUnit_iff_ne_zero.mpr z.2.2⟩
  apply Subtype.ext
  apply Prod.ext
  · apply AlgHom.ext
    intro a
    change P.P.lift z.1.2 hz (P.equivRing (algebraMap A B a)) = z.1.1 a
    rw [P.equivRing.commutes, AlgHom.commutes]
    rfl
  · change P.P.lift z.1.2 hz (P.equivRing P.x) = z.1.2
    rw [P.equivRing_x, StandardEtalePair.lift_X]

/-- The base map and distinguished root uniquely determine a presentation point.
Source: Mathlib, StandardEtalePresentation.hom_ext. -/
theorem s2e_c11_standardPresentation_read_injective
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) :
    Function.Injective (s2e_c11_standardPresentation_read P) := by
  intro φ ψ h
  have hb := congrArg (fun z : s2e_c11_standardRootData P.P => z.1.1) h
  have hx := congrArg (fun z : s2e_c11_standardRootData P.P => z.1.2) h
  letI : Algebra A ℂ := (φ.comp (IsScalarTower.toAlgHom ℂ A B)).toRingHom.toAlgebra
  let φA : B →ₐ[A] ℂ := ⟨φ.toRingHom, fun _ => rfl⟩
  let ψA : B →ₐ[A] ℂ := ⟨ψ.toRingHom, fun a => congrArg (fun q : A →ₐ[ℂ] ℂ => q a) hb.symm⟩
  have he : φA = ψA := P.hom_ext hx
  exact AlgHom.ext (fun b => congrArg (fun q : B →ₐ[A] ℂ => q b) he)

/-- Reading the base and distinguished root is continuous for pointwise convergence.
Source: ComplexPoint.continuous_affineAlgebraHom_apply and product topology. -/
theorem s2e_c11_standardPresentation_read_continuous
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) : Continuous (s2e_c11_standardPresentation_read P) := by
  apply Continuous.subtype_mk
  have hb : Continuous (fun φ : B →ₐ[ℂ] ℂ => φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
    rw [continuous_induced_rng]
    exact continuous_pi (fun a => continuous_affineAlgebraHom_apply B (algebraMap A B a))
  exact hb.prodMk (continuous_affineAlgebraHom_apply B P.x)

/-- The standard presentation identifies points bijectively with their actual root data.
Source: Mathlib, StandardEtalePresentation.hom_ext and StandardEtalePair.lift. -/
def s2e_c11_standardPresentationRootEquiv
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) : (B →ₐ[ℂ] ℂ) ≃ s2e_c11_standardRootData P.P :=
  Equiv.ofBijective (s2e_c11_standardPresentation_read P)
    ⟨s2e_c11_standardPresentation_read_injective P,
      fun z => ⟨s2e_c11_standardPresentation_lift P z, s2e_c11_standardPresentation_read_lift P z⟩⟩

/-- The presentation point correspondence preserves the actual pointwise topologies.
Source: Mathlib, StandardEtalePresentation.exists_mul_aeval_x_g_pow_eq_aeval_x. -/
def s2e_c11_standardPresentationRootHomeomorph
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    (P : StandardEtalePresentation A B) : (B →ₐ[ℂ] ℂ) ≃ₜ s2e_c11_standardRootData P.P where
  toEquiv := s2e_c11_standardPresentationRootEquiv P
  continuous_toFun := s2e_c11_standardPresentation_read_continuous P
  continuous_invFun := by
    let e := s2e_c11_standardPresentationRootEquiv P
    rw [continuous_induced_rng]
    apply continuous_pi
    intro b
    obtain ⟨q, n, hrel⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x b
    have hval (z : s2e_c11_standardRootData P.P) :
        e.symm z b = Polynomial.eval₂ z.1.1.toRingHom z.1.2 q /
          (Polynomial.eval₂ z.1.1.toRingHom z.1.2 P.g) ^ n := by
      let φ := e.symm z
      have he : s2e_c11_standardPresentation_read P φ = z := e.apply_symm_apply z
      have hb := congrArg (fun w : s2e_c11_standardRootData P.P => w.1.1) he
      have hx := congrArg (fun w : s2e_c11_standardRootData P.P => w.1.2) he
      change φ.comp (IsScalarTower.toAlgHom ℂ A B) = z.1.1 at hb
      change φ P.x = z.1.2 at hx
      have hr := congrArg φ hrel
      rw [map_mul, map_pow, ← s2e_c11_relativePolynomial_map,
        ← s2e_c11_relativePolynomial_map, hb, hx] at hr
      exact (eq_div_iff (pow_ne_zero n z.2.2)).mpr hr
    change Continuous (fun z : s2e_c11_standardRootData P.P => e.symm z b)
    rw [funext hval]
    exact ((s2e_c11_relativePolynomial_continuous q).comp continuous_subtype_val).div
      (((s2e_c11_relativePolynomial_continuous P.g).comp continuous_subtype_val).pow n)
      (fun z => pow_ne_zero n z.2.2)

/-- Etale algebra restriction has local analytic inverses by standard-etale source neighbourhoods.
Source: Algebra.IsEtaleAt.exists_isStandardEtale and ComplexAlgHom.localizationAwayAlgHomHomeomorph. -/
theorem s2e_c11_etaleAlgebra_local_inverse
    {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]
    [Algebra.Etale A B] :
    IsLocalHomeomorph (fun φ : B →ₐ[ℂ] ℂ => φ.comp (IsScalarTower.toAlgHom ℂ A B)) := by
  intro φ
  let q : Ideal B := RingHom.ker φ.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q
  letI := hstd
  let L := Localization.Away s
  let P : StandardEtalePresentation A L := Nonempty.some inferInstance
  let l := AlgebraicGeometry.ComplexAlgHom.localizationAwayAlgHomMap B s
  let r := fun φ : B →ₐ[ℂ] ℂ => φ.comp (IsScalarTower.toAlgHom ℂ A B)
  have hloc : IsLocalHomeomorph (r ∘ l) := by
    have hP := (s2e_c11_standardRoot_projection P.P).comp
      (s2e_c11_standardPresentationRootHomeomorph P).isLocalHomeomorph
    convert hP using 1
    funext ψ
    apply AlgHom.ext
    intro a
    change ψ (algebraMap B L (algebraMap A B a)) = ψ (algebraMap A L a)
    rw [IsScalarTower.algebraMap_apply A B L]
  have hOn := (hloc.isLocalHomeomorphOn (s := Set.univ)).of_comp_right
    ((AlgebraicGeometry.ComplexAlgHom.isOpenEmbedding_localizationAwayAlgHomMap B s).isLocalHomeomorph.isLocalHomeomorphOn
      (s := Set.univ))
  have hφ : φ s ≠ 0 := hs
  let u := (AlgebraicGeometry.ComplexAlgHom.localizationAwayAlgHomHomeomorph B s).symm ⟨φ, hφ⟩
  have hu : l u = φ := congrArg Subtype.val
    ((AlgebraicGeometry.ComplexAlgHom.localizationAwayAlgHomHomeomorph B s).apply_symm_apply ⟨φ, hφ⟩)
  exact hOn φ ⟨u, Set.mem_univ _, hu⟩

end HodgeLean.Foundations.Program
