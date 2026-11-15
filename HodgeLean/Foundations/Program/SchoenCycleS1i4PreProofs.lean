import HodgeLean.Foundations.Program.SchoenCycleS1i4FlatTower
import Mathlib.AlgebraicGeometry.Noetherian
import HodgeLean.Foundations.Program.SchoenCycleS1i4Pre2Proofs
import HodgeLean.Foundations.Program.SchoenCycleActualAnalyticAdic
import HodgeLean.Foundations.Program.SchoenCycleNativeAnalyticStalk
import HodgeLean.Foundations.Program.SchoenCycleFaithfulIdealContraction

/-! # Native analytic comparison predecessors
Implication from the actual smooth chart comparison to principal ideal descent.
The analytic ring and comparison map are the existing native germ constructions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program
/-- Holomorphic germs in a finite dimensional smooth chart form a Noetherian ring.
Source: Serre, Géométrie algébrique et géométrie analytique, §1, no. 4,
printed p. 6; Weierstrass division for convergent power series. -/
theorem s2e_s1i4_native_noetherian_aux (d : ℕ) :
    IsNoetherianRing (s2e_nativeAnalyticGermRing d) := by
  induction d with
  | zero =>
    exact isNoetherianRing_of_ringEquiv ℂ
      (RingEquiv.ofBijective (s2e_nativeAnalyticGerm_value 0)
        s2e_s1i4_dimension_zero_aux).symm
  | succ d ih =>
    exact (isNoetherianRing_iff_ideal_fg _).mpr
      (s2e_s1i4_ideal_induction_aux d ih (s2e_s1i4_germ_division_aux d))

/-- The actual stalk comparison reflects every finite order relation.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6,
Proposition 3, printed pp. 9–11. -/
theorem s2e_s1i4_native_finite_injective_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (N : ℕ) :
    Function.Injective (s2e_adic_quotient_ring_map
      (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying))
      (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
      (s2e_stalk_nativeAnalyticGerm X d p) (IsLocalRing.map_maximalIdeal_le _) N) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  apply s2e_s1i4_order_reflection_aux X d p N
    (s2e_s1i4_algebraic_representatives_aux X d p N) (a - b)
  rw [map_sub]
  exact Ideal.Quotient.eq.mp hab

/-- Noetherianity, extended maximal ideals and the compatible adic isomorphism
give flatness for the actual centered-chart comparison.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6,
Proposition 3 and Corollary 1, printed pp. 9–11; Stacks Project, Tag 00MC. -/
theorem s2e_s1i4_native_flat_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X)
    (hnoeth : IsNoetherianRing (s2e_nativeAnalyticGermRing d))
    (hmax : (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying)).map
      (s2e_stalk_nativeAnalyticGerm X d p) =
        IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
    (hcompat : ∀ a : X.left.presheaf.stalk p.underlying,
      s2e_actualAnalytic_adic_stalkMap X d p
        (AdicCompletion.of (IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying))
          (X.left.presheaf.stalk p.underlying) a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d))
        (s2e_nativeAnalyticGermRing d) (s2e_stalk_nativeAnalyticGerm X d p a))
    (hbij : Function.Bijective (s2e_actualAnalytic_adic_stalkMap X d p)) :
    letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
    Module.Flat (X.left.presheaf.stalk p.underlying) (s2e_nativeAnalyticGermRing d) := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsNoetherianRing (s2e_nativeAnalyticGermRing d) := hnoeth
  exact s2e_flat_of_completion_equiv (X.left.presheaf.stalk p.underlying)
    (s2e_nativeAnalyticGermRing d) (s2e_stalk_nativeAnalyticGerm X d p)
    (s2e_actualAnalytic_adic_stalkMap X d p) hcompat hbij

/-- Flatness of the actual local comparison implies faithful flatness.
Source: Serre, Géométrie algébrique et géométrie analytique, §2, no. 6,
Proposition 3 and Corollary 1, printed pp. 9–11. -/
theorem s2e_s1i4_native_faithfullyFlat_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X)
    (hflat : letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
      Module.Flat (X.left.presheaf.stalk p.underlying) (s2e_nativeAnalyticGermRing d)) :
    letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
    Module.FaithfullyFlat (X.left.presheaf.stalk p.underlying) (s2e_nativeAnalyticGermRing d) := by
  letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
  letI := hflat
  letI : IsLocalHom (algebraMap (X.left.presheaf.stalk p.underlying)
      (s2e_nativeAnalyticGermRing d)) :=
    inferInstanceAs (IsLocalHom (s2e_stalk_nativeAnalyticGerm X d p))
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Analytic unit comparison detects actual principal stalk ideals.
Source: Serre, Géométrie algébrique et géométrie analytique,
Annales de l’Institut Fourier 6 (1956), §2, no. 6, Proposition 3 and Corollary 1, printed pp. 9–11. -/
theorem s2e_s1i4_native_assembly_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X)
    (hflat : letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
      Module.FaithfullyFlat (X.left.presheaf.stalk p.underlying)
        (s2e_nativeAnalyticGermRing d)) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) (η : (Fin d → ℂ) → ℂ)
    (hη : AnalyticAt ℂ η 0) (hη0 : η 0 ≠ 0)
    (he : (fun z => Point.evaluate U s ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) =ᶠ[nhds 0]
      (fun z => η z * Point.evaluate U t ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z)))) :
    Ideal.span {X.left.presheaf.germ U p.underlying hp s} =
      Ideal.span {X.left.presheaf.germ U p.underlying hp t} := by
  letI := (s2e_stalk_nativeAnalyticGerm X d p).toAlgebra
  letI := hflat
  apply Ideal.map_injective_of_faithfullyFlat (B := s2e_nativeAnalyticGermRing d)
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  change Ideal.span {(s2e_stalk_nativeAnalyticGerm X d p (X.left.presheaf.germ U p.underlying hp s))} =
    Ideal.span {(s2e_stalk_nativeAnalyticGerm X d p (X.left.presheaf.germ U p.underlying hp t))}
  rw [s2e_stalk_nativeAnalyticGerm_germ, s2e_stalk_nativeAnalyticGerm_germ]
  exact s2e_nativeAnalyticGerm_unit_principal_ideals X d p U hp s t η hη hη0 he

/-- A nonzero constant unit tests the native analytic ring independently.
Source: SchoenCycleNativeAnalyticGerms,
s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero and s2e_nativeAnalyticGerm_value. -/
theorem s2e_s1i4_preProofs_check : IsUnit (1 + 1 : s2e_nativeAnalyticGermRing 1) ∧
    (1 + 1 : s2e_nativeAnalyticGermRing 1) ≠ 0 := by
  have hv : s2e_nativeAnalyticGerm_value 1 (1 + 1 : s2e_nativeAnalyticGermRing 1) ≠ 0 := by
    simp only [map_add, map_one]
    norm_num
  exact ⟨(s2e_nativeAnalyticGerm_isUnit_iff_value_ne_zero 1 _).mpr hv,
    fun h => hv (by rw [h, map_zero])⟩

#print axioms s2e_s1i4_preProofs_check

end HodgeLean.Foundations.Program
