import HodgeLean.Foundations.Program.SchoenTransferQ3TangentialParameters
import HodgeLean.Foundations.Port.AlgebraicGeometry.Smooth.RegularLocal

/-! Shared support parameters using regularity of the actual target stalk. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing RingTheory.Sequence
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- An etale map transports a system of parameters at a regular target
stalk, without requiring the entire target support to be smooth. -/
theorem s4_q3_etale_regular_support_stalk_parameters
    {C D : Scheme.{0}} [IsLocallyNoetherian D]
    (f : C ⟶ D) [Etale f] (p : C) (r : ℕ)
    [IsRegularLocalRing (D.presheaf.stalk (f p))]
    (hr : Order.coheight (f p) = r) :
    ∃ rs : List (D.presheaf.stalk (f p)),
      rs.length = r ∧ Ideal.ofList rs = maximalIdeal (D.presheaf.stalk (f p)) ∧
      IsRegular (D.presheaf.stalk (f p)) rs ∧
      IsRegular (C.presheaf.stalk p) (rs.map (f.stalkMap p).hom) ∧
      Ideal.ofList (rs.map (f.stalkMap p).hom) = maximalIdeal (C.presheaf.stalk p) := by
  let R := D.presheaf.stalk (f p)
  let A := C.presheaf.stalk p
  have hdim : ringKrullDim R = r := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hr
  obtain ⟨rs, hlen, hgen, _, _⟩ := a3c_exists_regular_sop R
  have hlen' : rs.length = r := by
    rw [hdim] at hlen
    exact_mod_cast hlen
  have hreg := regular_sequence_of_maximal_generators R r rs hdim hlen' hgen
  have hsource := regular_stalk_parameters_pullback f p rs hreg
  letI : Algebra R A := (f.stalkMap p).hom.toAlgebra
  letI : IsLocalHom (algebraMap R A) := f.toLRSHom.prop p
  letI : Algebra.EssFiniteType R A := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f p
  letI : Algebra.FormallyUnramified R A := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact FormallyUnramified.stalkMap f p
  refine ⟨rs, hlen', hgen, hreg, hsource, ?_⟩
  rw [← Ideal.map_ofList, hgen]
  exact Algebra.FormallyUnramified.map_maximalIdeal

/-- A smooth ambient neighbourhood supplies regularity of the original
support stalk, through the actual open-immersion stalk isomorphism. -/
theorem s4_q3_regular_stalk_of_smooth_neighbourhood
    {D : Scheme.{0}} (q : D ⟶ Spec ↧ℂ) (U : D.Opens)
    (hU : Smooth (U.ι ≫ q)) (x : D) (hx : x ∈ U) :
    IsRegularLocalRing (D.presheaf.stalk x) := by
  let y : U.toScheme := ⟨x, hx⟩
  letI : Smooth (U.ι ≫ q) := hU
  letI : IsRegularLocalRing (U.toScheme.presheaf.stalk y) :=
    Smooth.isRegularLocalRing_stalk_complex (f := U.ι ≫ q) y
  let b := U.ι.stalkMap y
  let e := RingEquiv.ofBijective b.hom (ConcreteCategory.bijective_of_isIso b)
  exact IsRegularLocalRing.of_ringEquiv e.symm

end HodgeLean.Foundations.Program
