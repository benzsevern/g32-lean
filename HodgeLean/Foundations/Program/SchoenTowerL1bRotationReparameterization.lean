import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
namespace HodgeLean.Foundations.Program

/-- A formal expansion can be reparameterized by any represented series with
zero constant coefficient and invertible linear coefficient. -/
theorem s2v_l1b_rotation_expansion_reparameterize
    {R K : Type*} [CommRing R] [CommRing K]
    (c : K →+* R) (ι : R →+* PowerSeries K) (hι : Function.Injective ι)
    (hc : ∀ k, ι (c k) = PowerSeries.C k)
    (u : R) (hzero : PowerSeries.constantCoeff (ι u) = 0)
    (hlinear : IsUnit (PowerSeries.coeff 1 (ι u))) :
    ∃ ψ : R →+* PowerSeries K, Function.Injective ψ ∧
      (∀ k, ψ (c k) = PowerSeries.C k) ∧ ψ u = PowerSeries.X := by
  let P := ι u
  let Q := P.substInvOfIsUnit hlinear
  have hP : PowerSeries.HasSubst P := .of_constantCoeff_zero' hzero
  have hQ : PowerSeries.HasSubst Q := PowerSeries.HasSubst.substInvOfIsUnit P hlinear
  let ψ : R →+* PowerSeries K := (PowerSeries.substAlgHom hQ).toRingHom.comp ι
  have happ (v : R) : ψ v = PowerSeries.subst Q (ι v) := by
    change (PowerSeries.substAlgHom hQ) (ι v) = _
    rw [PowerSeries.coe_substAlgHom]
  have hleft (F : PowerSeries K) : PowerSeries.subst P (PowerSeries.subst Q F) = F := by
    rw [PowerSeries.subst_comp_subst_apply hQ hP,
      PowerSeries.subst_substInvOfIsUnit_left P hzero hlinear,
      PowerSeries.X_subst]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro v w hvw
    apply hι
    have ht := congrArg (fun F : PowerSeries K => PowerSeries.subst P F) hvw
    simpa only [happ, hleft] using ht
  · intro k
    rw [happ, hc, PowerSeries.subst_C]; rfl
  · rw [happ]
    exact PowerSeries.subst_substInvOfIsUnit_right P hzero hlinear

/-- A represented series of order one generates the same residue kernel as
the initial parameter. -/
theorem s2v_l1b_rotation_reparameterized_kernel
    {R K : Type*} [CommRing R] [CommRing K]
    (ι : R →+* PowerSeries K)
    [IsLocalHom (PowerSeries.constantCoeff.comp ι)]
    (u : R) (hu : ι u = PowerSeries.X)
    (hker : RingHom.ker (PowerSeries.constantCoeff.comp ι) = Ideal.span {u})
    (v : R) (hzero : PowerSeries.constantCoeff (ι v) = 0)
    (hlinear : IsUnit (PowerSeries.coeff 1 (ι v))) :
    RingHom.ker (PowerSeries.constantCoeff.comp ι) = Ideal.span {v} := by
  have hv : v ∈ Ideal.span {u} := by
    rw [← hker, RingHom.mem_ker]
    exact hzero
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hv
  have he : PowerSeries.coeff 1 (ι v) = PowerSeries.constantCoeff (ι w) := by
    rw [hw, map_mul, hu, PowerSeries.coeff_succ_X_mul]
    exact PowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hwunit : IsUnit w := by
    apply isUnit_of_map_unit (PowerSeries.constantCoeff.comp ι) w
    change IsUnit (PowerSeries.constantCoeff (ι w))
    rwa [← he]
  rw [hw, Ideal.span_singleton_mul_right_unit hwunit]
  exact hker

end HodgeLean.Foundations.Program
