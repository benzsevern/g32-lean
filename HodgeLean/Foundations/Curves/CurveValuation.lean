import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.Length

/-! # Valuation-theoretic lemmas for curves

A DVR whose fraction field is `K` is maximal among the proper valuation subrings of `K`, and the
length-based order of an element is invariant under ring isomorphisms.
HC no distance; AV milestone no distance.
-/

noncomputable section
open IsDiscreteValuationRing

namespace HodgeLean.Foundations.Curves

/-- If a DVR with fraction field `K` lies in a proper valuation subring `V` of `K`, every element
of `V` comes from the DVR.
Source: Atiyah–Macdonald, Proposition 5.18 and Theorem 9.2. -/
theorem exists_algebraMap_eq_of_mem_valuationSubring {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (V : ValuationSubring K) (hR : ∀ r, algebraMap R K r ∈ V) (hV : V ≠ ⊤) {x : K}
    (hx : x ∈ V) : ∃ r, algebraMap R K r = x := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ V := by
    by_contra h
    push Not at h
    exact hV (eq_top_iff.mpr fun y _ ↦ h y)
  obtain ⟨a, ha⟩ := (ValuationRing.isInteger_or_isInteger R x).resolve_left
    fun ⟨r, hr⟩ ↦ hne ⟨r, hr⟩
  obtain ⟨b, hb⟩ := (ValuationRing.isInteger_or_isInteger R y).resolve_left
    fun ⟨r, hr⟩ ↦ hy (hr ▸ hR r)
  have hx0 : x ≠ 0 := by rintro rfl; exact hne ⟨0, map_zero _⟩
  have hy0 : y ≠ 0 := by rintro rfl; exact hy V.zero_mem
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact hy0 (inv_eq_zero.mp hb.symm)
  have hanu : ¬ IsUnit a := by
    intro hu
    apply hne
    refine ⟨(hu.unit⁻¹ : Rˣ), ?_⟩
    have h1 : algebraMap R K a * algebraMap R K ↑(hu.unit⁻¹) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    rw [← inv_inv x, ← ha]
    exact eq_inv_of_mul_eq_one_right h1
  have ha1 : 1 ≤ addVal R a := by
    by_contra h
    push Not at h
    have h0 : addVal R a ≤ addVal R 1 := by
      rw [addVal_one]; exact (Order.lt_one_iff.mp h).le
    exact hanu (isUnit_of_dvd_one (addVal_le_iff_dvd.mp h0))
  set m := (addVal R b).toNat
  have hbm : addVal R b = m := (ENat.natCast_toNat (by rwa [Ne, addVal_eq_top_iff])).symm
  obtain ⟨c, hc⟩ : b ∣ a ^ m := by
    apply addVal_le_iff_dvd.mp
    rw [addVal_pow, hbm]
    calc (m : ℕ∞) = m • (1 : ℕ∞) := by simp
      _ ≤ m • addVal R a := nsmul_le_nsmul_right ha1 _
  have hyx : y = algebraMap R K c * x ^ m := by
    have := congrArg (algebraMap R K) hc
    rw [map_pow, map_mul, ha, hb, inv_pow] at this
    field_simp at this ⊢
    exact this
  exact hy (hyx ▸ mul_mem (hR c) (pow_mem hx m))

/-- The length-based order of an element is invariant under ring isomorphisms.
Source: Stacks Project, Tag 02MD. -/
theorem ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    Ring.ord R x = Ring.ord S (e x) := by
  let := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl
  have hJ : Ideal.span {e x} = (Ideal.span {x}).map f := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let g := Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hJ
  rw [Ring.ord, Ring.ord, g.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

/-- The valuation subring of `K` given by a valuation ring with fraction field `K`. -/
def valuationSubringOfFractionRing (R K : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] : ValuationSubring K where
  toSubring := (algebraMap R K).range
  mem_or_inv_mem' x := (ValuationRing.isInteger_or_isInteger R x).imp
    (fun ⟨r, hr⟩ ↦ ⟨r, hr⟩) (fun ⟨r, hr⟩ ↦ ⟨r, hr⟩)

/-- Membership in the valuation subring of a valuation ring. -/
theorem mem_valuationSubringOfFractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {x : K} :
    x ∈ valuationSubringOfFractionRing R K ↔ ∃ r, algebraMap R K r = x := Iff.rfl

/-- Two injective maps to a field with the same image identify their sources, so the orders of
elements with the same image agree.
Source: Stacks Project, Tag 02MD. -/
theorem ord_eq_of_range_eq {R S K : Type*} [CommRing R] [CommRing S] [Field K] (f : R →+* K)
    (g : S →+* K) (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x, (∃ r, f r = x) ↔ ∃ s, g s = x) {r : R} {s : S} (hrs : f r = g s) :
    Ring.ord R r = Ring.ord S s := by
  have hrange : f.range = g.range := by ext x; exact h x
  let eR : R ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b hab ↦ hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩
  let eS : S ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab ↦ hg (congrArg Subtype.val hab), g.rangeRestrict_surjective⟩
  let e : R ≃+* S := eR.trans ((RingEquiv.subringCongr hrange).trans eS.symm)
  have he : e r = s := by
    apply hg
    have h1 : eS (e r) = RingEquiv.subringCongr hrange (eR r) := by simp [e]
    exact (congrArg Subtype.val h1).trans hrs
  rw [ord_ringEquiv e r, he]

end HodgeLean.Foundations.Curves
