import HodgeLean.Foundations.Program.SchoenTowerI2aFieldHelpers
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # Transport through normal root covers
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A map from a generated field lifts through an embedded field containing its base and generator.
Source: Mathlib, Subfield.closure_le and RingHom.rangeRestrictFieldEquiv. -/
theorem s2v_i2a_lift_generated_field
    {R K F L : Type*} [CommRing R] [Field K] [Field F] [Field L]
    [Algebra R K] [Algebra R F] [Algebra R L]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (i : F →ₐ[R] L) (hv : ∃ w, i w = f v) :
    ∃ g : K →ₐ[R] F, i.comp g = f := by
  let S := i.toRingHom.fieldRange
  have hle : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) ≤
      S.comap f.toRingHom := by
    apply Subfield.closure_le.mpr
    intro x hx
    rcases hx with ⟨r, rfl⟩ | hx
    · exact ⟨algebraMap R F r, (i.commutes r).trans (f.commutes r).symm⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact hv
  have H (x : K) : f x ∈ S := hle (hgen.symm ▸ (show x ∈ (⊤ : Subfield K) from trivial))
  let fS : K →+* S := f.toRingHom.codRestrict S.toSubring H
  let g : K →+* F := i.toRingHom.rangeRestrictFieldEquiv.symm.toRingHom.comp fS
  have hg (x : K) : i (g x) = f x :=
    i.toRingHom.rangeRestrictFieldEquiv_apply_symm_apply (fS x)
  let gA : K →ₐ[R] F := { g with
    commutes' r := by
      apply i.injective
      change i (g (algebraMap R K r)) = i (algebraMap R F r)
      rw [hg, i.commutes, f.commutes] }
  refine ⟨gA, ?_⟩
  ext x
  exact hg x

/-- Every integral element lifts into a normal coefficient ring containing an embedding of its field in the fraction field.
Source: Mathlib, IsIntegralClosure.mk', IsIntegral.map and IsIntegral.tower_top. -/
theorem s2v_i2a_integralClosure_lift_to_normal_cover
    {R K A L : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L]
    [Algebra R K] [Algebra R A] [Algebra A L] [Algebra R L]
    [IsScalarTower R A L] [IsFractionRing A L]
    (f : K →ₐ[R] L) :
    ∃ β : integralClosure R K →ₐ[R] A,
      ∀ b, algebraMap A L (β b) = f (b : K) := by
  let e : integralClosure R K →ₐ[R] L := f.comp (integralClosure R K).val
  have hint (b : integralClosure R K) : IsIntegral A (e b) :=
    (b.property.map f).tower_top
  let t (b : integralClosure R K) := IsIntegralClosure.mk' A (e b) (hint b)
  have ht (b : integralClosure R K) : algebraMap A L (t b) = e b :=
    IsIntegralClosure.algebraMap_mk' A (e b) (hint b)
  have hinj := IsIntegralClosure.algebraMap_injective A A L
  let β : integralClosure R K →ₐ[R] A :=
    { toFun := t
      map_zero' := by apply hinj; simp only [ht, map_zero]
      map_one' := by apply hinj; simp only [ht, map_one]
      map_add' b c := by apply hinj; simp only [ht, map_add]
      map_mul' b c := by apply hinj; simp only [ht, map_mul]
      commutes' r := by
        apply hinj
        change algebraMap A L (t (algebraMap R (integralClosure R K) r)) =
          algebraMap A L (algebraMap R A r)
        rw [ht, e.commutes, ← IsScalarTower.algebraMap_apply R A L] }
  exact ⟨β, ht⟩

/-- Compatibility on the generator determines compatibility of field actions through an embedding.
Source: Mathlib, RingHom.eq_of_eqOn_of_field_closure_eq_top. -/
theorem s2v_i2a_generated_field_action_compatibility
    {R K L : Type*} [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra R L]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (d : K ≃ₐ[R] K) (g : L ≃ₐ[R] L)
    (hv : g (f v) = f (d v)) :
    ∀ x, g (f x) = f (d x) := by
  have H : g.toRingHom.comp f.toRingHom = f.toRingHom.comp d.toRingHom :=
    RingHom.eq_of_eqOn_of_field_closure_eq_top hgen (by
      intro x hx
      rcases hx with ⟨r, rfl⟩ | hx
      · change g (f (algebraMap R K r)) = f (d (algebraMap R K r))
        rw [f.commutes, g.commutes, d.commutes, f.commutes]
      · rcases Set.mem_singleton_iff.mp hx with rfl
        exact hv)
  intro x
  exact congrArg (fun h : K →+* L => h x) H

/-- A fixed evaluation on an equivariant cover fixes every integral-element evaluation in the generated field.
Source: Mathlib, RingHom.eq_of_eqOn_of_field_closure_eq_top and AlgEquiv.coe_mapIntegralClosure. -/
theorem s2v_i2a_normal_cover_inertia
    {R K A L F : Type*} [CommRing R] [Field K] [CommRing A] [Field L] [CommRing F]
    [Algebra R K] [Algebra R A] [Algebra R L]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (i : A →ₐ[R] L) (hinj : Function.Injective i)
    (β : integralClosure R K →ₐ[R] A)
    (hβ : ∀ b, i (β b) = f (b : K))
    (d : K ≃ₐ[R] K) (g : A ≃ₐ[R] A) (gL : L ≃ₐ[R] L)
    (hg : ∀ a, i (g a) = gL (i a)) (hv : gL (f v) = f (d v))
    (p : integralClosure R K →+* F) (q : A →+* F)
    (hp : ∀ b, p b = q (β b)) (hq : ∀ a, q (g a) = q a) :
    ∀ b, p (d.mapIntegralClosure b) = p b := by
  have hcompat := s2v_i2a_generated_field_action_compatibility v hgen f d gL hv
  have hβg (b : integralClosure R K) : β (d.mapIntegralClosure b) = g (β b) := by
    apply hinj
    calc
      i (β (d.mapIntegralClosure b)) = f (d (b : K)) := by
        simpa only [AlgEquiv.coe_mapIntegralClosure] using hβ (d.mapIntegralClosure b)
      _ = gL (f (b : K)) := (hcompat (b : K)).symm
      _ = i (g (β b)) := by rw [hg, hβ]
  intro b
  rw [hp, hβg, hq, ← hp]

/-- Rotating a zero-valued root fixes every evaluation in the algebra generated by the roots and the unit root.
Source: Mathlib, AlgHom.ext_of_adjoin_eq_top and Polynomial root-cover generators. -/
theorem s2v_i2a_root_cover_evaluation_fixed
    {R A F : Type*} [CommRing R] [CommRing A] [CommRing F]
    [Algebra R A] [Algebra R F]
    (n : ℕ) (w : Fin n → A) (u : A)
    (hgen : Algebra.adjoin R (Set.range w ∪ {u}) = ⊤)
    (g : A ≃ₐ[R] A) (j : Fin n) (ζ : R)
    (hg : ∀ k, g (w k) = if k = j then algebraMap R A ζ * w k else w k)
    (hu : g u = u) (q : A →ₐ[R] F) (hq : q (w j) = 0) :
    ∀ a, q (g a) = q a := by
  have H : q.comp g.toAlgHom = q := AlgHom.ext_of_adjoin_eq_top hgen (by
    intro a ha
    rcases ha with ⟨k, rfl⟩ | ha
    · change q (g (w k)) = q (w k)
      rw [hg]
      by_cases hk : k = j
      · rw [if_pos hk, hk, map_mul, hq, mul_zero]
      · rw [if_neg hk]
    · have hau : a = u := Set.mem_singleton_iff.mp ha
      change q (g a) = q a
      rw [hau, hu])
  intro a
  exact congrArg (fun h : A →ₐ[R] F => h a) H

end HodgeLean.Foundations.Program
