import HodgeLean.Adapters.IntersectionProductBlochProjection
import HodgeLean.Foundations.Program.TorusAlgebraizationDefs

/-! # Evaluating regular functions of the theta Proj at theta points

A complex point `q : Spec ℂ ⟶ Proj A` lying in `D₊(t)` is `Spec` of the ring map
`(A_t)₀ → ℂ` obtained by evaluating `awayToSection` at `q`. For the point
`Proj.fromOfGlobalSections` of the evaluation `b5_evalGlobal z`, this ring map sends
`a / tᵐ` to `a(z) / t(z)ᵐ`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

section Generic

variable {σ' : Type*} {A : Type} [CommRing A] [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜]

/-- The ring map `(A_t)₀ → ℂ` of a complex point of `D₊(t)`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
def b56_awayPointHom (q : Spec ↧ℂ ⟶ Proj 𝒜) (t : A)
    (hq : q (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen 𝒜 t) :
    CommRingCat.of (HomogeneousLocalization.Away 𝒜 t) ⟶ ↧ℂ :=
  Proj.awayToSection 𝒜 t ≫ (Proj 𝒜).presheaf.germ _ _ hq ≫ Scheme.stalkClosedPointTo q

/-- A complex point of `D₊(t)` is `Spec` of its ring map `(A_t)₀ → ℂ`, followed by `awayι`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
theorem b56_awayPointHom_spec (q : Spec ↧ℂ ⟶ Proj 𝒜) {t : A} {m : ℕ} (ht : t ∈ 𝒜 m)
    (hm : 0 < m) (hq : q (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen 𝒜 t) :
    Spec.map (b56_awayPointHom 𝒜 q t hq) ≫ Proj.awayι 𝒜 t ht hm = q := by
  let U := Proj.basicOpen 𝒜 t
  rw [b56_awayPointHom, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U _ hq]
  change Spec.map (Scheme.stalkClosedPointTo q) ≫
    U.fromSpecStalkOfMem _ hq ≫ (Proj.basicOpenIsoSpec 𝒜 t ht hm).hom ≫ _ = q
  simp only [Proj.awayι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk q

/-- The ring map of a point written as `Spec ψ` followed by `awayι` is `ψ`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
theorem b56_awayPointHom_eq (q : Spec ↧ℂ ⟶ Proj 𝒜) {t : A} {m : ℕ} (ht : t ∈ 𝒜 m)
    (hm : 0 < m) (hq : q (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen 𝒜 t)
    (ψ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 t) ⟶ ↧ℂ)
    (hψ : Spec.map ψ ≫ Proj.awayι 𝒜 t ht hm = q) :
    b56_awayPointHom 𝒜 q t hq = ψ := by
  apply Spec.map_injective
  rw [← cancel_mono (Proj.awayι 𝒜 t ht hm), b56_awayPointHom_spec 𝒜 q ht hm hq, hψ]

/-- Points of the form `Spec ψ ≫ awayι` lie in `D₊(t)`.
Source: Mathlib `Proj.opensRange_awayι`. -/
theorem b56_mem_basicOpen_of_eq {t : A} {m : ℕ} (ht : t ∈ 𝒜 m) (hm : 0 < m)
    (q : Spec ↧ℂ ⟶ Proj 𝒜) (g : Spec ↧ℂ ⟶ Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 t)))
    (hg : g ≫ Proj.awayι 𝒜 t ht hm = q) :
    q (IsLocalRing.closedPoint ℂ) ∈ Proj.basicOpen 𝒜 t := by
  rw [← Proj.opensRange_awayι 𝒜 t ht hm, ← hg]
  exact ⟨g (IsLocalRing.closedPoint ℂ), rfl⟩

end Generic


section Theta

variable (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (Q : LinearMap.BilinForm ℤ Λ)

/-- A theta function that does not vanish at `z` is a unit after evaluation at `z`. -/
theorem b56_isUnit_evalGlobal (z : b5_V Λ F) {t : b5_S Λ F hF Q}
    (htz : b5_eval Λ F hF Q z t ≠ 0) : IsUnit (b5_evalGlobal Λ F hF Q z t) :=
  IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (Ne.isUnit htz)

/-- Evaluation at `z` of degree-zero fractions `a / tᵐ`, for `t(z) ≠ 0`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
def b56_awayEval (z : b5_V Λ F) (t : b5_S Λ F hF Q) (htz : b5_eval Λ F hF Q z t ≠ 0) :
    HomogeneousLocalization.Away (b5_grade Λ F hF Q) t →+* ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp
    (a3h_awayLift (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z)
      (b56_isUnit_evalGlobal Λ F hF Q z htz))

/-- The evaluation of `a / tᵏ` at `z` is `a(z) / t(z)ᵏ`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
theorem b56_awayEval_mk (z : b5_V Λ F) {t : b5_S Λ F hF Q} (htz : b5_eval Λ F hF Q z t ≠ 0)
    {d : ℕ} (hd : t ∈ b5_grade Λ F hF Q d) (k : ℕ) (a : b5_S Λ F hF Q)
    (ha : a ∈ b5_grade Λ F hF Q (k • d)) :
    b5_eval Λ F hF Q z t ^ k *
      b56_awayEval Λ F hF Q z t htz (HomogeneousLocalization.Away.mk _ hd k a ha) =
      b5_eval Λ F hF Q z a := by
  have h := a3h_awayLift_mk (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z)
    (b56_isUnit_evalGlobal Λ F hF Q z htz) hd k a ha
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom h
  rw [map_mul, map_pow] at h'
  simpa [b5_evalGlobal, b56_awayEval] using h'

/-- On `t(z) ≠ 0`, the theta point at `z` is `Spec` of the evaluation followed by `awayι`.
Source: Hartshorne, *Algebraic Geometry*, Theorem II.7.1 (proof); `a3h_fromOf_eq`. -/
theorem b56_fromOf_eq (z : b5_V Λ F)
    (hirr : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    {t : b5_S Λ F hF Q} (htz : b5_eval Λ F hF Q z t ≠ 0) {m : ℕ} (hm : 0 < m)
    (ht : t ∈ b5_grade Λ F hF Q m) :
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hirr =
      Spec.map (CommRingCat.ofHom (b56_awayEval Λ F hF Q z t htz)) ≫
        Proj.awayι (b5_grade Λ F hF Q) t ht hm := by
  rw [a3h_fromOf_eq (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hirr hm ht
    (b56_isUnit_evalGlobal Λ F hF Q z htz), ← SpecMap_ΓSpecIso_hom, ← Category.assoc,
    ← Spec.map_comp]
  rfl

variable {Λ F hF Q}

/-- A complex point given by the theta evaluation at `z` lies in `D₊(t)` when `t(z) ≠ 0`. -/
theorem b56_mem_basicOpen (z : b5_V Λ F)
    (hirr : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    (P : ComplexPoint (b5_model Λ F hF Q))
    (hP : P.left = Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hirr)
    {t : b5_S Λ F hF Q} (htz : b5_eval Λ F hF Q z t ≠ 0) {m : ℕ} (hm : 0 < m)
    (ht : t ∈ b5_grade Λ F hF Q m) :
    P ∈ Point.overOpen (Proj.basicOpen (b5_grade Λ F hF Q) t) :=
  b56_mem_basicOpen_of_eq (b5_grade Λ F hF Q) ht hm P.left _
    ((b56_fromOf_eq Λ F hF Q z hirr htz hm ht).symm.trans hP.symm)

/-- Evaluating `awayToSection (a / tᵏ)` at the theta point of `z` gives the evaluation of the
fraction at `z`.
Source: Hartshorne, *Algebraic Geometry*, Proposition II.2.5(b). -/
theorem b56_evaluate_awayToSection (z : b5_V Λ F)
    (hirr : (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
    (P : ComplexPoint (b5_model Λ F hF Q))
    (hP : P.left = Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) hirr)
    {t : b5_S Λ F hF Q} (htz : b5_eval Λ F hF Q z t ≠ 0) {m : ℕ} (hm : 0 < m)
    (ht : t ∈ b5_grade Λ F hF Q m) (x : HomogeneousLocalization.Away (b5_grade Λ F hF Q) t) :
    Point.evaluate (Proj.basicOpen (b5_grade Λ F hF Q) t)
      (Proj.awayToSection (b5_grade Λ F hF Q) t x) P = b56_awayEval Λ F hF Q z t htz x := by
  have hmem := b56_mem_basicOpen z hirr P hP htz hm ht
  unfold Point.evaluate
  split
  · change (b56_awayPointHom (b5_grade Λ F hF Q) P.left t hmem).hom x = _
    rw [b56_awayPointHom_eq (b5_grade Λ F hF Q) P.left ht hm hmem _
      ((b56_fromOf_eq Λ F hF Q z hirr htz hm ht).symm.trans hP.symm)]
    rfl
  · exact absurd hmem ‹_›

end Theta

end HodgeLean.Foundations.Program
