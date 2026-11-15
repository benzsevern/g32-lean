import HodgeLean.Foundations.Program.SchoenTowerL1aOpenSectionLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Actual principal restrictions of finite quotient diagrams

Implication from a finite affine quotient diagram and a nonvanishing denominator
to its actual compatible principal chart and restricted permutation lifts.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Principal restriction of the actual finite quotient retains the point,
the specified lifts, and localization on both actual global section rings.
Source: Hartshorne, Algebraic Geometry, II.2–3, principal opens and finite maps. -/
theorem s2v_l1a_principal_quotient_restriction
    (V U : Over (Spec ↧ℂ)) [IsAffine V.left] [IsAffine U.left]
    {T : Type*} (q : V ⟶ U) [IsFinite q.left]
    (ρ : T → (V ⟶ V)) (hρq : ∀ t, ρ t ≫ q = q)
    (p : ComplexPoint V) (d : Γ(U.left, ⊤))
    (hd : Point.evaluate ⊤ d (Point.map q p) ≠ 0) :
    ∃ (U' V' : Over (Spec ↧ℂ)) (hU' : IsAffine U'.left) (hV' : IsAffine V'.left)
      (u : U' ⟶ U) (v : V' ⟶ V) (q' : V' ⟶ U') (p' : ComplexPoint V')
      (σ : T → (V' ⟶ V')),
      IsOpenImmersion u.left ∧ IsOpenImmersion v.left ∧ IsFinite q'.left ∧
      v ≫ q = q' ≫ u ∧ Point.map v p' = p ∧
      (∀ t, σ t ≫ v = v ≫ ρ t) ∧ (∀ t, σ t ≫ q' = q') ∧
      (letI := u.left.appTop.hom.toAlgebra;
        IsLocalization.Away d Γ(U'.left, ⊤)) ∧
      (letI := v.left.appTop.hom.toAlgebra;
        IsLocalization.Away (q.left.appTop.hom d) Γ(V'.left, ⊤)) := by
  let O := U.left.basicOpen d
  let P := q.left ⁻¹ᵁ O
  let U' := ComplexPoint.openScheme U O
  let V' := ComplexPoint.openScheme V P
  let u : U' ⟶ U := ComplexPoint.openInclusion U O
  let v : V' ⟶ V := ComplexPoint.openInclusion V P
  let q' : V' ⟶ U' := Over.homMk (q.left ∣_ O) (by
    change (q.left ∣_ O) ≫ (O.ι ≫ U.hom) = P.ι ≫ V.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w q])
  have hmem : p.underlying ∈ P :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d (Point.map q p)
      (show Point.map q p ∈ Point.overOpen ⊤ from trivial)).mpr hd
  let p' := ComplexPoint.asOpenPoint V P p hmem
  have hpre (t : T) : P ≤ (ρ t).left ⁻¹ᵁ P := by
    change q.left ⁻¹ᵁ O ≤ (ρ t).left ⁻¹ᵁ (q.left ⁻¹ᵁ O)
    rw [← Scheme.Hom.comp_preimage]
    rw [show (ρ t).left ≫ q.left = q.left from
      congrArg (fun f : V ⟶ U => f.left) (hρq t)]
  let r (t : T) := (ρ t).left.resLE P P (hpre t)
  have hr (t : T) : r t ≫ P.ι = P.ι ≫ (ρ t).left := Scheme.Hom.resLE_comp_ι _ _
  let σ (t : T) : V' ⟶ V' := Over.homMk (r t) (by
    change r t ≫ (P.ι ≫ V.hom) = P.ι ≫ V.hom
    rw [← Category.assoc, hr, Category.assoc, Over.w])
  letI : IsAffine U'.left := (isAffineOpen_top U.left).basicOpen d
  letI : IsAffine V'.left := ((isAffineOpen_top U.left).basicOpen d).preimage q.left
  refine ⟨U', V', inferInstance, inferInstance, u, v, q', p', σ,
    inferInstanceAs (IsOpenImmersion O.ι), inferInstanceAs (IsOpenImmersion P.ι),
    inferInstanceAs (IsFinite (q.left ∣_ O)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact (morphismRestrict_ι q.left O).symm
  · apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac V P p hmem
  · intro t
    apply Over.OverMorphism.ext
    exact hr t
  · intro t
    apply Over.OverMorphism.ext
    apply (cancel_mono O.ι).mp
    change (r t ≫ (q.left ∣_ O)) ≫ O.ι = (q.left ∣_ O) ≫ O.ι
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hr, Category.assoc]
    rw [show (ρ t).left ≫ q.left = q.left from
      congrArg (fun f : V ⟶ U => f.left) (hρq t)]
  · exact s2v_l1a_openScheme_sections_localization U.left d
  · change letI := P.ι.appTop.hom.toAlgebra
      IsLocalization.Away (q.left.appTop.hom d) Γ(P.toScheme, ⊤)
    have H (Q : V.left.Opens) (hQ : Q = V.left.basicOpen (q.left.appTop.hom d)) :
        letI := Q.ι.appTop.hom.toAlgebra
        IsLocalization.Away (q.left.appTop.hom d) Γ(Q.toScheme, ⊤) := by
      subst Q
      exact s2v_l1a_openScheme_sections_localization V.left (q.left.appTop.hom d)
    exact H P (Scheme.preimage_basicOpen q.left d)

end HodgeLean.Foundations.Program
