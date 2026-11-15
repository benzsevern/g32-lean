import HodgeLean.Foundations.Program.G32Native.PairedC3PointwiseEquationsInside
import HodgeLean.Foundations.Program.G32Native.PairedC3SmoothSliceParameters

/-! # Smooth slice equations retaining the original affine sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- A smooth slice and its smooth divisor supply adapted affine equations
inside an existing chart, with the two specified sections retained exactly.
Source: Hartshorne, Algebraic Geometry, II.5, II.8 and III.10.2;
EGA IV, 17.11.1; Atiyah–Macdonald, Proposition 2.8. -/
theorem paired_c3_smooth_equations_inside
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (m k : ℕ) (hm : 0 < m)
    [SmoothOfRelativeDimension (m + (k + 1)) X.hom]
    (I D : X.left.IdealSheafData)
    [SmoothOfRelativeDimension m (I.subschemeι ≫ X.hom)]
    [SmoothOfRelativeDimension (m - 1) (D.subschemeι ≫ X.hom)]
    (x : ComplexPoint X) (hxD : x.underlying ∈ D.support) :
    let A := X.left.presheaf.stalk x.underlying
    ∀ (u v : maximalIdeal A),
    D.stalkIdeal x.underlying = I.stalkIdeal x.underlying ⊔ Ideal.span {(u : A)} →
    LinearIndependent (ResidueField A)
      ![(maximalIdeal A).toCotangent u, (maximalIdeal A).toCotangent v] →
    ∀ (a : A), (v : A) - a * (u : A) ∈ I.stalkIdeal x.underlying →
    ∀ (V : X.left.affineOpens) (hxV : x.underlying ∈ V.1)
      (d q : Γ(X.left, V.1)),
    (X.left.presheaf.germ V.1 x.underlying hxV).hom d = u →
    (X.left.presheaf.germ V.1 x.underlying hxV).hom q = (v : A) - a * (u : A) →
    ∃ (U : X.left.affineOpens) (hUV : U ≤ V) (hxU : x.underlying ∈ U.1),
      letI := HodgeLean.Foundations.Program.s2e_step1_sectionAlgebra X U.1
      ∃ (F : MvPolynomial (Fin (m + (k + 1))) ℂ →ₐ[ℂ] Γ(X.left, U.1))
        (e : Fin (k + 2) ↪ Fin (m + (k + 1))),
        F.toRingHom.Etale ∧
        I.ideal U = Ideal.span (Set.range (fun j : Fin (k + 1) =>
          F (MvPolynomial.X (e j.succ)))) ∧
        (X.left.presheaf.map (homOfLE hUV).op).hom d = F (MvPolynomial.X (e 0)) ∧
        (X.left.presheaf.map (homOfLE hUV).op).hom q =
          F (MvPolynomial.X (e (0 : Fin (k + 1)).succ)) := by
  dsimp only
  intro u v hD htrans a ht V hxV d q hd hq
  have hDm := (D.mem_support_iff_stalkIdeal_le_maximalIdeal x.underlying).mp hxD
  have hIm : I.stalkIdeal x.underlying ≤ maximalIdeal _ := by
    rw [hD] at hDm
    exact le_trans le_sup_left hDm
  have hxI := (I.mem_support_iff_stalkIdeal_le_maximalIdeal x.underlying).mpr hIm
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth (m + (k + 1)) X.hom
  letI : Smooth (I.subschemeι ≫ X.hom) := SmoothOfRelativeDimension.smooth m _
  letI : Smooth (D.subschemeι ≫ X.hom) := SmoothOfRelativeDimension.smooth (m - 1) _
  letI : IsRegularLocalRing (X.left.presheaf.stalk x.underlying) :=
    isRegularLocalRing_stalk X.hom x.underlying
  letI : IsRegularLocalRing (X.left.presheaf.stalk x.underlying ⧸ I.stalkIdeal x.underlying) :=
    isRegularLocalRing_quotient_stalkIdeal I X.hom hxI
  letI : IsRegularLocalRing (X.left.presheaf.stalk x.underlying ⧸
      (I.stalkIdeal x.underlying ⊔ Ideal.span {(u : X.left.presheaf.stalk x.underlying)})) := by
    rw [← hD]
    exact isRegularLocalRing_quotient_stalkIdeal D X.hom hxD
  have hclosed : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2
  have hdim := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed
    X.hom (m + (k + 1)) hclosed
  have hcodim : ringKrullDim (X.left.presheaf.stalk x.underlying ⧸ I.stalkIdeal x.underlying) + (k + 1) =
      ringKrullDim (X.left.presheaf.stalk x.underlying) := by
    letI : SmoothOfRelativeDimension ((m + (k + 1)) - (k + 1))
        (I.subschemeι ≫ X.hom) := by simpa only [Nat.add_sub_cancel] using
      (inferInstance : SmoothOfRelativeDimension m (I.subschemeι ≫ X.hom))
    exact ringKrullDim_quotient_stalkIdeal_add I X.hom (m + (k + 1)) (k + 1) (by omega) hxI
  have hsection : ringKrullDim (X.left.presheaf.stalk x.underlying ⧸
      (I.stalkIdeal x.underlying ⊔ Ideal.span {(u : X.left.presheaf.stalk x.underlying)})) + (k + 2) =
      ringKrullDim (X.left.presheaf.stalk x.underlying) := by
    rw [← hD]
    letI : SmoothOfRelativeDimension ((m + (k + 1)) - (k + 2))
        (D.subschemeι ≫ X.hom) := by
      have he : (m + (k + 1)) - (k + 2) = m - 1 := by omega
      rw [he]
      infer_instance
    exact ringKrullDim_quotient_stalkIdeal_add D X.hom (m + (k + 1)) (k + 2) (by omega) hxD
  exact paired_c3_pointwise_etale_equations_inside X (m + (k + 1)) I x hIm hdim
    k hcodim u v htrans a ht hsection V hxV d q hd hq

#print axioms paired_c3_smooth_equations_inside
end HodgeLean.Foundations.Program.G32Native
