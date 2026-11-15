import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedLocalParameters
import HodgeLean.Foundations.Program.G32Native.PairedC3EtaleEquationsInside

/-! # Adapted equations retaining the original affine branch sections -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- The pointwise Nakayama construction supplies actual affine étale slice
equations inside a prescribed affine neighbourhood. The original branch
section and branch difference agree with the coordinates as sections.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; EGA IV, 17.11.1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_pointwise_etale_equations_inside
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] (n : ℕ)
    [SmoothOfRelativeDimension n X.hom] (I : X.left.IdealSheafData)
    (x : ComplexPoint X) :
    let A := X.left.presheaf.stalk x.underlying
    let J := I.stalkIdeal x.underlying
    ∀ [IsRegularLocalRing A] [IsRegularLocalRing (A ⧸ J)],
    J ≤ maximalIdeal A → ringKrullDim A = n →
    ∀ (k : ℕ), ringKrullDim (A ⧸ J) + (k + 1) = ringKrullDim A →
    ∀ (u v : maximalIdeal A),
    LinearIndependent (ResidueField A)
      ![(maximalIdeal A).toCotangent u, (maximalIdeal A).toCotangent v] →
    ∀ (a : A), (v : A) - a * (u : A) ∈ J →
    ∀ [IsRegularLocalRing (A ⧸ (J ⊔ Ideal.span {(u : A)}))],
    ringKrullDim (A ⧸ (J ⊔ Ideal.span {(u : A)})) + (k + 2) = ringKrullDim A →
    ∀ (V : X.left.affineOpens) (hxV : x.underlying ∈ V.1)
      (d q : Γ(X.left, V.1)),
    (X.left.presheaf.germ V.1 x.underlying hxV).hom d = u →
    (X.left.presheaf.germ V.1 x.underlying hxV).hom q = (v : A) - a * (u : A) →
    ∃ (U : X.left.affineOpens) (hUV : U ≤ V) (hxU : x.underlying ∈ U.1),
      letI := HodgeLean.Foundations.Program.s2e_step1_sectionAlgebra X U.1
      ∃ (F : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.left, U.1))
        (e : Fin (k + 2) ↪ Fin n),
        F.toRingHom.Etale ∧
        I.ideal U = Ideal.span (Set.range (fun j : Fin (k + 1) =>
          F (MvPolynomial.X (e j.succ)))) ∧
        (X.left.presheaf.map (homOfLE hUV).op).hom d = F (MvPolynomial.X (e 0)) ∧
        (X.left.presheaf.map (homOfLE hUV).op).hom q =
          F (MvPolynomial.X (e (0 : Fin (k + 1)).succ)) := by
  dsimp only
  intro hA hJ hJm hdim k hcodim u v htrans a ht hD hsection V hxV d q hd hq
  obtain ⟨t, ht0, htgen, m, z, e, hz, hu, hzt, w, b, hw, hb⟩ :=
    paired_c3_adapted_local_parameters (I.stalkIdeal x.underlying) hJm k hcodim
      u v htrans a ht hsection
  have hmn : m = n := by
    have h := hz.2
    rw [hdim] at h
    exact_mod_cast h
  subst m
  have hc (j : Fin n) : z j ∈ maximalIdeal (X.left.presheaf.stalk x.underlying) := by
    rw [← hw j]
    exact (w j).property
  have hb' (j : Fin n) : b j =
      (maximalIdeal (X.left.presheaf.stalk x.underlying)).toCotangent ⟨z j, hc j⟩ := by
    rw [hb j]
    congr 1
    exact Subtype.ext (hw j)
  have hgen : I.stalkIdeal x.underlying =
      Ideal.span (Set.range (z ∘ fun j : Fin (k + 1) => e j.succ)) := by
    rw [← htgen]
    congr 1
    exact congrArg Set.range (funext fun j => (hzt j).symm)
  obtain ⟨U, hUV, hxU, F, hF, hI, hg, heq⟩ :=
    paired_c3_etale_equations_inside X n I x V hxV z hc b hb' (k + 1)
      (fun j => e j.succ) hgen
  exact ⟨U, hUV, hxU, F, e, hF, hI,
    heq (e 0) d (hd.trans hu.symm),
    heq (e (0 : Fin (k + 1)).succ) q (hq.trans ((hzt 0).trans ht0).symm)⟩

#print axioms paired_c3_pointwise_etale_equations_inside
end HodgeLean.Foundations.Program.G32Native
