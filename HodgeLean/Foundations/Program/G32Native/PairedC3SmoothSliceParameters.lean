import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedLocalParameters
import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.Order.Basic

/-! # Adapted parameters from a smooth slice and its smooth divisor -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.G32Native

/-- Smoothness of the actual slice and divisor supplies both quotient-ring
regularity inputs and their codimensions for the pointwise construction.
Source: Hartshorne, Algebraic Geometry, II.8 and III.10.2;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_smooth_slice_parameters
    {K : Type} [Field K] [PerfectField K]
    (X : Over (Spec (CommRingCat.of K))) (m k : ℕ) (hm : 0 < m)
    [SmoothOfRelativeDimension (m + (k + 1)) X.hom]
    (I D : X.left.IdealSheafData)
    [SmoothOfRelativeDimension m (I.subschemeι ≫ X.hom)]
    [SmoothOfRelativeDimension (m - 1) (D.subschemeι ≫ X.hom)]
    (x : X.left) (hxD : x ∈ D.support) :
    let A := X.left.presheaf.stalk x
    ∀ (u v : maximalIdeal A),
    D.stalkIdeal x = I.stalkIdeal x ⊔ Ideal.span {(u : A)} →
    LinearIndependent (ResidueField A)
      ![(maximalIdeal A).toCotangent u, (maximalIdeal A).toCotangent v] →
    ∀ (a : A), (v : A) - a * (u : A) ∈ I.stalkIdeal x →
    ∃ (t : Fin (k + 1) → A),
      t 0 = (v : A) - a * (u : A) ∧ Ideal.span (Set.range t) = I.stalkIdeal x ∧
      ∃ (n : ℕ) (z : Fin n → A) (e : Fin (k + 2) ↪ Fin n),
        IsRegularSystemOfParameters z ∧ z (e 0) = (u : A) ∧
        (∀ j, z (e j.succ) = t j) ∧
        ∃ (w : Fin n → maximalIdeal A)
          (b : Module.Basis (Fin n) (ResidueField A) (maximalIdeal A).Cotangent),
          (∀ j, (w j : A) = z j) ∧ ∀ j, b j = (maximalIdeal A).toCotangent (w j) := by
  dsimp only
  intro u v hD htrans a ht
  have hDm := (D.mem_support_iff_stalkIdeal_le_maximalIdeal x).mp hxD
  have hIm : I.stalkIdeal x ≤ maximalIdeal (X.left.presheaf.stalk x) := by
    rw [hD] at hDm
    exact le_trans le_sup_left hDm
  have hxI := (I.mem_support_iff_stalkIdeal_le_maximalIdeal x).mpr hIm
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth (m + (k + 1)) X.hom
  letI : Smooth (I.subschemeι ≫ X.hom) := SmoothOfRelativeDimension.smooth m _
  letI : Smooth (D.subschemeι ≫ X.hom) := SmoothOfRelativeDimension.smooth (m - 1) _
  letI : IsRegularLocalRing (X.left.presheaf.stalk x) := isRegularLocalRing_stalk X.hom x
  letI : IsRegularLocalRing (X.left.presheaf.stalk x ⧸ I.stalkIdeal x) :=
    isRegularLocalRing_quotient_stalkIdeal I X.hom hxI
  letI : IsRegularLocalRing (X.left.presheaf.stalk x ⧸
      (I.stalkIdeal x ⊔ Ideal.span {(u : X.left.presheaf.stalk x)})) := by
    rw [← hD]
    exact isRegularLocalRing_quotient_stalkIdeal D X.hom hxD
  have hcodim : ringKrullDim (X.left.presheaf.stalk x ⧸ I.stalkIdeal x) + (k + 1) =
      ringKrullDim (X.left.presheaf.stalk x) := by
    letI : SmoothOfRelativeDimension ((m + (k + 1)) - (k + 1))
        (I.subschemeι ≫ X.hom) := by simpa only [Nat.add_sub_cancel] using
      (inferInstance : SmoothOfRelativeDimension m (I.subschemeι ≫ X.hom))
    exact ringKrullDim_quotient_stalkIdeal_add I X.hom (m + (k + 1)) (k + 1) (by omega) hxI
  have hsection : ringKrullDim (X.left.presheaf.stalk x ⧸
      (I.stalkIdeal x ⊔ Ideal.span {(u : X.left.presheaf.stalk x)})) + (k + 2) =
      ringKrullDim (X.left.presheaf.stalk x) := by
    rw [← hD]
    letI : SmoothOfRelativeDimension ((m + (k + 1)) - (k + 2))
        (D.subschemeι ≫ X.hom) := by
      have he : (m + (k + 1)) - (k + 2) = m - 1 := by omega
      rw [he]
      infer_instance
    exact ringKrullDim_quotient_stalkIdeal_add D X.hom (m + (k + 1)) (k + 2) (by omega) hxD
  exact paired_c3_adapted_local_parameters (I.stalkIdeal x) hIm k hcodim
    u v htrans a ht hsection

#print axioms paired_c3_smooth_slice_parameters
end HodgeLean.Foundations.Program.G32Native
