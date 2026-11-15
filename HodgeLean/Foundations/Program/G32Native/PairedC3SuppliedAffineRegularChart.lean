import HodgeLean.Foundations.Program.G32Native.PairedC3AffineRegularChart
import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedChartGenerators
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections

/-! # Regular spectrum charts for the actual total-transform ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- Adapted coordinates on an ambient affine open and a supplied affine
Rees chart give the required spectrum chart for the actual pulled-back ideal.
Source: Hartshorne, Algebraic Geometry, II.5, II.7.13 and II.8. -/
theorem paired_c3_supplied_affine_regular_chart
    {X Y : Scheme.{0}} (p : Y ⟶ X) (I : X.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ p ⁻¹ᵁ U.1)
    (y : Y) (hy : y ∈ V.1)
    {K σ : Type} [CommRing K] [DecidableEq σ]
    [Algebra (MvPolynomial σ K) Γ(X, U.1)]
    [Algebra.Etale (MvPolynomial σ K) Γ(X, U.1)]
    (u v c : Γ(X, U.1)) (s : Γ(Y, V.1))
    (hsurj : Function.Surjective (eval₂RingHom (p.appLE U.1 V.1 hVU).hom s))
    (hker : RingHom.ker (eval₂RingHom (p.appLE U.1 V.1 hVU).hom s) =
      Ideal.span {C u - Polynomial.X * C v})
    {n : ℕ} (e : Fin (n + 2) ↪ σ)
    (hu : u - c * v = algebraMap (MvPolynomial σ K) Γ(X, U.1)
      (MvPolynomial.X (e (0 : Fin (n + 1)).succ)))
    (hv : v = algebraMap (MvPolynomial σ K) Γ(X, U.1) (MvPolynomial.X (e 0)))
    (hI : I.ideal U = Ideal.span (Set.range (fun j : Fin (n + 1) =>
      algebraMap (MvPolynomial σ K) Γ(X, U.1) (MvPolynomial.X (e j.succ))))) :
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ Y) (_ : IsOpenImmersion j),
      y ∈ j.opensRange ∧
      ∃ f : Fin (n + 1) → A, IsWeaklyRegular A (List.ofFn f) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          (((I.comap p).comap j).ideal ⟨⊤, isAffineOpen_top _⟩) =
          Ideal.span (Set.range f) := by
  obtain ⟨f, hreg, hgen⟩ := paired_c3_adapted_chart_generators
    (p.appLE U.1 V.1 hVU).hom u v c s hsurj hker e hu hv (I.ideal U) hI
  apply paired_c3_affine_regular_chart (I.comap p) V y hy f hreg
  rw [HodgeLean.Foundations.Program.s2e_c1_affine_comap_appLE p I U V hVU]
  exact hgen

#print axioms paired_c3_supplied_affine_regular_chart
end HodgeLean.Foundations.Program.G32Native
