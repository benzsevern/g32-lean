import HodgeLean.Foundations.Program.SchoenCycleIdealStalkCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Detection of ideal sections at closed points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- On a Jacobson scheme, containment of affine ideals is detected at closed point stalks.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Hartshorne, Algebraic Geometry, II.5. -/
theorem s2e_affine_ideal_le_of_closed_stalks
    {X : Scheme} [JacobsonSpace X] (U : X.affineOpens)
    (I J : Ideal Γ(X, U.1))
    (h : ∀ (x : X) (hx : x ∈ U.1), IsClosed ({x} : Set X) →
      Ideal.map (X.presheaf.germ U.1 x hx).hom I ≤
        Ideal.map (X.presheaf.germ U.1 x hx).hom J) : I ≤ J := by
  let (x : PrimeSpectrum Γ(X, U.1)) : Algebra Γ(X, U.1) (X.presheaf.stalk (U.2.fromSpec x)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U.1)) [hP : P.IsPrime] : IsLocalization.AtPrime _ P :=
    U.2.isLocalization_stalk' ⟨P, hP⟩ (U.2.isoSpec.inv _).2
  intro s hs
  refine Submodule.mem_of_localization_maximal
    (fun P hP => X.presheaf.stalk (U.2.fromSpec ⟨P, hP.isPrime⟩))
    (fun P hP => Algebra.linearMap _ _) s J ?_
  intro P hP
  rw [Ideal.localized₀_eq_restrictScalars_map]
  have hc : IsClosed ({U.2.fromSpec ⟨P, hP.isPrime⟩} : Set X) :=
    U.2.fromSpec.closedPoints_subset_preimage_closedPoints
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hP)
  exact h _ _ hc (Ideal.mem_map_of_mem _ hs)

end HodgeLean.Foundations.Program
