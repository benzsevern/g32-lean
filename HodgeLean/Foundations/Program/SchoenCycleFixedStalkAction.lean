import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets
import HodgeLean.Foundations.AlgebraicGeometry.Scheme.FixedPointStalk

/-! # Pullback on the stalk at a fixed scheme point -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Germs commute with transport between equal scheme points.
Source: Hartshorne, Algebraic Geometry, II.1, stalks of sheaves. -/
theorem s2e_germ_stalk_transport (X : Scheme) (U : X.Opens)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y) :
    X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
      X.presheaf.germ U y hy := by
  exact (Scheme.FixedPointStalk.germ_transport X).1 U x y hx hy h

/-- Pullback of sections induces the transported stalk map at a fixed point.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms of locally ringed spaces. -/
theorem s2e_fixed_point_germ_pullback (X : Scheme) (f : X ⟶ X)
    (p : X) (hp : f p = p) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U)
    (hmem : p ∈ U) :
    X.presheaf.germ U p hmem ≫
        (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p =
      f.appLE U U hU ≫ X.presheaf.germ U p hmem := by
  exact (Scheme.FixedPointStalk.germ_transport X).2 f p hp U hU hmem

/-- The stalk pullback transported to a fixed point.
Source: Hartshorne, Algebraic Geometry, II.2, morphisms of locally ringed spaces. -/
def s2e_fixed_point_stalkPullback (X : Scheme) (f : X ⟶ X)
    (p : X) (hp : f p = p) :
    X.presheaf.stalk p →+* X.presheaf.stalk p :=
  Scheme.FixedPointStalk.pullback X f p hp

/-- Fixed-point stalk pullback preserves every finite infinitesimal ideal.
Source: Hartshorne, Algebraic Geometry, II.2, local ring maps. -/
theorem s2e_fixed_point_stalkPullback_power (X : Scheme) (f : X ⟶ X)
    (p : X) (hp : f p = p) (N : ℕ) (r : X.presheaf.stalk p)
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N) :
    s2e_fixed_point_stalkPullback X f p hp r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N := by
  exact Scheme.FixedPointStalk.pullback_power X f p hp N r hr

/-- Every section representative of an invariant finite stalk jet remains
invariant to the same order under pullback.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5, stalks and localization. -/
theorem s2e_fixed_point_section_jet_invariant (X : Scheme) (f : X ⟶ X)
    (p : X) (hp : f p = p) (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U)
    (hmem : p ∈ U) (N : ℕ) (r : X.presheaf.stalk p)
    (hr : s2e_fixed_point_stalkPullback X f p hp r - r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N)
    (b : Γ(X, U))
    (hb : (X.presheaf.germ U p hmem).hom b - r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N) :
    (X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom b - b) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ N := by
  exact Scheme.FixedPointStalk.section_jet_invariant X f p hp U hU hmem N r hr b hb

end HodgeLean.Foundations.Program
