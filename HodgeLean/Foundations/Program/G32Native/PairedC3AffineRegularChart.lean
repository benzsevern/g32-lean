import HodgeLean.Foundations.Program.SchoenCycleC1FromSpecCentreTransport
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Regular affine equations as spectrum charts of the same ideal -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- An actual affine open with regular ideal generators supplies the
spectrum chart with the same generators under its canonical section map.
Source: Hartshorne, Algebraic Geometry, II.2, II.5 and II.8. -/
theorem paired_c3_affine_regular_chart
    {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) {k : ℕ} (f : Fin k → Γ(X, U.1))
    (hreg : IsWeaklyRegular Γ(X, U.1) (List.ofFn f))
    (hI : I.ideal U = Ideal.span (Set.range f)) :
    ∃ (A : CommRingCat.{0}) (j : Spec A ⟶ X) (_ : IsOpenImmersion j),
      x ∈ j.opensRange ∧
      ∃ g : Fin k → A, IsWeaklyRegular A (List.ofFn g) ∧
        Ideal.map (Scheme.ΓSpecIso A).hom.hom
          ((I.comap j).ideal ⟨⊤, isAffineOpen_top _⟩) = Ideal.span (Set.range g) := by
  refine ⟨Γ(X, U.1), U.2.fromSpec, U.2.isOpenImmersion_fromSpec, ?_, f, hreg, ?_⟩
  · rwa [U.2.opensRange_fromSpec]
  · rw [HodgeLean.Foundations.Program.s2e_c1_fromSpec_centre_transport,
      Scheme.IdealSheafData.ofIdealTop_ideal]
    simp only [homOfLE_refl, op_id]
    rw [CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
    rw [Ideal.map_map]
    simpa only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
      Ideal.map_id] using hI

#print axioms paired_c3_affine_regular_chart
end HodgeLean.Foundations.Program.G32Native
