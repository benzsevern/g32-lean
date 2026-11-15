import HodgeLean.Foundations.Program.SchoenCycleProjectiveReducedIdeals
import HodgeLean.Foundations.Program.SchoenCycleC1OpenCentreSections

/-! # Reduced total transforms on open isomorphism regions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Pulling back the ideal of a reduced closed slice along an open
immersion retains its reduced scheme structure.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5. -/
theorem paired_c3_open_pullback_reduced
    {Q X Y : Scheme.{0}} [IsReduced Q]
    (i : Q ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y) [IsOpenImmersion f] :
    (i.ker.comap f).radical = i.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f]
  letI : IsReduced (pullback f i) := isReduced_of_isOpenImmersion (pullback.snd f i)
  exact s2e_kernel_radical_of_reduced (pullback.fst f i)

#print axioms paired_c3_open_pullback_reduced
/-- Reducedness of the restricted ideal transfers back to its original
affine section ideal through the canonical top-section isomorphism.
Source: Hartshorne, Algebraic Geometry, II.5. -/
theorem paired_c3_affine_sections_radical
    {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (hred : (I.comap V.1.ι).radical = I.comap V.1.ι) :
    (I.ideal V).IsRadical := by
  apply Ideal.radical_eq_iff.mp
  have hJ := congrArg (fun J : V.1.toScheme.IdealSheafData =>
    J.ideal ⟨⊤, isAffineOpen_top _⟩) hred
  rw [Scheme.IdealSheafData.radical_ideal] at hJ
  have hker : RingHom.ker V.1.topIso.hom.hom ≤
      (I.comap V.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ := by
    intro a ha
    have hz : a = 0 := V.1.topIso.commRingCatIsoToRingEquiv.injective
      (show V.1.topIso.hom.hom a = V.1.topIso.hom.hom 0 from ha.trans (map_zero _).symm)
    rw [hz]
    exact Ideal.zero_mem _
  rw [← s2e_c1_open_centre_sections X I V,
    ← Ideal.map_radical_of_surjective V.1.topIso.commRingCatIsoToRingEquiv.surjective hker,
    hJ]

#print axioms paired_c3_affine_sections_radical
end HodgeLean.Foundations.Program.G32Native
