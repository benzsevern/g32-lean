import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport
import HodgeLean.Foundations.Program.G32Native.PairedResidualFreeRestriction

/-! # Restricting the last total-transform conormal to its retained component -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An invertible natural conormal comparison and the penultimate frame
supply the free source on the retained component. No flatness of the
ambient blowup is required by this transport.
Source: Hartshorne, Algebraic Geometry, II.8, conormal pullback;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7.
This transports an existing comparison; it does not assert its invertibility
for an arbitrary base change. -/
def paired_last_conormal_source_iso
    {P Q T V X : Scheme.{0}}
    (i₀ : Q ⟶ X) (t : T ⟶ V) (σ : V ⟶ X) (p : T ⟶ Q)
    (h : p ≫ i₀ = t ≫ σ)
    [IsIso (Conormal.comparisonMap i₀ t σ p h)]
    (a : P ⟶ T) (k : ℕ)
    (e₀ : s2c_conormal i₀ ≅
      (SheafOfModules.free (R := Q.ringCatSheaf) (Fin k) : Q.Modules)) :
    (Scheme.Modules.pullback a).obj (s2c_conormal t) ≅
      (SheafOfModules.free (R := P.ringCatSheaf) (Fin k) : P.Modules) := by
  letI : (SheafOfModules.pushforward.{0} (a ≫ p).toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward (a ≫ p)).IsRightAdjoint
  exact (Scheme.Modules.pullback a).mapIso
      (asIso (Conormal.comparisonMap i₀ t σ p h)).symm ≪≫
    (Scheme.Modules.pullbackComp a p).app (s2c_conormal i₀) ≪≫
    (Scheme.Modules.pullback (a ≫ p)).mapIso e₀ ≪≫
    SheafOfModules.pullbackObjFreeIso (a ≫ p).toRingCatSheafHom (Fin k)

#print axioms paired_last_conormal_source_iso

end HodgeLean.Foundations.Program.G32Native
