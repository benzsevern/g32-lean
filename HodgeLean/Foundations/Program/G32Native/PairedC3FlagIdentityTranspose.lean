import HodgeLean.Foundations.Program.G32Native.UnionConormalGlobalExact

/-! # Removing identity pullbacks and pushforwards from the flag -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Transposition along the identity agrees with the canonical identity
pullback and pushforward identifications. -/
theorem paired_c3_identity_pullback_transpose {Q : Scheme.{0}} {M N : Q.Modules}
    (a : (Scheme.Modules.pullback (𝟙 Q)).obj M ⟶ N) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Q)).homEquiv _ _ a) ≫
        (Scheme.Modules.pushforwardId Q).hom.app N =
      (Scheme.Modules.pullbackId Q).inv.app M ≫ a := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Q)
  let eL := Scheme.Modules.pullbackId Q
  let eR := Scheme.Modules.pushforwardId Q
  have hu := unit_conjugateEquiv (Adjunction.id : 𝟭 Q.Modules ⊣ 𝟭 Q.Modules) adj eL.hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at hu
  change eR.inv.app M = adj.unit.app M ≫ (Scheme.Modules.pushforward (𝟙 Q)).map
    (eL.hom.app M) at hu
  have hx : adj.unit.app M ≫ eR.hom.app ((Scheme.Modules.pullback (𝟙 Q)).obj M) =
      eL.inv.app M := by
    apply (cancel_mono (eL.hom.app M)).mp
    rw [Iso.inv_hom_id_app]
    calc
      _ = adj.unit.app M ≫ ((Scheme.Modules.pushforward (𝟙 Q)).map (eL.hom.app M) ≫
          eR.hom.app M) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => adj.unit.app M ≫ t)
            (eR.hom.naturality (eL.hom.app M)).symm)
      _ = (adj.unit.app M ≫ (Scheme.Modules.pushforward (𝟙 Q)).map (eL.hom.app M)) ≫
          eR.hom.app M := (Category.assoc _ _ _).symm
      _ = eR.inv.app M ≫ eR.hom.app M := by rw [← hu]
      _ = 𝟙 _ := Iso.inv_hom_id_app eR M
  rw [Adjunction.homEquiv_unit, Category.assoc, eR.hom.naturality,
    ← Category.assoc, hx]
  rfl

#print axioms paired_c3_identity_pullback_transpose
end HodgeLean.Foundations.Program.G32Native
