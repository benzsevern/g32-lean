import HodgeLean.Foundations.RationalHomologyManifold.KernelPrismCap
import HodgeLean.Foundations.RationalHomologyManifold.FixedCapPresheaf
import HodgeLean.Foundations.RationalHomologyManifold.AmbientKernelDifferential
import HodgeLean.Foundations.RationalHomologyManifold.SheafCapVanishing
import HodgeLean.Foundations.RationalHomologyManifold.SheafPrismCapIdentity

/-! The stabilized prism-cap homotopy identity as an actual presheaf morphism.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Fixed-cycle cap on the actual ambient cochain kernel is the signed sum of the two stabilized prism-cap morphisms.
Source: Bredon, Sheaf Theory, second edition, VI.12; the local subdivision homotopy for the actual cap construction.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapPresheaf_identity (X : TopCat.{0}) [RegularSpace X] (p q : ℕ)
    (z : (SingularChainComplex ℚ X).X (p + q))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (p + q) j z = 0) :
    (kernel.ι (ambientCochainPresheafComplexRestriction X)).f p ≫ ambientFixedCapPresheafMap X p q z =
      -((ambientLocalZeroPresheafComplex X).d p (p + 1) ≫
        kernelPrismCapPresheafLimit X (p + q) (p + 1) q z) -
      (-1 : ℤ) ^ p • (kernelPrismCapPresheafLimit X (p + q) p (q + 1) z ≫
        ((subdivisionLimitSheafComplex X).d (q + 1) q).hom) := by
  apply NatTrans.ext
  funext U
  ext b
  change ((ambientLocalZeroPresheafComplex X).X p).obj U at b
  let φ : Cochain ℚ (TopCat.toSSet.obj X) p :=
    (((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p).app U) b
  let bδ := ((ambientLocalZeroPresheafComplex X).d p (p + 1)).app U b
  let F := (subdivisionLimitSheafComplex X).X q
  let G := (subdivisionLimitSheafComplex X).X (q + 1)
  let d := ((subdivisionLimitSheafComplex X).d (q + 1) q).hom
  change subdivisionAmbientSectionMap X q U.unop 0 (cap ℚ p q φ z) =
    -(kernelPrismCapPresheafLimit X (p + q) (p + 1) q z).app U bδ -
      (-1 : ℤ) ^ p • d.app U ((kernelPrismCapPresheafLimit X (p + q) p (q + 1) z).app U b)
  apply TopCat.Presheaf.section_ext F
  intro x hx
  have hφ := ambientLocalZeroPresheaf_restriction_zero X p U.unop b
  change cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) (U.unop : Set X)).map) p φ = 0 at hφ
  obtain ⟨m₀, hm₀⟩ := subdivisionAmbientSection_cap_germ_eventually_zero X x U.unop hx p q φ hφ z
  obtain ⟨m₁, hm₁⟩ := locallyStationaryPresheafMap_germ_eventually _ G
    (kernelPrismCapPresheafMap X (p + q) p (q + 1) z)
    (kernelPrismCapPresheafMap_locally_stationary X (p + q) p (q + 1) z) U.unop b ⟨x, hx⟩
  obtain ⟨m₂, hm₂⟩ := locallyStationaryPresheafMap_germ_eventually _ F
    (kernelPrismCapPresheafMap X (p + q) (p + 1) q z)
    (kernelPrismCapPresheafMap_locally_stationary X (p + q) (p + 1) q z) U.unop bδ ⟨x, hx⟩
  let m := m₀ + m₁ + m₂
  have h₀ := hm₀ (m₁ + m₂)
  have h₁ := hm₁ (m₀ + m₂)
  have h₂ := hm₂ (m₀ + m₁)
  rw [show m₀ + (m₁ + m₂) = m by omega] at h₀
  rw [show m₁ + (m₀ + m₂) = m by omega] at h₁
  rw [show m₂ + (m₀ + m₁) = m by omega] at h₂
  have hδ := kernelPrismCapPresheafMap_apply X (p + q) (p + 1) q z m U.unop bδ
  rw [ambientLocalZeroPresheaf_coboundary X p U.unop b] at hδ
  have h := congrArg (F.presheaf.germ U.unop x hx)
    (subdivisionAmbientSection_cap_prism_identity X p q m U.unop φ z hz)
  simp only [map_sub, map_zsmul] at h
  rw [h₀, zero_sub, ← hδ] at h
  have h₁' := congrArg ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map d) h₁
  have hn (s : G.obj.obj U) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map d (G.presheaf.germ U.unop x hx s) =
        F.presheaf.germ U.unop x hx (d.app U s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hx d s
  have hh₁ := (hn _).symm.trans (h₁'.trans (hn _))
  rw [kernelPrismCapPresheafMap_apply] at hh₁
  change F.presheaf.germ U.unop x hx ((kernelPrismCapPresheafLimit X (p + q) (p + 1) q z).app U bδ) = _ at h₂
  simp only [map_sub, map_neg, map_zsmul]
  exact h.trans (congrArg₂ (fun a c => -a - (-1 : ℤ) ^ p • c) h₂.symm hh₁.symm)

#print axioms kernelPrismCapPresheaf_identity
end HodgeLean.Foundations.RationalHomologyManifold
