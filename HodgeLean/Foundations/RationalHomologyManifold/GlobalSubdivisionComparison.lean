import HodgeLean.Foundations.RationalHomologyManifold.GlobalSubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.AmbientPresheafSubdivisionSections

/-! Canonical global comparison of the actual supported subdivision presheaf and sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Sheafifying an actual ambient presheaf section gives its actual ambient subdivision sheaf section.
Source: Bredon, Sheaf Theory, second edition, VI.12; the canonical supported-chain sheafification map.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientPresheafSectionMap_sheafify (X : TopCat.{0}) (n : ℕ)
    (U : Opens X) (m : ℕ) :
    subdivisionAmbientPresheafSectionMap X n U m ≫
      ((toSheafify (Opens.grothendieckTopology X)
        ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op U)) =
    subdivisionAmbientSectionMap X n U m := by
  unfold subdivisionAmbientPresheafSectionMap subdivisionAmbientSectionMap
  exact Category.assoc _ _ _

#print axioms subdivisionAmbientPresheafSectionMap_sheafify
/-- Global actual sheaf equality of two ambient representatives already gives equality in the supported presheaf subdivision limit.
Source: Bredon, Sheaf Theory, second edition, VI.12; finite subdivision witnesses of global equality.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientPresheafSection_global_eq_of_sheaf_eq (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n m : ℕ) (z w : (SingularChainComplex ℚ X).X n)
    (h : (subdivisionAmbientSectionMap X n ⊤ m).hom z =
      (subdivisionAmbientSectionMap X n ⊤ m).hom w) :
    (subdivisionAmbientPresheafSectionMap X n ⊤ m).hom z =
      (subdivisionAmbientPresheafSectionMap X n ⊤ m).hom w := by
  obtain ⟨R, he⟩ := subdivisionAmbientSection_global_eq_eventually X n m z w h
  have hz := ConcreteCategory.congr_hom
    (subdivisionAmbientPresheafSectionMap_transition X n ⊤ m R) z
  have hw := ConcreteCategory.congr_hom
    (subdivisionAmbientPresheafSectionMap_transition X n ⊤ m R) w
  change (subdivisionAmbientPresheafSectionMap X n ⊤ (m + R)).hom
      ((rationalSubdivisionIterate X R).f n z) =
    (subdivisionAmbientPresheafSectionMap X n ⊤ m).hom z at hz
  change (subdivisionAmbientPresheafSectionMap X n ⊤ (m + R)).hom
      ((rationalSubdivisionIterate X R).f n w) =
    (subdivisionAmbientPresheafSectionMap X n ⊤ m).hom w at hw
  exact hz.symm.trans ((congrArg (subdivisionAmbientPresheafSectionMap X n ⊤ (m + R)).hom he).trans hw)

#print axioms subdivisionAmbientPresheafSection_global_eq_of_sheaf_eq
/-- The canonical supported subdivision-limit sheafification map is surjective on actual global sections.
Source: Bredon, Sheaf Theory, second edition, VI.12; global finite-chain representatives on compact spaces.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimit_global_sheafification_surjective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤)) := by
  intro s
  obtain ⟨M, w, hw⟩ := subdivisionLimitSheaf_global_ambient_rep X n s
  refine ⟨(subdivisionAmbientPresheafSectionMap X n ⊤ M).hom w, ?_⟩
  have h := ConcreteCategory.congr_hom (subdivisionAmbientPresheafSectionMap_sheafify X n ⊤ M) w
  change ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤))
      ((subdivisionAmbientPresheafSectionMap X n ⊤ M).hom w) =
    (subdivisionAmbientSectionMap X n ⊤ M).hom w at h
  exact h.trans hw

#print axioms subdivisionLimit_global_sheafification_surjective
/-- The canonical supported subdivision-limit sheafification map is injective on actual global sections.
Source: Bredon, Sheaf Theory, second edition, VI.12; compact finite-stage detection of global equality.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimit_global_sheafification_injective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ) :
    Function.Injective ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤)) := by
  intro a b hab
  obtain ⟨ma, z, ha⟩ := subdivisionLimitPresheaf_ambient_section_exists X n ⊤ a
  obtain ⟨mb, w, hb⟩ := subdivisionLimitPresheaf_ambient_section_exists X n ⊤ b
  let z' := (rationalSubdivisionIterate X mb).f n z
  let w' := (rationalSubdivisionIterate X ma).f n w
  have ha' : (subdivisionAmbientPresheafSectionMap X n ⊤ (ma + mb)).hom z' = a := by
    have ht := ConcreteCategory.congr_hom
      (subdivisionAmbientPresheafSectionMap_transition X n ⊤ ma mb) z
    change (subdivisionAmbientPresheafSectionMap X n ⊤ (ma + mb)).hom z' =
      (subdivisionAmbientPresheafSectionMap X n ⊤ ma).hom z at ht
    exact ht.trans ha
  have hb' : (subdivisionAmbientPresheafSectionMap X n ⊤ (ma + mb)).hom w' = b := by
    have ht := ConcreteCategory.congr_hom
      (subdivisionAmbientPresheafSectionMap_transition X n ⊤ mb ma) w
    change (subdivisionAmbientPresheafSectionMap X n ⊤ (mb + ma)).hom w' =
      (subdivisionAmbientPresheafSectionMap X n ⊤ mb).hom w at ht
    rw [Nat.add_comm mb ma] at ht
    exact ht.trans hb
  have haz := ConcreteCategory.congr_hom
    (subdivisionAmbientPresheafSectionMap_sheafify X n ⊤ (ma + mb)) z'
  have hbw := ConcreteCategory.congr_hom
    (subdivisionAmbientPresheafSectionMap_sheafify X n ⊤ (ma + mb)) w'
  change ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤))
      ((subdivisionAmbientPresheafSectionMap X n ⊤ (ma + mb)).hom z') =
    (subdivisionAmbientSectionMap X n ⊤ (ma + mb)).hom z' at haz
  change ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤))
      ((subdivisionAmbientPresheafSectionMap X n ⊤ (ma + mb)).hom w') =
    (subdivisionAmbientSectionMap X n ⊤ (ma + mb)).hom w' at hbw
  rw [ha'] at haz
  rw [hb'] at hbw
  have he := subdivisionAmbientPresheafSection_global_eq_of_sheaf_eq X n (ma + mb) z' w'
    (haz.symm.trans (hab.trans hbw))
  exact ha'.symm.trans (he.trans hb')

#print axioms subdivisionLimit_global_sheafification_injective
/-- Canonical sheafification is an isomorphism on actual global supported subdivision-limit sections.
Source: Bredon, Sheaf Theory, second edition, VI.12; global comparison on compact Hausdorff spaces.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimit_global_sheafification_isIso (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology X)
      ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op ⊤)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨subdivisionLimit_global_sheafification_injective X n,
    subdivisionLimit_global_sheafification_surjective X n⟩

#print axioms subdivisionLimit_global_sheafification_isIso
end HodgeLean.Foundations.RationalHomologyManifold
