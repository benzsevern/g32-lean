import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris

/-! # Ordinary homology vanishing through actual open covers -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing on two actual open pieces and their original overlap gives ordinary ambient homology vanishing, through the actual singular Mayer--Vietoris sequence.
Source: Hatcher, Algebraic Topology, section 2.2, the Mayer--Vietoris exact sequence.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_cover_homology_vanishes
    (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hu : Subsingleton (Homology ℚ (TopCat.of U) (n + 1)))
    (hv : Subsingleton (Homology ℚ (TopCat.of V) (n + 1)))
    (hi : Subsingleton (Homology ℚ (TopCat.of ↥(U ∩ V)) n)) :
    Subsingleton (Homology ℚ X (n + 1)) := by
  letI := hu
  letI := hv
  letI := hi
  let e := singularMayerVietorisHomologySumIso X U V (n + 1)
  have hz : IsZero (Homology ℚ (TopCat.of U) (n + 1) ⊞
      Homology ℚ (TopCat.of V) (n + 1) : ModuleCat ℚ) :=
    (biprod_isZero_iff _ _).mpr ⟨ModuleCat.isZero_of_subsingleton _, ModuleCat.isZero_of_subsingleton _⟩
  letI : Subsingleton (Homology ℚ (TopCat.of U) (n + 1) ⊞
      Homology ℚ (TopCat.of V) (n + 1) : ModuleCat ℚ) := ModuleCat.subsingleton_of_isZero hz
  letI : Subsingleton ((singularMayerVietorisShortComplex X U V).X₂.homology (n + 1)) :=
    e.toLinearEquiv.injective.subsingleton
  have hzero (c : Homology ℚ X (n + 1)) : c = 0 := by
    have hk : (singularMayerVietorisBoundary X U V hU hV hUV n).hom c = 0 :=
      Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (singularMayerVietoris_exact_ambient X U V hU hV hUV n) c hk
    have ha0 : a = 0 := Subsingleton.elim _ _
    rw [ha0, map_zero] at ha
    exact ha.symm
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

end HodgeLean.Foundations.QuotientDuality
