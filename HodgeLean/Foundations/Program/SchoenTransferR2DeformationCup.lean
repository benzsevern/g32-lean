import HodgeLean.Foundations.Program.SchoenTransferR2NeighbourhoodCup
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Supported cup annihilation from an ambient deformation

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- An ambient map homotopic to the identity and taking a support neighbourhood
into an embedded component supplies the required actual neighbourhood factor.
Source: Hatcher, Algebraic Topology, §0 and §3.2; subspace topology.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_deformation_cup_eq_zero
    (X Q : TopCat.{0}) (j : Q ⟶ X) (hj : IsEmbedding j)
    (S : Closeds X) (hS : (S : Set X) = Set.range j)
    (V : Opens X) (hSV : (S : Set X) ⊆ V)
    (F : C(X, X)) (H : ContinuousMap.Homotopy (ContinuousMap.id X) F)
    (hF : Set.MapsTo F V S) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (S : Set X)ᶜ) p)
    (u : Cohomology ℚ X q) (hu : cohomologyMap ℚ q j u = 0) :
    HodgeLean.Foundations.Singular.cup X rfl
      (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (S : Set X)ᶜ) p a) u = 0 := by
  let f : C(↥(V : Set X), Set.range j) :=
    ⟨fun x => ⟨F x, hS ▸ hF x.property⟩,
      (F.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let r : TopCat.of (V : Set X) ⟶ Q :=
    TopCat.ofHom ((⟨hj.toHomeomorph.symm, hj.toHomeomorph.symm.continuous⟩ : C(Set.range j, Q)).comp f)
  let incl : C(↥(V : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  have he : F.comp incl = j.hom.comp r.hom := by
    ext x
    change F x = j (hj.toHomeomorph.symm (f x))
    exact (congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply (f x))).symm
  have H' : TopCat.Homotopy (TopCat.ofHom incl) (r ≫ j) :=
    (H.compContinuousMap incl).cast (ContinuousMap.id_comp incl) he
  exact s4_assembly_neighbourhood_cup_eq_zero X Q j S V hSV r H' p q a u hu

#print axioms s4_assembly_deformation_cup_eq_zero
end HodgeLean.Foundations.Program
