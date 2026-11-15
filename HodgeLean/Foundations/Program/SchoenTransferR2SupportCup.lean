import HodgeLean.Foundations.Program.SchoenTransferR2RelativeLift
import HodgeLean.Adapters.CycleClassDivisorProduct3

/-! # Supported cup annihilation on an open neighbourhood

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Relative cohomology of the full pair has one element in every degree.
Source: Hatcher, Algebraic Topology, §2.1, the relative chain quotient.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_full_pair_subsingleton (X : TopCat.{0}) (n : ℕ) :
    Subsingleton (RelativeCohomology ℚ (TopPair.ofSubset (X := X) Set.univ) n) := by
  let P := TopPair.ofSubset (X := X) Set.univ
  haveI : IsIso P.hom :=
    (TopCat.isIso_iff_isHomeomorph P.hom).mpr (Homeomorph.Set.univ X).isHomeomorph
  haveI : IsIso ((chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map P.hom)
    infer_instance
  have hz : IsZero ((relativeChainFunctor ℚ).obj P) :=
    isZero_cokernel_of_epi ((chainPairFunctor ℚ).obj P).hom
  have hh : IsZero (RelativeHomology ℚ P n) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) n).map_isZero hz
  exact relativeCohomology_subsingleton ℚ P n (ModuleCat.subsingleton_of_isZero hh)

/-- A supported class cups to zero with a class vanishing on an open neighbourhood
of its entire support.
Source: Hatcher, Algebraic Topology, §3.2, relative cup product and exact sequence.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_support_cup_eq_zero
    (X : TopCat.{0}) (S : Closeds X) (U : Opens X)
    (hSU : (S : Set X) ⊆ U) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (S : Set X)ᶜ) p)
    (u : Cohomology ℚ X q)
    (hu : cohomologyMap ℚ q (TopPair.ofSubset (X := X) (U : Set X)).hom u = 0) :
    HodgeLean.Foundations.Singular.cup X rfl
      (relativeCohomologyToAbsolute ℚ (TopPair.ofSubset (S : Set X)ᶜ) p a) u = 0 := by
  let T : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have huT : cohomologyMap ℚ q (TopPair.ofSubset (X := X) (T : Set X)ᶜ).hom u = 0 := by
    have hTU : (T : Set X)ᶜ = (U : Set X) := compl_compl (U : Set X)
    rw [hTU]
    exact hu
  obtain ⟨b, hb⟩ := s4_assembly_relative_lift
    (TopPair.ofSubset (X := X) (T : Set X)ᶜ) q u huT
  have hfull : (((S ⊓ T : Closeds X) : Set X)ᶜ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x hx
    change x ∈ S ∧ x ∉ U at hx
    exact hx.2 (hSU hx.1)
  haveI : Subsingleton (RelativeCohomology ℚ
      (TopPair.ofSubset (X := X) ((S ⊓ T : Closeds X) : Set X)ᶜ) (p + q)) := by
    rw [hfull]
    exact s4_assembly_full_pair_subsingleton X (p + q)
  have hz : ccm15_relativeCup X S T p q a b = 0 := Subsingleton.elim _ _
  rw [← hb, ← ccm15_relativeCup_absolute, hz, map_zero]

#print axioms s4_assembly_full_pair_subsingleton
#print axioms s4_assembly_support_cup_eq_zero
end HodgeLean.Foundations.Program
