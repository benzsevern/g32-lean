import HodgeLean.Foundations.Singular.SmallCup
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative

/-! # First cochain layer of the supported product

The construction is the ambient Alexander–Whitney lift of two relative cochains.
Descent to the complement of the intersection remains a separate task.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters

/-- The two complements, whose union is the complement of the intersection.
Source: Hatcher, Algebraic Topology, §3.2, relative cup products. -/
def ccm13_complementFamily (Y : TopCat.{0}) (S T : Set Y) : Bool → Set Y :=
  fun b => if b then Tᶜ else Sᶜ

/-- Source: complements of the empty and full supports on a point. -/
example : ccm13_complementFamily (TopCat.of PUnit) Set.univ ∅ true = Set.univ := by
  simp [ccm13_complementFamily]

/-- Ambient Alexander–Whitney product of cochains on the two complement pairs.
This does not yet descend through the relative chains of the union.
Source: Hatcher, Algebraic Topology, §3.2, relative cup products. -/
def ccm13_relativeCupLift (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    Cochain ℚ (TopCat.toSSet.obj Y) (p + q) :=
  cupCochain Y p q (relativeCochainToAbsolute ℚ (TopPair.ofSubset Sᶜ) p u)
    (relativeCochainToAbsolute ℚ (TopPair.ofSubset Tᶜ) q v)

/-- Source: the ambient product formula on the constructed point pair. -/
example : ccm13_relativeCupLift (TopCat.of PUnit) Set.univ Set.univ 0 0 0 0 =
    cupCochain (TopCat.of PUnit) 0 0
      (relativeCochainToAbsolute ℚ (TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ) 0 0)
      (relativeCochainToAbsolute ℚ (TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ) 0 0) := rfl

/-- The unit functional descended to the relative chains of the point with empty complement.
Source: the cokernel universal property for relative chains; Hatcher, §3.1. -/
def ccm13_pointUnit : RelativeCochain ℚ
    (TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ) 0 := by
  let P := TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ
  exact ((relativeChainProjectionComponentIsCokernelForCap ℚ P 0).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (unitCochain (R := ℚ) (TopCat.of PUnit))) (by
      apply ModuleCat.hom_ext
      change cochainMap ℚ (TopCat.toSSet.map P.map) 0
        (unitCochain (R := ℚ) (TopCat.of PUnit)) = 0
      let : IsEmpty P.snd := ⟨fun x => x.2 (Set.mem_univ _)⟩
      exact cochain_eq_zero_of_isEmpty P.snd 0 _))).hom
/-- Source: the defining cokernel factorization of the unit functional. -/
example : relativeCochainToAbsolute ℚ
    (TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ) 0 ccm13_pointUnit =
    unitCochain (R := ℚ) (TopCat.of PUnit) := by
  unfold ccm13_pointUnit
  change ((relativeChainProjection ℚ _).f 0 ≫ _).hom = _
  exact congrArg ModuleCat.Hom.hom
    ((Cofork.IsColimit.π_desc (relativeChainProjectionComponentIsCokernelForCap ℚ (TopPair.ofSubset (Set.univ : Set (TopCat.of PUnit))ᶜ) 0)).trans (CokernelCofork.π_ofπ _ _ _))

end HodgeLean.Adapters
