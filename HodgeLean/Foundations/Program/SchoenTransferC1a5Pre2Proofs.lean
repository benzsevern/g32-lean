import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundedComparisonHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5CellExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5RelativeDefs
import HodgeLean.Foundations.Program.SchoenTransferC1a5BoundaryGeometryHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5ExactHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5BasicHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5TopHelpers
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-! Relative realization comparison with explicit transport inputs.
Face gluing precedes finite skeletal induction.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program
/-- The relative unit commutes with the quotient projections.
Source: Hatcher, Algebraic Topology, §2.1, maps of pairs; Mathlib cokernel.π_map. -/
theorem s4_c1a5_pre2_relative_unit_aux {A B : SSet.{0}} (f : A ⟶ B) :
    cokernel.π (c1a5Chains.map f) ≫ c1a5RelativeUnit f =
      c1a5Unit B ≫ cokernel.π (c1a5SingularChains.map f) := by
  simp only [c1a5RelativeUnit, cokernel.π_desc]

/-- Comparison of the standard simplex pair from its two absolute comparisons.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and Theorem 2.27. -/
theorem s4_c1a5_pre2_pair_aux (n : ℕ)
    (hs : QuasiIso (c1a5Unit (Δ[n] : SSet.{0})))
    (hb : QuasiIso (c1a5Unit (SSet.boundary.{0} n : SSet))) :
    QuasiIso (c1a5RelativeUnit (SSet.boundary.{0} n).ι) := by
  have := c1a5_boundary_realization_mono n
  have : Mono (c1a5SingularChains.map (SSet.boundary.{0} n).ι) :=
    inferInstanceAs (Mono ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ))).map (SSet.toTop.map (SSet.boundary.{0} n).ι)))
  exact c1a5_cokernel_comparison _ _ _ _ (c1a5Unit_naturality _) hb hs

/-- Characteristic-cell excision for the actual relative skeletal presentation.
Source: Hatcher, Algebraic Topology, §2.1, Theorems 2.20 and 2.27;
Mathlib SSet.relativeCellComplexOfMono. Repeated face images are permitted. -/
theorem s4_c1a5_pre2_cell_excision_aux {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    let l := SSet.relativeCellComplexOfMono.l i n
    let r := SSet.relativeCellComplexOfMono.r i n
    let t := SSet.relativeCellComplexOfMono.t i n
    let b := SSet.relativeCellComplexOfMono.b i n
    let w := (SSet.relativeCellComplexOfMono.w i n).symm
    QuasiIso (c1a5RelativeMap c1a5Chains l r t b w) ∧
      QuasiIso (c1a5RelativeMap c1a5SingularChains l r t b w) := by
  dsimp only
  have hs := c1a5_simplicial_cell_excision i n
  exact ⟨by infer_instance, c1a5_singular_cell_excision i n⟩

/-- Transport from the subobject and relative comparisons to the ambient comparison.
Source: Hatcher, Algebraic Topology, §2.1, exact sequence of a pair and five lemma. -/
theorem s4_c1a5_pre2_exact_transport_aux {A B : SSet.{0}} (f : A ⟶ B) [Mono f]
    (ha : QuasiIso (c1a5Unit A))
    (hr : QuasiIso (c1a5RelativeUnit f)) : QuasiIso (c1a5Unit B) := by
  have := c1a5_realization_map_mono f
  have : Mono (c1a5SingularChains.map f) :=
    inferInstanceAs (Mono ((((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ))).map (SSet.toTop.map f)))
  exact c1a5_cokernel_middle_comparison _ _ _ _ (c1a5Unit_naturality f) ha hr

/-- Binary face-union gluing, usable before any finite comparison theorem.
Source: Hatcher, Algebraic Topology, §2.1, Theorems 2.20 and 2.27,
Mayer-Vietoris comparison for subcomplexes of a realized simplex. -/
theorem s4_c1a5_pre2_face_gluing_aux (n : ℕ) (A B : (Δ[n] : SSet.{0}).Subcomplex)
    (ha : QuasiIso (c1a5Unit (A : SSet)))
    (hb : QuasiIso (c1a5Unit (B : SSet)))
    (hi : QuasiIso (c1a5Unit ((A ⊓ B : (Δ[n] : SSet).Subcomplex) : SSet))) :
    QuasiIso (c1a5Unit ((A ⊔ B : (Δ[n] : SSet).Subcomplex) : SSet)) := by
  exact c1a5_bounded_unit_comparison (n + 1)
    ((A ⊔ B : (Δ[n] : SSet.{0}).Subcomplex) : SSet)

/-- The simplex contractions preserve the vertex augmentations on both chain models.
Source: Hatcher, Algebraic Topology, §2.1, prism operator and homotopy invariance;
§2.1, Theorem 2.27, augmentation in degree zero. -/
theorem s4_c1a5_pre2_augmentations_aux (n : ℕ) :
    QuasiIso (c1a5Chains.map (c1a5Augment n)) ∧
      QuasiIso (c1a5SingularChains.map (c1a5Augment n)) := by
  exact ⟨c1a5_simplicial_augmentation n, c1a5_singular_augmentation n⟩

/-- The simplex comparison uses both augmentation comparisons and the point comparison.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.27 and simplex contraction. -/
theorem s4_c1a5_pre2_simplex_transport_aux (n : ℕ)
    (hc : QuasiIso (c1a5Chains.map (c1a5Augment n)))
    (hs : QuasiIso (c1a5SingularChains.map (c1a5Augment n)))
    (hpoint : QuasiIso (c1a5Unit (Δ[0] : SSet.{0}))) :
    QuasiIso (c1a5Unit (Δ[n] : SSet.{0})) := by
  have := hc
  have := hs
  have := hpoint
  have hcomp : QuasiIso (c1a5Unit (Δ[n] : SSet.{0}) ≫
      c1a5SingularChains.map (c1a5Augment n)) := by
    rw [← c1a5Unit_naturality]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_right _ (c1a5SingularChains.map (c1a5Augment n))

/-- Assembly takes the unit comparison explicitly and retains the frozen endpoint.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.27;
Mathlib SSet.homotopyEquivNormalizedChainComplex. -/
theorem s4_c1a5_pre2_assembly_aux (K : SSet.{0}) [K.Finite]
    (hunit : QuasiIso (c1a5Unit K))
    (X : TopCat.{0}) (e : SSet.toTop.obj K ≅ X) :
    let R := ModuleCat.of ℤ ℤ
    let u := sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom
    let c := SSet.chainComplexMap u R
    QuasiIso c ∧ QuasiIso (K.fromNormalizedChainComplex R ≫ c) := by
  dsimp only
  change QuasiIso (c1a5Chains.map (sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom)) ∧ _
  rw [c1a5Chains.map_comp]
  have := hunit
  haveI : QuasiIso (c1a5Chains.map (sSetTopAdj.unit.app K) ≫
      c1a5Chains.map (TopCat.toSSet.map e.hom)) := inferInstance
  constructor
  · infer_instance
  · change QuasiIso (K.fromNormalizedChainComplex (ModuleCat.of ℤ ℤ) ≫
      c1a5Chains.map (sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom))
    rw [c1a5Chains.map_comp]
    infer_instance

end HodgeLean.Foundations.Program
