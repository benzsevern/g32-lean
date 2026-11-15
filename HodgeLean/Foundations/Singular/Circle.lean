import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Contractible
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CohomologyZero
import HodgeLean.Foundations.Singular.MayerVietoris
import HodgeLean.Foundations.Singular.Cup
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The two-arc cover of the circle

The complements of zero and one half are open contractible arcs.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLean.Foundations.Singular

/-- The circle cut at the class of the real number `a`.
Source: Hatcher, *Algebraic Topology*, §2.2, the two-arc cover of the circle.
-/
def circleArc (a : ℝ) : Set UnitAddCircle := {(a : UnitAddCircle)}ᶜ

example : (0 : UnitAddCircle) ∉ circleArc 0 := by simp [circleArc]

/-- A cut circle is the open unit interval, via the quotient map.
Source: Mathlib `AddCircle.openPartialHomeomorphCoe`.
-/
def circleArcHomeomorph (a : ℝ) : Set.Ioo a (a + 1) ≃ₜ circleArc a :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).toHomeomorphSourceTarget

example (a : ℝ) (x : Set.Ioo a (a + 1)) :
    (circleArcHomeomorph a x).val = (x.val : UnitAddCircle) := rfl

/-- Each of the cut-circle arcs is open.
Source: Hatcher, *Algebraic Topology*, §2.2, the two-arc cover.
-/
theorem isOpen_circleArc (a : ℝ) : IsOpen (circleArc a) := isOpen_compl_singleton

/-- Each cut circle is contractible, since its interval model is convex.
Source: Hatcher, *Algebraic Topology*, §2.2; Mathlib `Convex.contractibleSpace`.
-/
theorem contractibleSpace_circleArc (a : ℝ) : ContractibleSpace (circleArc a) := by
  let : ContractibleSpace (Set.Ioo a (a + 1)) :=
    (convex_Ioo a (a + 1)).contractibleSpace ⟨a + 1 / 2, by constructor <;> linarith⟩
  exact (circleArcHomeomorph a).symm.contractibleSpace

private theorem circle_half_ne_zero : ((1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  have h' : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      (by constructor <;> norm_num) (by constructor <;> norm_num)).mp h
  norm_num at h'

/-- The arcs cut at zero and one half cover the circle.
Source: Hatcher, *Algebraic Topology*, §2.2, Mayer–Vietoris for the circle.
-/
theorem circleArc_cover : circleArc 0 ∪ circleArc (1 / 2) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = 0
  · right
    simpa [circleArc, hx] using circle_half_ne_zero.symm
  · left
    simpa [circleArc] using hx

/-- Degree-zero cohomology of any path-connected space has dimension one.
Source: Hatcher, *Algebraic Topology*, §3.1, degree-zero cohomology.
-/
theorem finrank_cohomology_zero_of_pathConnected (Y : TopCat.{0}) [PathConnectedSpace Y] :
    Module.finrank ℚ (Cohomology ℚ Y 0) = 1 :=
  (finrank_eq_one_iff_of_nonzero (cohomologyUnitZero ℚ Y)
    (cohomologyUnitZero_ne_zero ℚ Y)).mpr (span_cohomologyUnitZero_eq_top ℚ Y)

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of UnitAddCircle) 0) = 1 :=
  finrank_cohomology_zero_of_pathConnected _

/-- Positive-degree singular cohomology of a contractible space is zero.
Source: Hatcher, *Algebraic Topology*, §3.1, homotopy invariance and the point computation;
upstream `singularCochainComplex_exactAt_of_contractible`.
-/
theorem isZero_cohomology_succ_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) :
    CategoryTheory.Limits.IsZero (Cohomology ℚ (TopCat.of X) (n + 1)) :=
  (AlgebraicTopology.singularCochainComplex_exactAt_of_contractible ℚ X n).isZero_homology

/-- The rational cohomology dimensions of a nonempty contractible space.
Source: Hatcher, *Algebraic Topology*, §3.1, homotopy invariance and the point computation.
-/
theorem finrank_cohomology_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of X) n) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simpa using finrank_cohomology_zero_of_pathConnected (TopCat.of X)
  | succ n =>
    have : Subsingleton (Cohomology ℚ (TopCat.of X) (n + 1)) :=
      ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible X n)
    simp [Module.finrank_zero_of_subsingleton]

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of PUnit) 2) = 0 := by
  simpa using finrank_cohomology_of_contractible PUnit 2

/-- Contractible spaces have finite-dimensional rational cohomology in every degree.
Source: Hatcher, *Algebraic Topology*, §3.1, the point computation.
-/
theorem finite_cohomology_of_contractible (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) : Module.Finite ℚ (Cohomology ℚ (TopCat.of X) n) := by
  cases n with
  | zero =>
    exact Module.finite_of_finrank_eq_succ
      (finrank_cohomology_zero_of_pathConnected (TopCat.of X))
  | succ n =>
    have : Subsingleton (Cohomology ℚ (TopCat.of X) (n + 1)) :=
      ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible X n)
    infer_instance

/-- Homeomorphic spaces have linearly equivalent singular cohomology.
Source: Hatcher, *Algebraic Topology*, §3.1, homotopy invariance.
-/
def cohomologyHomeomorphEquiv {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) (n : ℕ) :
    Cohomology ℚ (TopCat.of X) n ≃ₗ[ℚ] Cohomology ℚ (TopCat.of Z) n :=
  ((HomologicalComplex.linearDualHomotopyEquiv
    (AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv ℚ e.toHomotopyEquiv)).toHomologyIso n).symm.toLinearEquiv

example (n : ℕ) : cohomologyHomeomorphEquiv (Homeomorph.refl PUnit) n 0 = 0 := map_zero _

/-- The inverse of the homeomorphism comparison is its cohomological pullback.
Source: Hatcher, *Algebraic Topology*, §3.1, functorial homotopy invariance.
-/
theorem cohomologyHomeomorphEquiv_symm {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) (n : ℕ) : (cohomologyHomeomorphEquiv e n).symm.toLinearMap =
      cohomologyMap ℚ n (TopCat.ofHom ⟨e, e.continuous⟩) := rfl

/-- A cylinder with contractible second factor has the cohomology of its first factor.
The inverse is pullback along the first projection.
Source: Hatcher, *Algebraic Topology*, §3.1, homotopy invariance.
-/
def cohomologyProdContractibleEquiv (Y C : Type) [TopologicalSpace Y] [TopologicalSpace C]
    [ContractibleSpace C] (n : ℕ) :
    Cohomology ℚ (TopCat.of (Y × C)) n ≃ₗ[ℚ] Cohomology ℚ (TopCat.of Y) n :=
  let e := ((ContinuousMap.HomotopyEquiv.refl Y).prodCongr
    (Classical.choice (ContractibleSpace.hequiv_unit C))).trans
      (Homeomorph.prodUnique Y Unit).toHomotopyEquiv
  ((HomologicalComplex.linearDualHomotopyEquiv
    (AlgebraicTopology.singularChainHomotopyEquivOfHomotopyEquiv ℚ e)).toHomologyIso n).symm.toLinearEquiv

/-- The cylinder equivalence is induced by the actual projection, not a chosen vector-space basis.
Source: Hatcher, *Algebraic Topology*, §3.1, functorial homotopy invariance.
-/
theorem cohomologyProdContractibleEquiv_symm (Y C : Type) [TopologicalSpace Y]
    [TopologicalSpace C] [ContractibleSpace C] (n : ℕ) :
    (cohomologyProdContractibleEquiv Y C n).symm.toLinearMap =
      cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) := rfl

example (n : ℕ) : cohomologyProdContractibleEquiv PUnit PUnit n 0 = 0 := map_zero _

/-- A subset pulled back from the second factor is the product with that subset.
Source: the subspace and product topology definitions (Mathlib `Homeomorph`).
-/
def prodSubsetHomeomorph (Y X : Type) [TopologicalSpace Y] [TopologicalSpace X]
    (S : Set X) : {p : Y × X // p.2 ∈ S} ≃ₜ Y × S where
  toFun p := (p.val.1, ⟨p.val.2, p.2⟩)
  invFun p := ⟨(p.1, p.2.val), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

example (p : {p : PUnit × ℝ // p.2 ∈ Set.Ioo (0 : ℝ) 1}) :
    (prodSubsetHomeomorph PUnit ℝ (Set.Ioo 0 1) p).1 = p.val.1 := rfl

private def prodDisjointCohomologyEquiv (Y X : Type) [TopologicalSpace Y] [TopologicalSpace X]
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
    (hd : Disjoint A B) (n : ℕ) :
    Cohomology ℚ (TopCat.of (Y × X)) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of (Y × A)) n × Cohomology ℚ (TopCat.of (Y × B)) n) :=
  (cohomologyDisjointCoverEquiv (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B)
    (hA.preimage continuous_snd) (hB.preimage continuous_snd)
    (by rw [← Set.preimage_union, hc]; rfl)
    (hd.preimage _) n).trans
      (LinearEquiv.prodCongr (cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X A) n)
        (cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X B) n))

private abbrev SlitInterval := {x : ℝ // 0 < x ∧ x < 1 ∧ x ≠ 1 / 2}

private theorem coe_interval_eq_half_iff (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    (x : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) ↔ x = 1 / 2 :=
  AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    ⟨le_of_lt h0, by simpa using h1⟩ (by constructor <;> norm_num)

private def slitIntervalHomeomorph : SlitInterval ≃ₜ
    ↥(circleArc 0 ∩ circleArc (1 / 2)) where
  toFun x := ⟨(x.val : UnitAddCircle),
    (circleArcHomeomorph 0 ⟨x.val, x.2.1, by simpa using x.2.2.1⟩).2,
    fun h => x.2.2.2 ((coe_interval_eq_half_iff x.val x.2.1 x.2.2.1).mp h)⟩
  invFun y :=
    let x := (circleArcHomeomorph 0).symm ⟨y.val, y.2.1⟩
    ⟨x.val, x.2.1, by simpa using x.2.2, by
      intro hx
      have he : (x.val : UnitAddCircle) = y.val :=
        congrArg Subtype.val ((circleArcHomeomorph 0).apply_symm_apply ⟨y.val, y.2.1⟩)
      exact y.2.2 (he.symm.trans (congrArg (fun t : ℝ => (t : UnitAddCircle)) hx))⟩
  left_inv x := by
    apply Subtype.ext
    change ((circleArcHomeomorph 0).symm ((circleArcHomeomorph 0)
      ⟨x.val, x.2.1, by simpa using x.2.2.1⟩)).val = x.val
    exact congrArg Subtype.val ((circleArcHomeomorph 0).symm_apply_apply
      ⟨x.val, x.2.1, by simpa using x.2.2.1⟩)
  right_inv y := by
    apply Subtype.ext
    change ((circleArcHomeomorph 0) ((circleArcHomeomorph 0).symm ⟨y.val, y.2.1⟩)).val = y.val
    exact congrArg Subtype.val ((circleArcHomeomorph 0).apply_symm_apply ⟨y.val, y.2.1⟩)
  continuous_toFun := ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp ((circleArcHomeomorph 0).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

private def slitLeft : Set SlitInterval := {x | x.val < 1 / 2}
private def slitRight : Set SlitInterval := {x | 1 / 2 < x.val}

private def slitLeftHomeomorph : slitLeft ≃ₜ Set.Ioo (0 : ℝ) (1 / 2) where
  toFun x := ⟨x.val.val, x.val.2.1, x.2⟩
  invFun x := ⟨⟨x.val, x.2.1, lt_trans x.2.2 (by norm_num), ne_of_lt x.2.2⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def slitRightHomeomorph : slitRight ≃ₜ Set.Ioo (1 / 2 : ℝ) 1 where
  toFun x := ⟨x.val.val, x.2, x.val.2.2.1⟩
  invFun x := ⟨⟨x.val, lt_trans (by norm_num) x.2.1, x.2.2, ne_of_gt x.2.1⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private instance slitLeft_contractible : ContractibleSpace slitLeft := by
  let : ContractibleSpace (Set.Ioo (0 : ℝ) (1 / 2)) :=
    (convex_Ioo (0 : ℝ) (1 / 2)).contractibleSpace ⟨1 / 4, by constructor <;> norm_num⟩
  exact slitLeftHomeomorph.contractibleSpace

private instance slitRight_contractible : ContractibleSpace slitRight := by
  let : ContractibleSpace (Set.Ioo (1 / 2 : ℝ) 1) :=
    (convex_Ioo (1 / 2 : ℝ) 1).contractibleSpace ⟨3 / 4, by constructor <;> norm_num⟩
  exact slitRightHomeomorph.contractibleSpace

private def slitCohomologyEquiv (n : ℕ) :
    Cohomology ℚ (TopCat.of SlitInterval) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of slitLeft) n × Cohomology ℚ (TopCat.of slitRight) n) :=
  cohomologyDisjointCoverEquiv (TopCat.of SlitInterval) slitLeft slitRight
    (isOpen_lt continuous_subtype_val continuous_const)
    (isOpen_lt continuous_const continuous_subtype_val)
    (Set.eq_univ_of_forall fun x => lt_or_gt_of_ne x.2.2.2)
    (Set.disjoint_left.mpr fun x h₁ h₂ => (not_lt_of_gt (show x.val < 1 / 2 from h₁)) h₂) n

private def overlapCohomologyEquiv (n : ℕ) :
    Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of slitLeft) n × Cohomology ℚ (TopCat.of slitRight) n) :=
  (cohomologyHomeomorphEquiv slitIntervalHomeomorph.symm n).trans (slitCohomologyEquiv n)

/-- The two-arc overlap has cohomology of dimension two in degree zero and zero otherwise.
Source: Hatcher, *Algebraic Topology*, §2.2 and §3.1, the two components of the overlap.
-/
theorem finrank_cohomology_circleArc_inter (n : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) n) =
      if n = 0 then 2 else 0 := by
  let :=  finite_cohomology_of_contractible slitLeft n
  let :=  finite_cohomology_of_contractible slitRight n
  rw [(overlapCohomologyEquiv n).finrank_eq, Module.finrank_prod,
    finrank_cohomology_of_contractible, finrank_cohomology_of_contractible]
  split_ifs <;> norm_num

/-- Positive-degree cohomology of the two-arc overlap vanishes.
Source: Hatcher, *Algebraic Topology*, §3.1, additivity on two contractible components.
-/
theorem isZero_cohomology_circleArc_inter_succ (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) (n + 1)) := by
  let :=  ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible slitLeft n)
  let :=  ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible slitRight n)
  let : Subsingleton (Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) (n + 1)) :=
    (overlapCohomologyEquiv (n + 1)).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

example : Module.finrank ℚ
    (Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) 0) = 2 :=
  finrank_cohomology_circleArc_inter 0

private theorem homeomorphEquiv_apply {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) (n : ℕ) (a : Cohomology ℚ (TopCat.of X) n) :
    cohomologyHomeomorphEquiv e n a =
      cohomologyMap ℚ n (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) a := rfl

private theorem homeomorphEquiv_cup {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) {p q k : ℕ} (h : p + q = k)
    (a : Cohomology ℚ (TopCat.of X) p) (b : Cohomology ℚ (TopCat.of X) q) :
    cohomologyHomeomorphEquiv e k (cup (TopCat.of X) h a b) =
      cup (TopCat.of Z) h (cohomologyHomeomorphEquiv e p a) (cohomologyHomeomorphEquiv e q b) :=
  cohomologyMap_cup _ (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) h a b

private theorem prodContractibleEquiv_cup (Y C : Type) [TopologicalSpace Y] [TopologicalSpace C]
    [ContractibleSpace C] {p q k : ℕ} (h : p + q = k)
    (a : Cohomology ℚ (TopCat.of (Y × C)) p) (b : Cohomology ℚ (TopCat.of (Y × C)) q) :
    cohomologyProdContractibleEquiv Y C k (cup (TopCat.of (Y × C)) h a b) =
      cup (TopCat.of Y) h (cohomologyProdContractibleEquiv Y C p a)
        (cohomologyProdContractibleEquiv Y C q b) := by
  apply (cohomologyProdContractibleEquiv Y C k).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = cohomologyMap ℚ k (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) _
  rw [cohomologyMap_cup]
  change _ = cup (TopCat.of (Y × C)) h
    ((cohomologyProdContractibleEquiv Y C p).symm (cohomologyProdContractibleEquiv Y C p a))
    ((cohomologyProdContractibleEquiv Y C q).symm (cohomologyProdContractibleEquiv Y C q b))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

private theorem prodContractibleEquiv_unit (Y C : Type) [TopologicalSpace Y] [TopologicalSpace C]
    [ContractibleSpace C] : cohomologyProdContractibleEquiv Y C 0
      (unit (R := ℚ) (TopCat.of (Y × C))) = unit (TopCat.of Y) := by
  apply (cohomologyProdContractibleEquiv Y C 0).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (cohomologyMap_unit (TopCat.of Y) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem prodDisjointCohomologyEquiv_cup (Y X : Type)
    [TopologicalSpace Y] [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (hd : Disjoint A B)
    {p q k : ℕ} (h : p + q = k)
    (a : Cohomology ℚ (TopCat.of (Y × X)) p) (b : Cohomology ℚ (TopCat.of (Y × X)) q) :
    prodDisjointCohomologyEquiv Y X A B hA hB hc hd k (cup (TopCat.of (Y × X)) h a b) =
      (cup (TopCat.of (Y × A)) h (prodDisjointCohomologyEquiv Y X A B hA hB hc hd p a).1
        (prodDisjointCohomologyEquiv Y X A B hA hB hc hd q b).1,
       cup (TopCat.of (Y × B)) h (prodDisjointCohomologyEquiv Y X A B hA hB hc hd p a).2
        (prodDisjointCohomologyEquiv Y X A B hA hB hc hd q b).2) := by
  simp only [prodDisjointCohomologyEquiv, LinearEquiv.trans_apply]
  rw [cohomologyDisjointCoverEquiv_apply (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) _ _ _ _ k,
    cohomologyDisjointCoverEquiv_apply (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) _ _ _ _ p,
    cohomologyDisjointCoverEquiv_apply (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) _ _ _ _ q]
  simp only [LinearEquiv.prodCongr_apply, cohomologyMap_cup]
  exact Prod.ext (homeomorphEquiv_cup (prodSubsetHomeomorph Y X A) h _ _)
    (homeomorphEquiv_cup (prodSubsetHomeomorph Y X B) h _ _)

private theorem homeomorphEquiv_prod_snd (Y X Z : Type) [TopologicalSpace Y]
    [TopologicalSpace X] [TopologicalSpace Z] (e : X ≃ₜ Z) (n : ℕ)
    (a : Cohomology ℚ (TopCat.of X) n) :
    cohomologyHomeomorphEquiv ((Homeomorph.refl Y).prodCongr e) n
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) a) =
    cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cohomologyHomeomorphEquiv e n a) := by
  rw [homeomorphEquiv_apply, homeomorphEquiv_apply,
    ← LinearMap.comp_apply, ← cohomologyMap_comp, ← LinearMap.comp_apply, ← cohomologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem prodDisjointCohomologyEquiv_snd (Y X : Type)
    [TopologicalSpace Y] [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (hd : Disjoint A B)
    (n : ℕ) (a : Cohomology ℚ (TopCat.of X) n) :
    prodDisjointCohomologyEquiv Y X A B hA hB hc hd n
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) a) =
    (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
        (cohomologyMap ℚ n (topologicalSubsetInclusion (TopCat.of X) A) a),
      cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
        (cohomologyMap ℚ n (topologicalSubsetInclusion (TopCat.of X) B) a)) := by
  unfold prodDisjointCohomologyEquiv
  rw [LinearEquiv.trans_apply, cohomologyDisjointCoverEquiv_apply
    (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) _ _ _ _ n]
  apply Prod.ext
  · change cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X A) n _ = _
    rw [homeomorphEquiv_apply (prodSubsetHomeomorph Y X A) n,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    dsimp only
    exact (congrArg (fun f => f a) (cohomologyMap_comp ℚ n
      (TopCat.ofHom ⟨(prodSubsetHomeomorph Y X A).symm,
        (prodSubsetHomeomorph Y X A).symm.continuous⟩)
      (topologicalSubsetInclusion (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) ≫
        TopCat.ofHom ⟨Prod.snd, continuous_snd⟩))).symm
  · change cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X B) n _ = _
    rw [homeomorphEquiv_apply (prodSubsetHomeomorph Y X B) n,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp,
      ← LinearMap.comp_apply, ← cohomologyMap_comp]
    dsimp only
    exact (congrArg (fun f => f a) (cohomologyMap_comp ℚ n
      (TopCat.ofHom ⟨(prodSubsetHomeomorph Y X B).symm,
        (prodSubsetHomeomorph Y X B).symm.continuous⟩)
      (topologicalSubsetInclusion (TopCat.of (Y × X)) (Prod.snd ⁻¹' B) ≫
        TopCat.ofHom ⟨Prod.snd, continuous_snd⟩))).symm

private theorem homeomorphEquiv_pullback {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) (W : TopCat.{0}) (f : TopCat.of Z ⟶ W) (n : ℕ)
    (a : Cohomology ℚ W n) :
    cohomologyHomeomorphEquiv e n
      (cohomologyMap ℚ n ((TopCat.ofHom ⟨e, e.continuous⟩) ≫ f) a) =
      cohomologyMap ℚ n f a := by
  rw [cohomologyMap_comp, LinearMap.comp_apply]
  change cohomologyHomeomorphEquiv e n
    ((cohomologyHomeomorphEquiv e n).symm (cohomologyMap ℚ n f a)) = _
  exact (cohomologyHomeomorphEquiv e n).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
private theorem prodDisjointCohomologyEquiv_projection (Y X : Type)
    [TopologicalSpace Y] [TopologicalSpace X] (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ) (hd : Disjoint A B)
    (n : ℕ) (a : Cohomology ℚ (TopCat.of Y) n) :
    prodDisjointCohomologyEquiv Y X A B hA hB hc hd n
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) =
    (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a,
      cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) := by
  unfold prodDisjointCohomologyEquiv
  rw [LinearEquiv.trans_apply, cohomologyDisjointCoverEquiv_apply
    (TopCat.of (Y × X)) (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) _ _ _ _ n]
  apply Prod.ext
  · change cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X A) n
      (cohomologyMap ℚ n (topologicalSubsetInclusion (TopCat.of (Y × X)) (Prod.snd ⁻¹' A))
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)) = _
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    exact homeomorphEquiv_pullback (prodSubsetHomeomorph Y X A) (TopCat.of Y)
      (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) n a
  · change cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y X B) n
      (cohomologyMap ℚ n (topologicalSubsetInclusion (TopCat.of (Y × X)) (Prod.snd ⁻¹' B))
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)) = _
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    exact homeomorphEquiv_pullback (prodSubsetHomeomorph Y X B) (TopCat.of Y)
      (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) n a

/-- The product of any space with the two-arc overlap has two copies of its cohomology.
Source: Hatcher, *Algebraic Topology*, §3.1, additivity and homotopy invariance.
-/
def cohomologyProdCircleOverlapEquiv (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Cohomology ℚ (TopCat.of (Y × ↥(circleArc 0 ∩ circleArc (1 / 2)))) n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of Y) n × Cohomology ℚ (TopCat.of Y) n) :=
  (cohomologyHomeomorphEquiv ((Homeomorph.refl Y).prodCongr slitIntervalHomeomorph.symm) n).trans
    ((prodDisjointCohomologyEquiv Y SlitInterval slitLeft slitRight
      (isOpen_lt continuous_subtype_val continuous_const)
      (isOpen_lt continuous_const continuous_subtype_val)
      (Set.eq_univ_of_forall fun x => lt_or_gt_of_ne x.2.2.2)
      (Set.disjoint_left.mpr fun x h₁ h₂ =>
        (not_lt_of_gt (show x.val < 1 / 2 from h₁)) h₂) n).trans
      (LinearEquiv.prodCongr (cohomologyProdContractibleEquiv Y slitLeft n)
        (cohomologyProdContractibleEquiv Y slitRight n)))

example (n : ℕ) : cohomologyProdCircleOverlapEquiv PUnit n 0 = 0 := map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- Pullback from the first factor is the diagonal under the two-component overlap equivalence.
Source: Hatcher, *Algebraic Topology*, §3.1, naturality of additivity and homotopy invariance.
-/
theorem cohomologyProdCircleOverlapEquiv_projection (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (a : Cohomology ℚ (TopCat.of Y) n) :
    cohomologyProdCircleOverlapEquiv Y n
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) = (a, a) := by
  unfold cohomologyProdCircleOverlapEquiv
  simp only [LinearEquiv.trans_apply]
  rw [show cohomologyHomeomorphEquiv
      ((Homeomorph.refl Y).prodCongr slitIntervalHomeomorph.symm) n
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a) =
      cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a from
    homeomorphEquiv_pullback _ (TopCat.of Y) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) n a]
  rw [prodDisjointCohomologyEquiv_projection]
  change ((cohomologyProdContractibleEquiv Y slitLeft n)
      ((cohomologyProdContractibleEquiv Y slitLeft n).symm a),
    (cohomologyProdContractibleEquiv Y slitRight n)
      ((cohomologyProdContractibleEquiv Y slitRight n).symm a)) = _
  simp only [LinearEquiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The overlap decomposition preserves cup products component by component.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of cup product.
-/
theorem cohomologyProdCircleOverlapEquiv_cup (Y : Type) [TopologicalSpace Y]
    {p q k : ℕ} (h : p + q = k)
    (a : Cohomology ℚ (TopCat.of (Y × ↥(circleArc 0 ∩ circleArc (1 / 2)))) p)
    (b : Cohomology ℚ (TopCat.of (Y × ↥(circleArc 0 ∩ circleArc (1 / 2)))) q) :
    cohomologyProdCircleOverlapEquiv Y k (cup _ h a b) =
      (cup (TopCat.of Y) h (cohomologyProdCircleOverlapEquiv Y p a).1
        (cohomologyProdCircleOverlapEquiv Y q b).1,
       cup (TopCat.of Y) h (cohomologyProdCircleOverlapEquiv Y p a).2
        (cohomologyProdCircleOverlapEquiv Y q b).2) := by
  simp only [cohomologyProdCircleOverlapEquiv, LinearEquiv.trans_apply,
    homeomorphEquiv_cup, prodDisjointCohomologyEquiv_cup, LinearEquiv.prodCongr_apply,
    prodContractibleEquiv_cup]

private abbrev circleSpace := TopCat.of UnitAddCircle
private abbrev arc₀ := circleArc 0
private abbrev arc₁ := circleArc (1 / 2)
private abbrev circleMV := mvCochainShortComplex circleSpace arc₀ arc₁

private def circleMiddleEquiv (n : ℕ) : circleMV.X₂.homology n ≃ₗ[ℚ]
    (Cohomology ℚ (TopCat.of arc₀) n × Cohomology ℚ (TopCat.of arc₁) n) :=
  ((mvCohomologySumIso circleSpace arc₀ arc₁ n) ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

private instance circleMiddle_succ_subsingleton (n : ℕ) :
    Subsingleton (circleMV.X₂.homology (n + 1)) := by
  let := contractibleSpace_circleArc 0
  let := contractibleSpace_circleArc (1 / 2)
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible arc₀ n)
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible arc₁ n)
  exact (circleMiddleEquiv (n + 1)).injective.subsingleton

private theorem circleMiddle_zero_finrank : Module.finrank ℚ (circleMV.X₂.homology 0) = 2 := by
  let := contractibleSpace_circleArc 0
  let := contractibleSpace_circleArc (1 / 2)
  let := finite_cohomology_of_contractible arc₀ 0
  let := finite_cohomology_of_contractible arc₁ 0
  rw [(circleMiddleEquiv 0).finrank_eq, Module.finrank_prod,
    finrank_cohomology_zero_of_pathConnected, finrank_cohomology_zero_of_pathConnected]

private abbrev circleδ (n : ℕ) :=
  mvδ circleSpace arc₀ arc₁ (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover n
private abbrev circleRestriction (n : ℕ) :=
  mvRestriction circleSpace arc₀ arc₁ (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover n

private theorem circleδ_surjective (n : ℕ) : Function.Surjective (circleδ n) := by
  intro x
  exact (mv_exact₁ circleSpace arc₀ arc₁ (isOpen_circleArc 0) (isOpen_circleArc (1 / 2))
    circleArc_cover n x).mp (Subsingleton.elim _ _)

/-- Circle cohomology vanishes above degree one, from the two-arc Mayer–Vietoris sequence.
Source: Hatcher, *Algebraic Topology*, §2.2 and §3.1, the circle computation.
-/
theorem isZero_cohomology_circle_add_two (n : ℕ) :
    CategoryTheory.Limits.IsZero (Cohomology ℚ circleSpace (n + 2)) := by
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_circleArc_inter_succ n)
  let : Subsingleton (Cohomology ℚ circleSpace (n + 2)) :=
    (circleδ_surjective (n + 1)).subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem circle_one_finrank : Module.finrank ℚ (Cohomology ℚ circleSpace 1) = 1 := by
  let r := circleRestriction 0
  let d := mvDifference circleSpace arc₀ arc₁ 0
  let b := circleδ 0
  let := Module.finite_of_finrank_eq_succ circleMiddle_zero_finrank
  let := Module.finite_of_finrank_eq_succ (finrank_cohomology_circleArc_inter 0)
  let := Module.Finite.of_surjective b (circleδ_surjective 0)
  have hr : Module.finrank ℚ r.range = 1 := by
    rw [LinearMap.finrank_range_of_inj
      (mvRestriction_zero_injective circleSpace arc₀ arc₁ (isOpen_circleArc 0)
        (isOpen_circleArc (1 / 2)) circleArc_cover)]
    exact finrank_cohomology_zero_of_pathConnected _
  have hd : d.ker = r.range :=
    (LinearMap.exact_iff.mp (mv_exact₂ circleSpace arc₀ arc₁ (isOpen_circleArc 0)
      (isOpen_circleArc (1 / 2)) circleArc_cover 0))
  have hb : b.ker = d.range :=
    (LinearMap.exact_iff.mp (mv_exact₃ circleSpace arc₀ arc₁ (isOpen_circleArc 0)
      (isOpen_circleArc (1 / 2)) circleArc_cover 0))
  have h₁ := d.finrank_range_add_finrank_ker
  have h₂ := b.finrank_range_add_finrank_ker
  rw [hd, hr, circleMiddle_zero_finrank] at h₁
  rw [hb, LinearMap.range_eq_top.mpr (circleδ_surjective 0), finrank_top,
    finrank_cohomology_circleArc_inter] at h₂
  norm_num at h₂
  exact Nat.add_right_cancel (h₂.trans ((Nat.add_comm 1 _).trans h₁).symm)

/-- Rational singular cohomology of the circle has dimension one in degrees zero and one,
and vanishes in every higher degree.
Source: Hatcher, *Algebraic Topology*, §2.2 and §3.1, Mayer–Vietoris for the circle.
HC no distance; AV milestone no distance.
-/
theorem finrank_cohomology_circle (k : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of UnitAddCircle) k) = if k ≤ 1 then 1 else 0 := by
  rcases k with _ | (_ | n)
  · simpa using finrank_cohomology_zero_of_pathConnected circleSpace
  · simpa using circle_one_finrank
  · let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_circle_add_two n)
    simp [Module.finrank_zero_of_subsingleton]

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of UnitAddCircle) 2) = 0 := by
  simpa using finrank_cohomology_circle 2

/-- Every rational cohomology group of the circle is finite-dimensional.
Source: Hatcher, *Algebraic Topology*, §3.1, the circle computation.
-/
theorem finite_cohomology_circle (k : ℕ) :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of UnitAddCircle) k) := by
  rcases k with _ | (_ | n)
  · exact Module.finite_of_finrank_eq_succ (finrank_cohomology_circle 0)
  · exact Module.finite_of_finrank_eq_succ (finrank_cohomology_circle 1)
  · let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_circle_add_two n)
    infer_instance

private theorem homeomorphEquiv_unit {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) : cohomologyHomeomorphEquiv e 0 (unit (R := ℚ) (TopCat.of X)) =
      unit (TopCat.of Z) := by
  apply (cohomologyHomeomorphEquiv e 0).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (cohomologyMap_unit (TopCat.of Z) (TopCat.ofHom ⟨e, e.continuous⟩)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem overlapCohomologyEquiv_unit :
    overlapCohomologyEquiv 0 (unit (R := ℚ) (TopCat.of ↥(arc₀ ∩ arc₁))) =
      (unit (TopCat.of slitLeft), unit (TopCat.of slitRight)) := by
  change slitCohomologyEquiv 0
    (cohomologyHomeomorphEquiv slitIntervalHomeomorph.symm 0 (unit _)) = _
  rw [homeomorphEquiv_unit]
  unfold slitCohomologyEquiv
  rw [cohomologyDisjointCoverEquiv_apply]
  simp only [cohomologyMap_unit]

private theorem exists_smul_unit (X : TopCat.{0}) [PathConnectedSpace X]
    (a : Cohomology ℚ X 0) : ∃ r : ℚ, r • unit (R := ℚ) X = a := by
  have hs : Submodule.span ℚ {unit (R := ℚ) X} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero (unit (R := ℚ) X) (unit_ne_zero X)).mp
      (finrank_cohomology_zero_of_pathConnected X)
  apply Submodule.mem_span_singleton.mp
  rw [hs]
  trivial

/-- The degree-zero overlap indicator with values one on the component modeled by
`(0, 1/2)` and zero on the component modeled by `(1/2, 1)`.
Source: constructed here for the two-arc Mayer–Vietoris generator, Hatcher,
*Algebraic Topology*, §3.1. HC no distance; AV milestone no distance.
-/
def circleOverlapIndicator : Cohomology ℚ (TopCat.of ↥(circleArc 0 ∩ circleArc (1 / 2))) 0 :=
  (overlapCohomologyEquiv 0).symm (unit (TopCat.of slitLeft), 0)

example : overlapCohomologyEquiv 0 circleOverlapIndicator =
    (unit (TopCat.of slitLeft), 0) := (overlapCohomologyEquiv 0).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Pullback of the chosen overlap indicator has component values `(1, 0)` over any space.
Source: constructed here from the defining indicator and naturality of additivity.
-/
theorem cohomologyProdCircleOverlapEquiv_indicator (Y : Type) [TopologicalSpace Y] :
    cohomologyProdCircleOverlapEquiv Y 0
      (cohomologyMap ℚ 0 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleOverlapIndicator) =
      (unit (R := ℚ) (TopCat.of Y), 0) := by
  have hi := (overlapCohomologyEquiv 0).apply_symm_apply
    (unit (R := ℚ) (TopCat.of slitLeft), (0 : Cohomology ℚ (TopCat.of slitRight) 0))
  change overlapCohomologyEquiv 0 circleOverlapIndicator = _ at hi
  unfold overlapCohomologyEquiv slitCohomologyEquiv at hi
  rw [LinearEquiv.trans_apply, cohomologyDisjointCoverEquiv_apply] at hi
  have hL := congrArg Prod.fst hi
  have hR := congrArg Prod.snd hi
  dsimp only at hL hR
  unfold cohomologyProdCircleOverlapEquiv
  rw [LinearEquiv.trans_apply, homeomorphEquiv_prod_snd, LinearEquiv.trans_apply,
    prodDisjointCohomologyEquiv_snd]
  change (cohomologyProdContractibleEquiv Y slitLeft 0
      (cohomologyMap ℚ 0 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) _),
    cohomologyProdContractibleEquiv Y slitRight 0
      (cohomologyMap ℚ 0 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) _)) = _
  rw [hL, hR, cohomologyMap_unit, map_zero, map_zero, prodContractibleEquiv_unit]

/-- The oriented degree-one circle class is the connecting image of the first-component
indicator. The chain MV map has signs `(i, -j)`; the cochain overlap map is first
restriction minus second restriction.
Source: Hatcher, *Algebraic Topology*, §3.1, connecting homomorphism for the circle.
HC no distance; AV milestone no distance. Stage S4 retires no stated hypothesis.
-/
def circleClass : Cohomology ℚ (TopCat.of UnitAddCircle) 1 :=
  mvδ (TopCat.of UnitAddCircle) (circleArc 0) (circleArc (1 / 2))
    (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover 0 circleOverlapIndicator

example : circleClass = circleδ 0 circleOverlapIndicator := rfl

/-- The first-component indicator is not the restriction difference of two arc constants,
so its connecting image is nonzero.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris computation of the circle.
-/
theorem circleClass_ne_zero : circleClass ≠ 0 := by
  let := contractibleSpace_circleArc 0
  let := contractibleSpace_circleArc (1 / 2)
  intro hz
  obtain ⟨z, hz⟩ := (mv_exact₃ circleSpace arc₀ arc₁ (isOpen_circleArc 0)
    (isOpen_circleArc (1 / 2)) circleArc_cover 0 circleOverlapIndicator).mp hz
  obtain ⟨⟨a, b⟩, rfl⟩ := (circleMiddleEquiv 0).symm.surjective z
  obtain ⟨r, rfl⟩ := exists_smul_unit (TopCat.of arc₀) a
  obtain ⟨s, rfl⟩ := exists_smul_unit (TopCat.of arc₁) b
  rw [show (circleMiddleEquiv 0).symm =
    ((mvCohomologySumIso circleSpace arc₀ arc₁ 0 ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv).symm from rfl,
    mvDifference_sum_apply, map_smul, map_smul, cohomologyMap_unit,
    cohomologyMap_unit, ← sub_smul] at hz
  have h := congrArg (overlapCohomologyEquiv 0) hz
  rw [map_smul, overlapCohomologyEquiv_unit] at h
  change (r - s) • (unit (R := ℚ) (TopCat.of slitLeft), unit (TopCat.of slitRight)) =
    (overlapCohomologyEquiv 0) ((overlapCohomologyEquiv 0).symm _) at h
  rw [LinearEquiv.apply_symm_apply] at h
  have hr : r - s = 0 := (smul_eq_zero.mp (congrArg Prod.snd h)).resolve_right
    (unit_ne_zero (TopCat.of slitRight))
  have hl := congrArg Prod.fst h
  rw [hr, zero_smul] at hl
  exact unit_ne_zero (TopCat.of slitLeft) hl.symm

/-- The chosen Mayer–Vietoris circle class spans its degree-one rational cohomology.
Source: Hatcher, *Algebraic Topology*, §3.1, the circle computation.
-/
theorem span_circleClass_eq_top : Submodule.span ℚ {circleClass} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero circleClass circleClass_ne_zero).mp
    (by simpa using finrank_cohomology_circle 1)

example : circleClass ≠ 0 := circleClass_ne_zero

#print axioms circleOverlapIndicator
#print axioms circleClass
#print axioms circleClass_ne_zero
#print axioms span_circleClass_eq_top

#print axioms cohomologyProdContractibleEquiv
#print axioms cohomologyProdContractibleEquiv_symm
#print axioms cohomologyHomeomorphEquiv_symm
#print axioms prodSubsetHomeomorph
#print axioms cohomologyProdCircleOverlapEquiv
#print axioms finite_cohomology_circle
#print axioms isOpen_circleArc
#print axioms finite_cohomology_of_contractible
#print axioms cohomologyHomeomorphEquiv
#print axioms finrank_cohomology_circle
#print axioms isZero_cohomology_circle_add_two
#print axioms finrank_cohomology_circleArc_inter
#print axioms isZero_cohomology_circleArc_inter_succ
#print axioms isZero_cohomology_succ_of_contractible
#print axioms finrank_cohomology_of_contractible
#print axioms finrank_cohomology_zero_of_pathConnected
#print axioms circleArcHomeomorph
#print axioms contractibleSpace_circleArc
#print axioms circleArc_cover

end HodgeLean.Foundations.Singular
