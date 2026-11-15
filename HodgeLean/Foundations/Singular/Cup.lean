import HodgeLean.Foundations.Simplicial.Cup
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CochainCohomologyEquiv
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The Alexander–Whitney cup product

The cup product evaluates a cochain on the cap product with another cochain.
The cochain formula and Leibniz rule use the upstream front/back face machinery.
Associativity, both unit laws and naturality hold on cochains and on upstream
singular cohomology. Descent uses cocycles modulo coboundaries over any commutative
ring. The constant unit is nonzero on a
nonempty space over a nontrivial ring, and cohomology vanishes on the empty space.
This makes the cup product statable for C7 on the torus track; it retires nothing yet.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Limits
open AlgebraicTopology.Simplicial
open scoped Simplicial

namespace HodgeLean.Foundations.Singular

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

variable {R : Type} [CommRing R] (Y : TopCat.{0})

private theorem cochain_ext {X : SSet.{0}} {n : ℕ} (φ ψ : Cochain R X n)
    (h : ∀ σ : X _⦋n⦌, φ (chainOfSimplex R σ) = ψ (chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • chainOfSimplex R σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

/-- The Alexander–Whitney product of singular cochains, evaluated on front and back faces.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
def cupCochain (p q : ℕ) :
    Cochain R (TopCat.toSSet.obj Y) p →ₗ[R]
      Cochain R (TopCat.toSSet.obj Y) q →ₗ[R]
        Cochain R (TopCat.toSSet.obj Y) (p + q) :=
  HodgeLean.Foundations.Simplicial.cupCochain (TopCat.toSSet.obj Y) p q

/-- Evaluation on a singular simplex is the product of the evaluations on its two faces.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
theorem cupCochain_apply_simplex (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q)
    (σ : (TopCat.toSSet.obj Y) _⦋p + q⦌) :
    cupCochain Y p q φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R (frontFace (TopCat.toSSet.obj Y) σ)) *
        ψ (chainOfSimplex R (backFace (TopCat.toSSet.obj Y) σ)) :=
  HodgeLean.Foundations.Simplicial.cupCochain_apply_simplex (TopCat.toSSet.obj Y) p q φ ψ σ

example (φ ψ : Cochain R (TopCat.toSSet.obj Y) 0)
    (σ : (TopCat.toSSet.obj Y) _⦋0 + 0⦌) :
    cupCochain Y 0 0 φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R (frontFace (TopCat.toSSet.obj Y) σ)) *
        ψ (chainOfSimplex R (backFace (TopCat.toSSet.obj Y) σ)) :=
  cupCochain_apply_simplex Y 0 0 φ ψ σ

/-- The Leibniz rule, with the canonical reassociation of the first summand's degree.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6.
-/
theorem coboundary_cupCochain (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q) :
    coboundary R (p + q) (cupCochain Y p q φ ψ) =
      (cupCochain Y (p + 1) q (coboundary R p φ) ψ).comp (reassocChain R p q) +
        (-1 : R) ^ p • cupCochain Y p (q + 1) φ (coboundary R q ψ) :=
  HodgeLean.Foundations.Simplicial.coboundary_cupCochain (TopCat.toSSet.obj Y) p q φ ψ

/-- Pullback along a continuous map preserves the cochain cup product.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup product.
-/
theorem cupCochain_naturality {Z : TopCat.{0}} (f : Z ⟶ Y) (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q) :
    cochainMap R (TopCat.toSSet.map f) (p + q) (cupCochain Y p q φ ψ) =
      cupCochain Z p q (cochainMap R (TopCat.toSSet.map f) p φ)
        (cochainMap R (TopCat.toSSet.map f) q ψ) :=
  HodgeLean.Foundations.Simplicial.cupCochain_naturality (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) p q φ ψ

/-- Associativity of the Alexander–Whitney product, with its canonical degree transport.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity of the cup product.
-/
theorem cupCochain_assoc (p q r : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q)
    (χ : Cochain R (TopCat.toSSet.obj Y) r) :
    cupCochain Y (p + q) r (cupCochain Y p q φ ψ) χ =
      (cupCochain Y p (q + r) φ (cupCochain Y q r ψ χ)).comp
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
          (Nat.add_assoc p q r)).hom.hom :=
  HodgeLean.Foundations.Simplicial.cupCochain_assoc (TopCat.toSSet.obj Y) p q r φ ψ χ

/-- The constant singular zero-cochain with value one on every vertex.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
def unitCochain : Cochain R (TopCat.toSSet.obj Y) 0 :=
  HodgeLean.Foundations.Simplicial.unitCochain (TopCat.toSSet.obj Y)

/-- The unit cochain evaluates to one on each vertex.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
@[simp] theorem unitCochain_apply_simplex (σ : (TopCat.toSSet.obj Y) _⦋0⦌) :
    unitCochain (R := R) Y (chainOfSimplex R σ) = 1 :=
  HodgeLean.Foundations.Simplicial.unitCochain_apply_simplex (TopCat.toSSet.obj Y) σ

example (σ : (TopCat.toSSet.obj Y) _⦋0⦌) :
    unitCochain (R := R) Y (chainOfSimplex R σ) = 1 :=
  unitCochain_apply_simplex Y σ

/-- The constant unit cochain is closed.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
@[simp] theorem coboundary_unitCochain :
    coboundary R 0 (unitCochain (R := R) Y) = 0 :=
  HodgeLean.Foundations.Simplicial.coboundary_unitCochain (TopCat.toSSet.obj Y)

/-- The right unit law on singular cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem cupCochain_one (p : ℕ) (φ : Cochain R (TopCat.toSSet.obj Y) p) :
    cupCochain Y p 0 φ (unitCochain Y) = φ :=
  HodgeLean.Foundations.Simplicial.cupCochain_one (TopCat.toSSet.obj Y) p φ

/-- The left unit law on singular cochains, with the degree equality explicit.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem one_cupCochain (q : ℕ) (ψ : Cochain R (TopCat.toSSet.obj Y) q) :
    cupCochain Y 0 q (unitCochain Y) ψ =
      ψ.comp (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
        (Nat.zero_add q)).hom.hom :=
  HodgeLean.Foundations.Simplicial.one_cupCochain (TopCat.toSSet.obj Y) q ψ

/-- Constant zero-cochains multiply their scalar values.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
theorem cupCochain_constants (a b : R) :
    cupCochain Y 0 0 (a • unitCochain (R := R) Y) (b • unitCochain (R := R) Y) =
      (a * b) • unitCochain (R := R) Y :=
  HodgeLean.Foundations.Simplicial.cupCochain_constants (TopCat.toSSet.obj Y) a b

example : cupCochain (TopCat.of PUnit) 0 0
    ((2 : ℚ) • unitCochain (R := ℚ) _) ((3 : ℚ) • unitCochain (R := ℚ) _) =
      (6 : ℚ) • unitCochain (R := ℚ) _ := by
  convert cupCochain_constants (TopCat.of PUnit) (2 : ℚ) 3 using 1
  norm_num

private abbrev dualShortComplex (n : ℕ) :=
  (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).sc n).linearDual

private def cocycleToCycle (n : ℕ) :
    Cocycle R (TopCat.toSSet.obj Y) n →ₗ[R]
      LinearMap.ker (dualShortComplex (R := R) Y n).g.hom where
  toFun φ := ⟨φ.1, by
    change (((AlgebraicTopology.Singular.SingularChainComplex R Y).sc n).f.hom.dualMap) φ.1 = 0
    have hφ : coboundary R n φ.1 = 0 := φ.2
    change (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).d
      ((ComplexShape.down ℕ).prev n) n).hom.dualMap φ.1 = 0
    rw [ChainComplex.prev]
    exact hφ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def quotientEquiv (n : ℕ) :
    (dualShortComplex (R := R) Y n).moduleCatLeftHomologyData.H ≃ₗ[R]
      AlgebraicTopology.Singular.Cohomology R Y n :=
  (dualShortComplex (R := R) Y n).moduleCatHomologyIso.toLinearEquiv.symm.trans
    (AlgebraicTopology.Singular.cochainCohomologyEquiv R Y n)

/-- The singular cohomology class represented by a closed singular cochain.
Source: Hatcher, *Algebraic Topology*, §3.1, cohomology as cocycles modulo coboundaries.
-/
def cohomologyClass (n : ℕ) :
    Cocycle R (TopCat.toSSet.obj Y) n →ₗ[R]
      AlgebraicTopology.Singular.Cohomology R Y n :=
  (quotientEquiv Y n).toLinearMap.comp
    (((dualShortComplex (R := R) Y n).moduleCatToCycles.range).mkQ.comp
      (cocycleToCycle Y n))

example (n : ℕ) : cohomologyClass (R := R) Y n 0 = 0 := map_zero _

/-- Every singular cohomology class has a cocycle representative.
Source: Hatcher, *Algebraic Topology*, §3.1, cohomology as cocycles modulo coboundaries.
-/
theorem cohomologyClass_surjective (n : ℕ) :
    Function.Surjective (cohomologyClass (R := R) Y n) := by
  intro a
  obtain ⟨b, rfl⟩ := (quotientEquiv (R := R) Y n).surjective a
  induction b using Submodule.Quotient.induction_on with
  | H b =>
    refine ⟨cohomologyCycleToCocycle R n b, ?_⟩
    rfl

private def castCocycle {m n : ℕ} (h : m = n) :
    Cocycle R (TopCat.toSSet.obj Y) m ≃ₗ[R] Cocycle R (TopCat.toSSet.obj Y) n := by
  subst n
  exact LinearEquiv.refl R _

private theorem castCocycle_val {m n : ℕ} (h : m = n)
    (φ : Cocycle R (TopCat.toSSet.obj Y) m) :
    (castCocycle Y h φ).1 = φ.1.comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq h.symm).hom.hom := by
  subst n
  rfl

private theorem cohomologyClass_cast_eq_zero {m n : ℕ} (h : m = n)
    (φ : Cocycle R (TopCat.toSSet.obj Y) m) :
    cohomologyClass Y n (castCocycle Y h φ) = 0 ↔ cohomologyClass Y m φ = 0 := by
  subst n
  rfl

private def boundaryCocycle (n : ℕ) (φ : Cochain R (TopCat.toSSet.obj Y) n) :
    Cocycle R (TopCat.toSSet.obj Y) (n + 1) :=
  ⟨coboundary R n φ, coboundary_coboundary R n φ⟩

private theorem cohomologyClass_boundary (n : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) n) :
    cohomologyClass Y (n + 1) (boundaryCocycle Y n φ) = 0 := by
  let K := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)
  let T := (K.sc (n + 1)).linearDual
  let hn : (ComplexShape.down ℕ).next (n + 1) = n := ChainComplex.next_nat_succ n
  let η : T.X₁ := φ.comp (K.XIsoOfEq hn).hom.hom
  have hη : (η : Module.Dual R (K.X ((ComplexShape.down ℕ).next (n + 1)))).comp
      (K.XIsoOfEq hn).inv.hom = φ := by
    ext c
    exact congrArg φ (ConcreteCategory.congr_hom (K.XIsoOfEq hn).inv_hom_id c)
  have he := cohomologyCycleToCocycle_moduleCatToCycles_succ R n η
  dsimp only at he
  rw [hη] at he
  have ht : T.moduleCatToCycles η = cocycleToCycle Y (n + 1) (boundaryCocycle Y n φ) := by
    apply Subtype.ext
    exact congrArg (fun x : Cocycle R (TopCat.toSSet.obj Y) (n + 1) => x.1) he
  have hq : (Submodule.Quotient.mk (cocycleToCycle Y (n + 1) (boundaryCocycle Y n φ)) :
      T.moduleCatLeftHomologyData.H) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨η, ht⟩
  change quotientEquiv Y (n + 1) (Submodule.Quotient.mk
    (cocycleToCycle Y (n + 1) (boundaryCocycle Y n φ))) = 0
  exact (congrArg (quotientEquiv Y (n + 1)) hq).trans (map_zero _)

private def cupCocycle (p q : ℕ) :
    Cocycle R (TopCat.toSSet.obj Y) p →ₗ[R]
      Cocycle R (TopCat.toSSet.obj Y) q →ₗ[R]
        Cocycle R (TopCat.toSSet.obj Y) (p + q) where
  toFun φ :=
    { toFun := fun ψ => ⟨cupCochain Y p q φ.1 ψ.1, by
        change coboundary R (p + q) (cupCochain Y p q φ.1 ψ.1) = 0
        rw [coboundary_cupCochain, show coboundary R p φ.1 = 0 from φ.2,
          show coboundary R q ψ.1 = 0 from ψ.2]
        simp⟩
      map_add' := fun ψ χ => Subtype.ext (map_add (cupCochain Y p q φ.1) ψ.1 χ.1)
      map_smul' := fun a ψ => Subtype.ext (map_smul (cupCochain Y p q φ.1) a ψ.1) }
  map_add' φ ψ := by
    apply LinearMap.ext
    intro χ
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (cupCochain Y p q) φ.1 ψ.1) χ.1
  map_smul' a φ := by
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (cupCochain Y p q) a φ.1) ψ.1

private theorem cupCocycle_boundary_left (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) p)
    (ψ : Cocycle R (TopCat.toSSet.obj Y) q) :
    cohomologyClass Y (p + 1 + q) (cupCocycle Y (p + 1) q (boundaryCocycle Y p φ) ψ) = 0 := by
  let h : p + 1 + q = p + q + 1 := by omega
  rw [← cohomologyClass_cast_eq_zero Y h]
  have hc : castCocycle Y h (cupCocycle Y (p + 1) q (boundaryCocycle Y p φ) ψ) =
      boundaryCocycle Y (p + q) (cupCochain Y p q φ ψ.1) := by
    apply Subtype.ext
    rw [castCocycle_val]
    change (cupCochain Y (p + 1) q (coboundary R p φ) ψ.1).comp (reassocChain R p q) =
      coboundary R (p + q) (cupCochain Y p q φ ψ.1)
    rw [coboundary_cupCochain, show coboundary R q ψ.1 = 0 from ψ.2]
    simp
  rw [hc]
  exact cohomologyClass_boundary Y (p + q) _

private theorem cupCocycle_boundary_right (p q : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q) :
    cohomologyClass Y (p + (q + 1)) (cupCocycle Y p (q + 1) φ (boundaryCocycle Y q ψ)) = 0 := by
  have hs : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
    rw [← pow_add, (Even.add_self p).neg_one_pow]
  have hc : cupCocycle Y p (q + 1) φ (boundaryCocycle Y q ψ) =
      (-1 : R) ^ p • boundaryCocycle Y (p + q) (cupCochain Y p q φ.1 ψ) := by
    apply Subtype.ext
    change cupCochain Y p (q + 1) φ.1 (coboundary R q ψ) =
      (-1 : R) ^ p • coboundary R (p + q) (cupCochain Y p q φ.1 ψ)
    rw [coboundary_cupCochain, show coboundary R p φ.1 = 0 from φ.2]
    simp [smul_smul, hs]
  rw [hc, map_smul]
  exact (congrArg (fun a => (-1 : R) ^ p • a)
    (cohomologyClass_boundary Y (p + q) (cupCochain Y p q φ.1 ψ))).trans (smul_zero _)

private theorem boundaries_zero :
    (dualShortComplex (R := R) Y 0).moduleCatToCycles = 0 := by
  apply LinearMap.ext
  intro η
  apply Subtype.ext
  change (((AlgebraicTopology.Singular.SingularChainComplex R Y).sc 0).g.hom.dualMap) η = 0
  have hg : ((AlgebraicTopology.Singular.SingularChainComplex R Y).sc 0).g = 0 := by
    change (AlgebraicTopology.Singular.SingularChainComplex R Y).d 0
      ((ComplexShape.down ℕ).next 0) = 0
    apply HomologicalComplex.shape
    rw [ChainComplex.next_nat_zero]
    simp
  rw [hg]
  ext c
  let ηF : Module.Dual R ((AlgebraicTopology.Singular.SingularChainComplex R Y).sc 0).X₃ := η
  change ηF 0 = 0
  exact map_zero ηF

private theorem cohomologyClass_zero_injective :
    Function.Injective (cohomologyClass (R := R) Y 0) := by
  intro φ ψ h
  have hq := (quotientEquiv (R := R) Y 0).injective h
  change Submodule.Quotient.mk (cocycleToCycle Y 0 φ) =
    Submodule.Quotient.mk (cocycleToCycle Y 0 ψ) at hq
  rw [Submodule.Quotient.eq, boundaries_zero, LinearMap.range_zero] at hq
  have hcycles : cocycleToCycle Y 0 φ = cocycleToCycle Y 0 ψ := sub_eq_zero.mp hq
  apply Subtype.ext
  exact congrArg (fun x : LinearMap.ker (dualShortComplex (R := R) Y 0).g.hom =>
    x.1) hcycles

/-- The degree-zero cup unit is the class of the constant cochain one.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
def unit : AlgebraicTopology.Singular.Cohomology R Y 0 :=
  cohomologyClass Y 0 ⟨unitCochain Y, coboundary_unitCochain Y⟩

example : unit (R := R) Y =
    cohomologyClass Y 0 ⟨unitCochain Y, coboundary_unitCochain Y⟩ := rfl


/-- A nonempty space has a nonzero cup unit over a nontrivial coefficient ring.
Source: Hatcher, *Algebraic Topology*, §3.1 and §3.2, degree-zero cohomology and its unit.
-/
theorem unit_ne_zero [Nontrivial R] [Nonempty Y] : unit (R := R) Y ≠ 0 := by
  intro h
  have hc := cohomologyClass_zero_injective (R := R) Y
    (h.trans (map_zero (cohomologyClass (R := R) Y 0)).symm)
  let σ : (TopCat.toSSet.obj Y) _⦋0⦌ :=
    (Y.toSSetObjEquiv _).symm (ContinuousMap.const _ (Classical.arbitrary Y))
  have he := LinearMap.congr_fun (congrArg Subtype.val hc) (chainOfSimplex R σ)
  simp at he

/-- Every singular cochain on an empty space vanishes.
Source: Hatcher, *Algebraic Topology*, §3.1, singular cochains as duals of singular chains.
-/
theorem cochain_eq_zero_of_isEmpty [IsEmpty Y] (n : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) n) : φ = 0 := by
  apply cochain_ext
  intro σ
  exact isEmptyElim ((Y.toSSetObjEquiv _) σ (Classical.arbitrary _))

/-- Singular cohomology of an empty space vanishes in every degree.
Source: Hatcher, *Algebraic Topology*, §3.1, singular cohomology.
-/
theorem cohomology_eq_zero_of_isEmpty [IsEmpty Y] (n : ℕ)
    (a : AlgebraicTopology.Singular.Cohomology R Y n) : a = 0 := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y n a
  have h : φ = 0 := Subtype.ext (cochain_eq_zero_of_isEmpty Y n φ.1)
  rw [h, map_zero]

example : unit (R := ℚ) (TopCat.of PUnit) ≠ 0 := unit_ne_zero _

example (n : ℕ) (a : AlgebraicTopology.Singular.Cohomology R (TopCat.of PEmpty) n) :
    a = 0 := cohomology_eq_zero_of_isEmpty _ n a


private def cycleCupClass (p q : ℕ) :
    LinearMap.ker (dualShortComplex (R := R) Y p).g.hom →ₗ[R]
      LinearMap.ker (dualShortComplex (R := R) Y q).g.hom →ₗ[R]
        AlgebraicTopology.Singular.Cohomology R Y (p + q) where
  toFun φ := (cohomologyClass Y (p + q)).comp
    ((cupCocycle Y p q (cohomologyCycleToCocycle R p φ)).comp (cohomologyCycleToCocycle R q))
  map_add' φ ψ := by
    ext χ
    change cohomologyClass Y (p + q)
      (cupCocycle Y p q (cohomologyCycleToCocycle R p (φ + ψ)) (cohomologyCycleToCocycle R q χ)) = _
    simp only [map_add, LinearMap.add_apply, LinearMap.comp_apply]
  map_smul' a φ := by
    ext ψ
    change cohomologyClass Y (p + q)
      (cupCocycle Y p q (cohomologyCycleToCocycle R p (a • φ)) (cohomologyCycleToCocycle R q ψ)) = _
    simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply]

private theorem cycleCupClass_left (p q : ℕ) :
    (dualShortComplex (R := R) Y p).moduleCatToCycles.range ≤
      (cycleCupClass (R := R) Y p q).ker := by
  rintro _ ⟨η, rfl⟩
  apply LinearMap.ext
  intro ψ
  change cohomologyClass Y (p + q) (cupCocycle Y p q
    (cohomologyCycleToCocycle R p ((dualShortComplex Y p).moduleCatToCycles η))
    (cohomologyCycleToCocycle R q ψ)) = 0
  cases p with
  | zero => simp only [boundaries_zero, LinearMap.zero_apply, map_zero]
  | succ p =>
    rw [cohomologyCycleToCocycle_moduleCatToCycles_succ]
    exact cupCocycle_boundary_left Y p q _ _

private theorem cycleCupClass_right (p q : ℕ) :
    (dualShortComplex (R := R) Y q).moduleCatToCycles.range ≤
      (cycleCupClass (R := R) Y p q).flip.ker := by
  rintro _ ⟨η, rfl⟩
  apply LinearMap.ext
  intro φ
  change cohomologyClass Y (p + q) (cupCocycle Y p q
    (cohomologyCycleToCocycle R p φ)
    (cohomologyCycleToCocycle R q ((dualShortComplex Y q).moduleCatToCycles η))) = 0
  cases q with
  | zero => simp only [boundaries_zero, LinearMap.zero_apply, map_zero]
  | succ q =>
    rw [cohomologyCycleToCocycle_moduleCatToCycles_succ]
    exact cupCocycle_boundary_right Y p q _ _

private def cupQuotient (p q : ℕ) :
    (dualShortComplex (R := R) Y p).moduleCatLeftHomologyData.H →ₗ[R]
      (dualShortComplex (R := R) Y q).moduleCatLeftHomologyData.H →ₗ[R]
        AlgebraicTopology.Singular.Cohomology R Y (p + q) :=
  (cycleCupClass Y p q).liftQ₂ _ _ (cycleCupClass_left Y p q) (cycleCupClass_right Y p q)

/-- The Alexander–Whitney product on upstream singular cohomology, with an explicit target degree.
Source: Hatcher, *Algebraic Topology*, §3.2, cup product on cohomology and Lemma 3.6.
-/
def cup {p q k : ℕ} (h : p + q = k) :
    AlgebraicTopology.Singular.Cohomology R Y p →ₗ[R]
      AlgebraicTopology.Singular.Cohomology R Y q →ₗ[R]
        AlgebraicTopology.Singular.Cohomology R Y k := by
  subst k
  exact
    { toFun := fun a => (cupQuotient Y p q ((quotientEquiv Y p).symm a)).comp
        (quotientEquiv Y q).symm.toLinearMap
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }

example (a : AlgebraicTopology.Singular.Cohomology R Y 0) : cup Y (q := 0) rfl a 0 = 0 :=
  map_zero _

private theorem cup_on_class (p q k : ℕ) (h : p + q = k)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p) (ψ : Cocycle R (TopCat.toSSet.obj Y) q) :
    cup Y h (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y k (castCocycle Y h (cupCocycle Y p q φ ψ)) := by
  subst k
  change cupQuotient Y p q
    ((quotientEquiv Y p).symm ((quotientEquiv Y p) (Submodule.Quotient.mk (cocycleToCycle Y p φ))))
    ((quotientEquiv Y q).symm ((quotientEquiv Y q) (Submodule.Quotient.mk (cocycleToCycle Y q ψ)))) = _
  simp only [LinearEquiv.symm_apply_apply]
  rfl


/-- The constant class is a left unit for singular cup product.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem one_cup {q : ℕ} (a : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y (Nat.zero_add q) (unit Y) a = a := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y q a
  rw [unit, cup_on_class]
  apply congrArg (cohomologyClass Y q)
  apply Subtype.ext
  rw [castCocycle_val]
  change (cupCochain Y 0 q (unitCochain Y) φ.1).comp
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq (Nat.zero_add q).symm).hom.hom = φ.1
  rw [one_cupCochain]
  ext c
  let K := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)
  have hc := ConcreteCategory.congr_hom (K.XIsoOfEq (Nat.zero_add q)).inv_hom_id c
  exact congrArg φ.1 hc

/-- The constant class is a right unit for singular cup product.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem cup_one {p : ℕ} (a : AlgebraicTopology.Singular.Cohomology R Y p) :
    cup Y (Nat.add_zero p) a (unit Y) = a := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y p a
  rw [unit, cup_on_class]
  apply congrArg (cohomologyClass Y p)
  apply Subtype.ext
  exact cupCochain_one Y p φ.1

/-- Associativity with the same degree-equality interface as the geometric cup-product package.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity of the cup product.
-/
theorem cup_assoc {i j l ij jl k : ℕ} (hij : i + j = ij) (hjl : j + l = jl)
    (h₁ : ij + l = k) (h₂ : i + jl = k)
    (a : AlgebraicTopology.Singular.Cohomology R Y i)
    (b : AlgebraicTopology.Singular.Cohomology R Y j)
    (c : AlgebraicTopology.Singular.Cohomology R Y l) :
    cup Y h₁ (cup Y hij a b) c = cup Y h₂ a (cup Y hjl b c) := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y i a
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y j b
  obtain ⟨χ, rfl⟩ := cohomologyClass_surjective Y l c
  rw [cup_on_class, cup_on_class, cup_on_class, cup_on_class]
  apply congrArg (cohomologyClass Y k)
  cases hij
  cases hjl
  cases h₁
  apply Subtype.ext
  simp only [castCocycle_val]
  exact cupCochain_assoc Y i j l φ.1 ψ.1 χ.1

/-- Constant degree-zero classes multiply their scalar values.
Source: Hatcher, *Algebraic Topology*, §3.2, the unit and bilinearity of cup product.
-/
theorem cup_constants (a b : R) :
    cup Y rfl (a • unit (R := R) Y) (b • unit (R := R) Y) =
      (a * b) • unit (R := R) Y := by
  simp [map_smul, LinearMap.smul_apply, one_cup, smul_smul, mul_comm]

example : cup (TopCat.of PUnit) rfl
    ((2 : ℚ) • unit (R := ℚ) _) ((3 : ℚ) • unit (R := ℚ) _) =
      (6 : ℚ) • unit (R := ℚ) _ := by
  convert cup_constants (TopCat.of PUnit) (2 : ℚ) 3 using 1
  norm_num


private theorem homologyMap_class {S T : ShortComplex (ModuleCat R)} (f : S ⟶ T)
    (a : LinearMap.ker S.g.hom) (b : LinearMap.ker T.g.hom)
    (hab : f.τ₂.hom a.1 = b.1) :
    (ShortComplex.homologyMap f).hom (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk a)) =
      T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk b) := by
  let ac := S.moduleCatCyclesIso.inv.hom a
  let bc := T.moduleCatCyclesIso.inv.hom b
  have ha : S.homologyπ.hom ac = S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk a) :=
    ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π a
  have hb : T.homologyπ.hom bc = T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk b) :=
    ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_π b
  have hx : (ShortComplex.cyclesMap f).hom ac = bc := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    have hs : S.iCycles.hom ac = a.1 :=
      ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles a
    have ht : T.iCycles.hom bc = b.1 :=
      ConcreteCategory.congr_hom T.moduleCatCyclesIso_inv_iCycles b
    have hc := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i f) ac
    change T.iCycles.hom ((ShortComplex.cyclesMap f).hom ac) = f.τ₂.hom (S.iCycles.hom ac) at hc
    change T.iCycles.hom ((ShortComplex.cyclesMap f).hom ac) = T.iCycles.hom bc
    rw [hc, hs, ht]
    exact hab
  have hm := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality f) ac
  change (ShortComplex.homologyMap f).hom (S.homologyπ.hom ac) =
    T.homologyπ.hom ((ShortComplex.cyclesMap f).hom ac) at hm
  rw [ha, hx, hb] at hm
  exact hm

private def cochainCycle (n : ℕ) (φ : Cocycle R (TopCat.toSSet.obj Y) n) :
    LinearMap.ker ((AlgebraicTopology.Singular.SingularCochainComplex R Y).sc n).g.hom :=
  ⟨φ.1, by
    change ((AlgebraicTopology.Singular.SingularCochainComplex R Y).d n
      ((ComplexShape.up ℕ).next n)).hom φ.1 = 0
    rw [CochainComplex.next]
    exact φ.2⟩

private theorem cohomologyClass_eq (n : ℕ) (φ : Cocycle R (TopCat.toSSet.obj Y) n) :
    cohomologyClass Y n φ =
      ((AlgebraicTopology.Singular.SingularCochainComplex R Y).sc n).moduleCatHomologyIso.inv.hom
        (Submodule.Quotient.mk (cochainCycle Y n φ)) := by
  let e := HomologicalComplex.linearDualCochainComplexScIso
    (AlgebraicTopology.Singular.SingularChainComplex R Y) n
  exact homologyMap_class e.inv (cocycleToCycle Y n φ) (cochainCycle Y n φ) rfl

/-- A morphism of the degreewise short complexes whose middle map is right cup
multiplication induces right cup multiplication on cohomology.
Source: constructed here from the cocycle description of cup product in Hatcher,
*Algebraic Topology*, §3.2.
-/
theorem homologyMap_cup_right (p q k : ℕ) (h : p + q = k)
    (β : Cocycle R (TopCat.toSSet.obj Y) q)
    (f : (AlgebraicTopology.Singular.SingularCochainComplex R Y).sc p ⟶
      (AlgebraicTopology.Singular.SingularCochainComplex R Y).sc k)
    (hf : ∀ φ, f.τ₂.hom φ = (cupCochain Y p q φ β.1).comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq h.symm).hom.hom) :
    (ShortComplex.homologyMap f).hom =
      (cup Y h).flip (cohomologyClass Y q β) := by
  subst k
  ext a
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y p a
  change (ShortComplex.homologyMap f).hom (cohomologyClass Y p φ) =
    cup Y rfl (cohomologyClass Y p φ) (cohomologyClass Y q β)
  rw [cup_on_class, cohomologyClass_eq, cohomologyClass_eq]
  exact homologyMap_class f (cochainCycle Y p φ)
    (cochainCycle Y (p + q) (castCocycle Y rfl (cupCocycle Y p q φ β))) (hf φ.1)

/-- A degreewise map given by scalar times left cup multiplication induces the
same operation on cohomology.
Source: constructed here from the cocycle definition in Hatcher,
*Algebraic Topology*, §3.2.
-/
theorem homologyMap_cup_left (p q k : ℕ) (h : q + p = k)
    (β : Cocycle R (TopCat.toSSet.obj Y) q) (r : R)
    (f : (AlgebraicTopology.Singular.SingularCochainComplex R Y).sc p ⟶
      (AlgebraicTopology.Singular.SingularCochainComplex R Y).sc k)
    (hf : ∀ φ, f.τ₂.hom φ = r • (cupCochain Y q p β.1 φ).comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq h.symm).hom.hom) :
    (ShortComplex.homologyMap f).hom = r • cup Y h (cohomologyClass Y q β) := by
  subst k
  ext a
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y p a
  change (ShortComplex.homologyMap f).hom (cohomologyClass Y p φ) =
    r • cup Y rfl (cohomologyClass Y q β) (cohomologyClass Y p φ)
  rw [cup_on_class, ← map_smul, cohomologyClass_eq, cohomologyClass_eq]
  exact homologyMap_class f (cochainCycle Y p φ)
    (cochainCycle Y (q + p) (r • castCocycle Y rfl (cupCocycle Y q p β φ))) (hf φ.1)

private def pullbackCocycle {Z : TopCat.{0}} (f : Z ⟶ Y) (n : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) n) : Cocycle R (TopCat.toSSet.obj Z) n :=
  ⟨cochainMap R (TopCat.toSSet.map f) n φ.1, by
    have h := ConcreteCategory.congr_hom
      ((AlgebraicTopology.Singular.singularCochainComplexMap R f).comm n (n + 1)) φ.1
    change coboundary R n (cochainMap R (TopCat.toSSet.map f) n φ.1) =
      cochainMap R (TopCat.toSSet.map f) (n + 1) (coboundary R n φ.1) at h
    rw [show coboundary R n φ.1 = 0 from φ.2, map_zero] at h
    exact h⟩

private theorem cohomologyClass_naturality {Z : TopCat.{0}} (f : Z ⟶ Y) (n : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) n) :
    AlgebraicTopology.Singular.cohomologyMap R n f (cohomologyClass Y n φ) =
      cohomologyClass Z n (pullbackCocycle Y f n φ) := by
  rw [cohomologyClass_eq, cohomologyClass_eq]
  exact homologyMap_class
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℕ) n).map
      (AlgebraicTopology.Singular.singularCochainComplexMap R f))
    (cochainCycle Y n φ) (cochainCycle Z n (pullbackCocycle Y f n φ)) rfl

/-- Pulling back a cocycle pulls back the cohomology class it represents.
Source: Hatcher, *Algebraic Topology*, §3.1, functoriality of singular cohomology.
-/
theorem cohomologyMap_class {Z : TopCat.{0}} (f : Z ⟶ Y) (n : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) n) (ψ : Cocycle R (TopCat.toSSet.obj Z) n)
    (h : ψ.1 = cochainMap R (TopCat.toSSet.map f) n φ.1) :
    AlgebraicTopology.Singular.cohomologyMap R n f (cohomologyClass Y n φ) =
      cohomologyClass Z n ψ := by
  rw [cohomologyClass_naturality]
  exact congrArg (cohomologyClass Z n) (Subtype.ext h.symm)

/-- Pullback along a continuous map preserves the singular cohomology cup product.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup product.
-/
theorem cohomologyMap_cup {Z : TopCat.{0}} (f : Z ⟶ Y) {p q k : ℕ} (h : p + q = k)
    (a : AlgebraicTopology.Singular.Cohomology R Y p)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    AlgebraicTopology.Singular.cohomologyMap R k f (cup Y h a b) =
      cup Z h (AlgebraicTopology.Singular.cohomologyMap R p f a)
        (AlgebraicTopology.Singular.cohomologyMap R q f b) := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y p a
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y q b
  rw [cup_on_class, cohomologyClass_naturality, cohomologyClass_naturality,
    cohomologyClass_naturality, cup_on_class]
  apply congrArg (cohomologyClass Z k)
  subst k
  apply Subtype.ext
  exact cupCochain_naturality Y f p q φ.1 ψ.1


/-- Pullback preserves the constant degree-zero cohomology class.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup unit.
-/
@[simp] theorem cohomologyMap_unit {Z : TopCat.{0}} (f : Z ⟶ Y) :
    AlgebraicTopology.Singular.cohomologyMap R 0 f (unit (R := R) Y) = unit Z := by
  rw [unit, cohomologyClass_naturality, unit]
  apply congrArg (cohomologyClass Z 0)
  apply Subtype.ext
  exact HodgeLean.Foundations.Simplicial.cochainMap_unitCochain _ (TopCat.toSSet.map f)

example {Z : TopCat.{0}} (f : Z ⟶ Y) :
    AlgebraicTopology.Singular.cohomologyMap R 0 f (unit (R := R) Y) = unit Z :=
  cohomologyMap_unit Y f

private theorem pointUnit_bijective : Function.Bijective
    (LinearMap.toSpanSingleton R _ (unit (R := R) (TopCat.of PUnit))) := by
  let P := TopCat.of PUnit
  let u : Cocycle R (TopCat.toSSet.obj P) 0 := ⟨unitCochain P, coboundary_unitCochain P⟩
  let σ : (TopCat.toSSet.obj P) _⦋0⦌ :=
    (P.toSSetObjEquiv _).symm (ContinuousMap.const _ PUnit.unit)
  constructor
  · intro a b hab
    change a • unit (R := R) P = b • unit (R := R) P at hab
    have hc : cohomologyClass P 0 (a • u) = cohomologyClass P 0 (b • u) := by
      simpa only [map_smul, u, unit] using hab
    have hu := cohomologyClass_zero_injective P hc
    have hv := congrArg (fun x : Cocycle R (TopCat.toSSet.obj P) 0 =>
      x.1 (chainOfSimplex R σ)) hu
    simpa [u] using hv
  · intro a
    obtain ⟨φ, rfl⟩ := cohomologyClass_surjective P 0 a
    refine ⟨φ.1 (chainOfSimplex R σ), ?_⟩
    change φ.1 (chainOfSimplex R σ) • cohomologyClass P 0 u = cohomologyClass P 0 φ
    rw [← map_smul]
    apply congrArg (cohomologyClass P 0)
    apply Subtype.ext
    apply cochain_ext
    intro τ
    have hτ : τ = σ := (P.toSSetObjEquiv _).injective (by ext x)
    simp [u, hτ]

/-- Degree-zero singular cohomology of a point, identified with the coefficient ring by the unit.
Source: Hatcher, *Algebraic Topology*, §3.1, cohomology of a point.
-/
def pointCohomologyZeroEquiv : AlgebraicTopology.Singular.Cohomology R (TopCat.of PUnit) 0 ≃ₗ[R] R :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ (unit (R := R) (TopCat.of PUnit)))
    pointUnit_bijective).symm

/-- The point identification sends a scalar multiple of the unit to that scalar.
Source: Hatcher, *Algebraic Topology*, §3.1 and §3.2, normalization of the degree-zero unit.
-/
@[simp] theorem pointCohomologyZeroEquiv_smul_unit (a : R) :
    pointCohomologyZeroEquiv (a • unit (R := R) (TopCat.of PUnit)) = a :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton R _ (unit (R := R) (TopCat.of PUnit)))
    pointUnit_bijective).symm_apply_apply a

example : pointCohomologyZeroEquiv ((2 : ℚ) • unit (R := ℚ) (TopCat.of PUnit)) = 2 :=
  pointCohomologyZeroEquiv_smul_unit 2

/-- On a point, the cup product in bidegree `(0, 0)` is multiplication in the coefficient ring.
Source: Hatcher, *Algebraic Topology*, §3.2, cup product on a point.
-/
theorem pointCohomologyZeroEquiv_cup
    (a b : AlgebraicTopology.Singular.Cohomology R (TopCat.of PUnit) 0) :
    pointCohomologyZeroEquiv (R := R) (cup (R := R) (TopCat.of PUnit) (p := 0) (q := 0) rfl a b) =
      pointCohomologyZeroEquiv (R := R) a * pointCohomologyZeroEquiv (R := R) b := by
  obtain ⟨a, rfl⟩ := (pointCohomologyZeroEquiv (R := R)).symm.surjective a
  obtain ⟨b, rfl⟩ := (pointCohomologyZeroEquiv (R := R)).symm.surjective b
  change pointCohomologyZeroEquiv (R := R) (cup (R := R) (TopCat.of PUnit) (p := 0) (q := 0) rfl
    (a • unit (R := R) _) (b • unit (R := R) _)) =
      pointCohomologyZeroEquiv (R := R) (a • unit (R := R) _) *
        pointCohomologyZeroEquiv (R := R) (b • unit (R := R) _)
  rw [cup_constants, pointCohomologyZeroEquiv_smul_unit,
    pointCohomologyZeroEquiv_smul_unit, pointCohomologyZeroEquiv_smul_unit]



/-! ## Axiom audit -/

#print axioms cupCochain
#print axioms cupCochain_apply_simplex
#print axioms coboundary_cupCochain
#print axioms cupCochain_naturality
#print axioms cupCochain_assoc
#print axioms unitCochain
#print axioms unitCochain_apply_simplex
#print axioms coboundary_unitCochain
#print axioms cupCochain_one
#print axioms one_cupCochain
#print axioms cupCochain_constants
#print axioms cohomologyClass
#print axioms unit
#print axioms unit_ne_zero
#print axioms cochain_eq_zero_of_isEmpty
#print axioms cohomology_eq_zero_of_isEmpty
#print axioms cup
#print axioms one_cup
#print axioms cup_one
#print axioms cup_assoc
#print axioms cup_constants
#print axioms cohomologyMap_unit
#print axioms cohomologyMap_class
#print axioms homologyMap_cup_right
#print axioms homologyMap_cup_left
#print axioms cohomologyMap_cup
#print axioms pointCohomologyZeroEquiv
#print axioms pointCohomologyZeroEquiv_smul_unit
#print axioms pointCohomologyZeroEquiv_cup

end HodgeLean.Foundations.Singular
