import HodgeLean.Foundations.AnalyticDivisorAlgebraic23Proofs

/-! # Generic points and simultaneous reduced local equations

An implication from set-level Chow supplies the bh4 algebraization fields except codimension.
The local products are constructed from complete local factorizations and their orbit labels.
The auxiliary geometric proofs remain open for the proving lane.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic23
open Filter Set Topology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21
open HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open scoped Manifold CategoryTheory.MonObj

/-- Generic points retain the distinct carriers, positive weights and total support.
Source: Mathlib `IsIrreducible.closure_genericPoint`; `gaga22_chow_support`. -/
theorem gaga23_indexing (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    let N := gaga23_schemeEnumeration X hD hper hChow
    let x := fun i : Fin N.1 ↦ gaga23_point X hD hper hChow (N.2 i)
    let mult := fun i : Fin N.1 ↦ (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)
    (∀ i, closure ({x i} : Set X.left) = gaga23_carrier X hD hper hChow (N.2 i)) ∧
    Function.Injective x ∧
    (∀ i, 0 < mult i) ∧
    abelianExp X '' localDivisorSupport V f = ⋃ i, gaga23_componentSupport X (x i) :=
  gaga23_indexing_aux X hD hper hChow

/-- Every factor in a group has the group's descended multiplicity.
Source: `gaga21_glued_multiplicity`; `gaga22_descended_representative`. -/
theorem gaga23_group_weights {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    ∀ a : Fin A.count,
      A.exponents a = (gaga22_descendedDivisor Λ hD hper).multiplicity
        (gaga23_label Λ hD hper j p hp A a) :=
  gaga23_group_weights_aux Λ hD hper j p hp A

/-- Products of distinct coprime irreducible germs are squarefree, including empty groups.
Source: Gunning--Rossi II.B, Theorems 3--6; unique factorization in `AnalyticGermAt`. -/
theorem gaga23_group_squarefree {d : ℕ} {I : Type} (f : (Fin d → ℂ) → ℂ)
    (p : Fin d → ℂ) (A : gaga23_Factorization f p) (label : Fin A.count → I) :
    ∃ hg : ∀ i, AnalyticAt ℂ (gaga23_group A.factors label i) p,
      ∀ i, Squarefree (⟨Filter.Germ.ofFun (gaga23_group A.factors label i),
        gaga23_group A.factors label i, hg i, rfl⟩ : AnalyticGermAt d p) :=
  gaga23_group_squarefree_aux f p A label

/-- The grouped zero germs identify each descended carrier, with units off that carrier.
Source: Chirka §5.1; stage-21 finite local branches and stage-22 carrier descent. -/
theorem gaga23_group_zeros {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    ∀ O : gaga22_ComponentOrbit Λ hD hper,
      (∀ᶠ z in 𝓝 p,
        gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O z = 0 ↔
          QuotientAddGroup.mk z ∈ (gaga22_descendedDivisor Λ hD hper).carrier O) ∧
      (QuotientAddGroup.mk p ∉ (gaga22_descendedDivisor Λ hD hper).carrier O →
        gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) O p ≠ 0) :=
  gaga23_group_zeros_aux Λ hD hper j p hp A

/-- Regroup the complete factorization using orbit weights, retaining its analytic unit.
Source: Griffiths--Harris, Chapter 1 §1; `gaga23_group_weights` and finite product regrouping. -/
theorem gaga23_group_associated {d : ℕ} {J : Type}
    {V : J → Set (Fin d → ℂ)} {f : J → (Fin d → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin d → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    [CompactSpace ((Fin d → ℂ) ⧸ Λ)]
    (j : J) (p : Fin d → ℂ) (hp : p ∈ V j)
    (A : gaga23_Factorization (f j) p) :
    let N := gaga23_enumeration Λ hD hper
    AreAssociatedAt (f j) (fun z ↦ ∏ i : Fin N.1,
      gaga23_group A.factors (gaga23_label Λ hD hper j p hp A) (N.2 i) z ^
        (gaga22_descendedDivisor Λ hD hper).multiplicity (N.2 i)) p :=
  gaga23_group_associated_aux Λ hD hper j p hp A

/-- The constructed orbit products give simultaneous reduced equations on the scheme's cover.
Source: `gaga23_group_squarefree`, `gaga23_group_zeros`, `gaga23_group_associated`;
Birkenhake--Lange §1.1, exponential uniformization. -/
theorem gaga23_local_equations (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C)
    (j : J) (p : Fin (dim X.left) → ℂ) (hp : p ∈ V j) :
    let N := gaga23_schemeEnumeration X hD hper hChow
    let A := gaga23_factorization (f j) p (hD.2.2.1 j p hp) (hD.2.2.2.1 j p hp)
    let g := fun i : Fin N.1 ↦ gaga23_group A.factors
      (gaga23_label (abelianPeriodLattice X).toAddSubgroup hD hper j p hp A) (N.2 i)
    ∃ hg : ∀ i, AnalyticAt ℂ (g i) p,
      (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
        AnalyticGermAt (dim X.left) p)) ∧
      (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔ abelianExp X z ∈
        gaga23_componentSupport X (gaga23_point X hD hper hChow (N.2 i))) ∧
      AreAssociatedAt (f j) (fun z ↦ ∏ i, g i z ^
        (gaga22_descendedOnX X hD hper).multiplicity (N.2 i)) p :=
  gaga23_local_equations_aux X hD hper hChow j p hp

/-- An implication from set-level Chow supplying every bh4 field except codimension.
Source: `gaga23_indexing`, `gaga23_local_equations`; Serre, GAGA, Théorème 3. -/
theorem gaga23_algebraization_without_codim (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] {J : Type}
    {V : J → Set (Fin (dim X.left) → ℂ)} {f : J → (Fin (dim X.left) → ℂ) → ℂ}
    (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : abelianPeriodLattice X) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (hChow : ∀ Z : Set (ComplexPoint X), IsClosedAnalytic (Fin (dim X.left) → ℂ) Z →
      ∃ C : Set X.left, IsClosed C ∧
        Z = (Point.underlying : ComplexPoint X → X.left) ⁻¹' C) :
    ∃ (n : ℕ) (x : Fin n → X.left) (mult : Fin n → ℕ),
      Function.Injective x ∧
      (∀ i, 0 < mult i) ∧
      (abelianExp X '' localDivisorSupport V f = ⋃ i, gaga23_componentSupport X (x i)) ∧
      (∀ j p, p ∈ V j →
        ∃ (g : Fin n → (Fin (dim X.left) → ℂ) → ℂ)
          (hg : ∀ i, AnalyticAt ℂ (g i) p),
          (∀ i, Squarefree (⟨Filter.Germ.ofFun (g i), g i, hg i, rfl⟩ :
            AnalyticGermAt (dim X.left) p)) ∧
          (∀ i, ∀ᶠ z in 𝓝 p, g i z = 0 ↔
            abelianExp X z ∈ gaga23_componentSupport X (x i)) ∧
          AreAssociatedAt (f j) (fun z ↦ ∏ i, g i z ^ mult i) p) :=
  gaga23_algebraization_without_codim_aux X hD hper hChow

end HodgeLean.Foundations.AnalyticDivisorAlgebraic23
