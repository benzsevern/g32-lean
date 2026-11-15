import HodgeLean.Foundations.Program.SchoenSegrePowerOverlaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual image of a projective tuple chart is determined by the individual factor chart images. -/
theorem s2_segrePowerChart_range (d n : ℕ) (a : Fin n → Fin (d + 1)) :
    Set.range (s2_segrePowerChartι d n a) =
      {x | ∀ i, s2_schemeProductπ n (fun _ => g3c_P d) i x ∈ Set.range (g3c_chartι d (a i))} := by
  induction n with
  | zero =>
    ext x
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      exact ⟨x, rfl⟩
  | succ n ih =>
    ext x
    let f := terminal.from (g3c_P d)
    let g := terminal.from (s2_segrePower d n)
    change (x : (pullback f g : Scheme)) ∈ Set.range (pullback.map
      (terminal.from (Spec (.of (Away (UniversalGrading d) (X (a 0) : UniversalRing d)))))
      (terminal.from (s2_segrePowerChart d n (fun i => a i.succ))) f g
      (g3c_chartι d (a 0)) (s2_segrePowerChartι d n (fun i => a i.succ)) (𝟙 (terminal Scheme))
      (terminal.hom_ext _ _) (terminal.hom_ext _ _)) ↔ _
    rw [Scheme.Pullback.range_map]
    constructor
    · rintro ⟨h₀, ht⟩ i
      refine Fin.cases h₀ (fun j => ?_) i
      exact ((Set.ext_iff.mp (ih (fun j => a j.succ)) ((pullback.snd f g) x)).mp ht) j
    · intro H
      refine ⟨H 0, ?_⟩
      apply (Set.ext_iff.mp (ih (fun j => a j.succ)) ((pullback.snd f g) x)).mpr
      intro j
      exact H j.succ

/-- Membership in the basic open of a finite product of global sections is membership in every factor basic open. -/
theorem s2_mem_basicOpen_prod {ι : Type} (X : Scheme.{0}) (s : Finset ι)
    (r : ι → Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen (∏ i ∈ s, r i) ↔ ∀ i ∈ s, x ∈ X.basicOpen (r i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_one]
    constructor
    · intro _ i hi
      exact ((Finset.notMem_empty i) hi).elim
    · intro _
      trivial
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.basicOpen_mul]
    change (x ∈ X.basicOpen (r i) ∧ x ∈ X.basicOpen (∏ j ∈ s, r j)) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hi, hs⟩ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hs j hj
    · intro H
      exact ⟨H i (Finset.mem_insert_self i s), fun j hj => H j (Finset.mem_insert_of_mem hj)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Basic opens of actual normalized tuple-chart coordinates recover the corresponding factor chart preimages. -/
theorem s2_segrePowerCoord_basicOpen (d n : ℕ) (a : Fin n → Fin (d + 1))
    (i : Fin n) (k : Fin (d + 1)) :
    (s2_segrePowerChart d n a).basicOpen (s2_segrePowerCoord d n a i k) =
      s2_schemeProductπ n _ i ⁻¹ᵁ
        (g3c_chartι d (a i) ⁻¹ᵁ (g3c_chartι d k).opensRange) := by
  rw [g3c_chartι_preimage_opensRange, Scheme.preimage_basicOpen_top]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual tuple-chart overlaps are the basic opens of their Segre coordinate evaluations. -/
theorem s2_segrePowerChartι_preimage_opensRange (d n : ℕ)
    (a b : Fin n → Fin (d + 1)) :
    s2_segrePowerChartι d n b ⁻¹ᵁ (s2_segrePowerChartι d n a).opensRange =
      (s2_segrePowerChart d n b).basicOpen (s2_segrePowerSections d n b (X a)) := by
  ext x
  change s2_segrePowerChartι d n b x ∈ Set.range (s2_segrePowerChartι d n a) ↔ _
  have hleft : s2_segrePowerChartι d n b x ∈ Set.range (s2_segrePowerChartι d n a) ↔
      ∀ i, s2_schemeProductπ n (fun _ => g3c_P d) i (s2_segrePowerChartι d n b x) ∈
        Set.range (g3c_chartι d (a i)) :=
    Set.ext_iff.mp (s2_segrePowerChart_range d n a) _
  have hright : x ∈ (s2_segrePowerChart d n b).basicOpen
      (s2_segrePowerSections d n b (X a)) ↔
      ∀ i, x ∈ (s2_segrePowerChart d n b).basicOpen (s2_segrePowerCoord d n b i (a i)) := by
    rw [s2_segrePowerSections_X]
    exact (s2_mem_basicOpen_prod _ Finset.univ _ x).trans
      (by simp only [Finset.mem_univ, true_implies])
  refine hleft.trans (Iff.trans ?_ hright.symm)
  apply forall_congr'
  intro i
  have H := congrArg (fun f : s2_segrePowerChart d n b ⟶ g3c_P d => f x)
    (s2_segrePowerChartι_π d n b i)
  have HC := Iff.of_eq (congrArg
    (fun U : (s2_segrePowerChart d n b).Opens => x ∈ U)
    (s2_segrePowerCoord_basicOpen d n b i (a i)))
  exact (Iff.of_eq (congrArg (fun z : g3c_P d => z ∈ Set.range (g3c_chartι d (a i))) H)).trans HC.symm

end HodgeLean.Foundations.Program
