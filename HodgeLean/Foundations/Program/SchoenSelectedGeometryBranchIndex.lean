import HodgeLean.Foundations.Program.G32SelectedRealizationExponentWeights

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Papers
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Finite local monodromy indices whose character value gives a residual branch. -/
def s0_BranchIndex {G : Type} [Group G] [Finite G] {m n : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : Fin n → G) :=
  {a : Σ i : Fin n, Quotient (MulAction.orbitRel (Subgroup.zpowers (g i)) (G ⧸ H)) //
    χ (papersLocalMonodromy H (g a.1) a.2) ≠ 1}

instance s0_branchIndex_finite {G : Type} [Group G] [Finite G] {m n : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : Fin n → G) :
    Finite (s0_BranchIndex H χ g) := by unfold s0_BranchIndex; infer_instance

/-- The character value attached to a residual branch index. -/
def s0_branchLabel {G : Type} [Group G] [Finite G] {m n : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : Fin n → G)
    (a : s0_BranchIndex H χ g) : ZMod m :=
  Multiplicative.toAdd (χ (papersLocalMonodromy H (g a.val.1) a.val.2))

/-- Summing branch labels agrees with the local exponent multisets. -/
theorem s0_branchIndex_weight {G : Type} [Group G] [Finite G] {m n : ℕ}
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : Fin n → G)
    (w : ZMod m → ℝ) (hw : w 0 = 0) :
    letI := Fintype.ofFinite (s0_BranchIndex H χ g)
    ∑ a : s0_BranchIndex H χ g, w (s0_branchLabel H χ g a) =
      ∑ i, ((papersExps H χ (g i)).map w).sum := by
  classical
  let Q := Σ i : Fin n, Quotient (MulAction.orbitRel (Subgroup.zpowers (g i)) (G ⧸ H))
  letI : ∀ i, Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (g i)) (G ⧸ H))) :=
    fun _ ↦ Fintype.ofFinite _
  letI := Fintype.ofFinite (s0_BranchIndex H χ g)
  let v : Q → ZMod m := fun a ↦ Multiplicative.toAdd (χ (papersLocalMonodromy H (g a.1) a.2))
  letI : Fintype {a : Q // χ (papersLocalMonodromy H (g a.1) a.2) ≠ 1} :=
    Fintype.ofFinite (s0_BranchIndex H χ g)
  have he : ∑ a : s0_BranchIndex H χ g, w (s0_branchLabel H χ g a) =
      ∑ a : Q, w (v a) := by
    change (∑ a : {a : Q // χ (papersLocalMonodromy H (g a.1) a.2) ≠ 1}, w (v a.val)) = _
    rw [← Finset.sum_subtype (p := fun a : Q ↦ χ (papersLocalMonodromy H (g a.1) a.2) ≠ 1)
      (Finset.univ.filter fun a : Q ↦ χ (papersLocalMonodromy H (g a.1) a.2) ≠ 1)
      (by simp) (fun a ↦ w (v a))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · rfl
    · have h : χ (papersLocalMonodromy H (g a.1) a.2) = 1 := not_ne_iff.mp ha
      simp [v, h, hw]
  rw [he, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (g32y_papers_local_exponent_weight H χ (g i) w hw).symm

#print axioms s0_branchIndex_weight
end HodgeLean.Foundations.Program
