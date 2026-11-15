import HodgeLean.Foundations.Program.SchoenGradedInvariants

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The degree piece in a subring is the inverse image of the ambient degree piece. -/
def s2_subringGradedPiece {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) (R : Subring A) (n : ℕ) : AddSubgroup R :=
  (𝒜 n).comap R.subtype.toAddMonoidHom

/-- The inherited subring degree pieces preserve the unit and graded multiplication. -/
instance s2_subringGradedPiece_gradedMonoid {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A) :
    SetLike.GradedMonoid (s2_subringGradedPiece 𝒜 R) where
  one_mem := SetLike.one_mem_graded 𝒜
  mul_mem i j a b ha hb := by
    change (a.val * b.val) ∈ 𝒜 (i + j)
    exact SetLike.mul_mem_graded (show a.val ∈ 𝒜 i from ha) (show b.val ∈ 𝒜 j from hb)

/-- Recomposing inherited subring degree pieces is injective. -/
theorem s2_subringGradedPiece_recompose_injective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A) :
    Function.Injective (DirectSum.coeAddMonoidHom (s2_subringGradedPiece 𝒜 R)) := by
  let f (n : ℕ) : s2_subringGradedPiece 𝒜 R n →+ 𝒜 n :=
    { toFun := fun a => ⟨a.val.val, a.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let F := DirectSum.map f
  have hF : Function.Injective F := (DirectSum.map_injective f).mpr (fun n => by
    intro a b hab
    have hval : a.val.val = b.val.val := congrArg (fun z : 𝒜 n => (z : A)) hab
    exact Subtype.ext (Subtype.ext hval))
  have hcoe : (DirectSum.coeAddMonoidHom 𝒜).comp F =
      R.subtype.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom (s2_subringGradedPiece 𝒜 R)) := by
    apply DirectSum.addHom_ext
    intro n a
    simp only [AddMonoidHom.comp_apply, F, DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  intro a b hab
  apply hF
  apply (DirectSum.Decomposition.isInternal 𝒜).injective
  exact (DFunLike.congr_fun hcoe a).trans
    ((congrArg (fun r : R => (r : A)) hab).trans (DFunLike.congr_fun hcoe b).symm)

/-- Homogeneity of a subring makes recomposition of its inherited degree pieces surjective. -/
theorem s2_subringGradedPiece_recompose_surjective {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    (hR : ∀ n, ∀ a ∈ R, (DirectSum.decompose 𝒜 a n : A) ∈ R) :
    Function.Surjective (DirectSum.coeAddMonoidHom (s2_subringGradedPiece 𝒜 R)) := by
  classical
  intro a
  let z (n : ℕ) : s2_subringGradedPiece 𝒜 R n :=
    ⟨⟨(DirectSum.decompose 𝒜 a.val n : A), hR n a.val a.property⟩,
      (DirectSum.decompose 𝒜 a.val n).property⟩
  refine ⟨∑ n ∈ (DirectSum.decompose 𝒜 a.val).support,
    DirectSum.of (fun n => s2_subringGradedPiece 𝒜 R n) n (z n), ?_⟩
  apply Subtype.ext
  change R.subtype.toAddMonoidHom (DirectSum.coeAddMonoidHom (s2_subringGradedPiece 𝒜 R)
    (∑ n ∈ (DirectSum.decompose 𝒜 a.val).support,
      DirectSum.of (fun n => s2_subringGradedPiece 𝒜 R n) n (z n))) = a.val
  simp only [map_sum, DirectSum.coeAddMonoidHom_of]
  exact DirectSum.sum_support_decompose 𝒜 a.val

/-- A homogeneous subring carries the grading inherited from its ambient ring. -/
def s2_homogeneousSubringGrading {A : Type} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (R : Subring A)
    (hR : ∀ n, ∀ a ∈ R, (DirectSum.decompose 𝒜 a n : A) ∈ R) :
    GradedRing (s2_subringGradedPiece 𝒜 R) where
  toGradedMonoid := s2_subringGradedPiece_gradedMonoid 𝒜 R
  toDecomposition := (show DirectSum.IsInternal (s2_subringGradedPiece 𝒜 R) from
    ⟨s2_subringGradedPiece_recompose_injective 𝒜 R,
      s2_subringGradedPiece_recompose_surjective 𝒜 R hR⟩).chooseDecomposition

end HodgeLean.Foundations.Program
