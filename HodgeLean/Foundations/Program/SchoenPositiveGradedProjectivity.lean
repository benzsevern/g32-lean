import HodgeLean.Foundations.Program.SchoenDegreeSubalgebraProjective
import HodgeLean.Foundations.Program.SchoenDegreeSubalgebraProj
import HodgeLean.Foundations.Program.SchoenSubalgebraProjBase

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory
open scoped BigOperators
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive finite homogeneous generators construct a projective presentation of the actual Proj. -/
theorem s2_projective_of_positive_homogeneous_generators {A ι : Type}
    [CommRing A] [IsDomain A] [Fintype ι]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] (v : ι → A) (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (hv : ∀ i, v i ∈ 𝒜 (d i))
    (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) :
    IsProjective (Proj.toSpecZero 𝒜) := by
  classical
  let D := ∏ i, d i
  let c := fun i => D / d i
  let N := Fintype.card ι + 1
  let M := N * D
  have hD : 0 < D := Finset.prod_pos (fun i _ => hd i)
  have hN : Fintype.card ι < N := Nat.lt_succ_self _
  have hc : ∀ i, c i * d i = D := fun i =>
    Nat.div_mul_cancel (Finset.dvd_prod_of_mem d (Finset.mem_univ i))
  have hM : 0 < M := Nat.mul_pos (Nat.succ_pos _) hD
  have hfull : ∀ k : ℕ, ∀ a : A, a ∈ 𝒜 (k * M) → a ∈ s2_degreeSubalgebra 𝒜 M := by
    intro k a ha
    exact s2_highDegree_homogeneous_mem 𝒜 v d c hd hv hgen D N hD hc hN k ha
  let R := s2_degreeSubalgebra 𝒜 M
  let ℬ := s2_subringGradedPiece 𝒜 R.toSubring
  letI : GradedRing ℬ := s2_degreeSubalgebraGrading 𝒜 M
  let q := s2_degreeSubalgebraProjMap 𝒜 M hM hfull
  haveI : IsIso q := s2_degreeSubalgebraProjMap_isIso 𝒜 M hM hfull
  have ht := s2_degreeSubalgebra_projective 𝒜 v d hd hv hgen M hM
  obtain ⟨P⟩ := ht.nonempty_presentation
  letI := P.isClosedImmersion
  refine ⟨⟨⟨P.ambientDimension, q ≫ P.immersion, ?_⟩⟩⟩
  rw [Category.assoc, P.immersion_toBase]
  exact s2_subalgebraProjMap_toSpecZero 𝒜 R
    (s2_degreeSubalgebra_irrelevant_le_radical 𝒜 M hM hfull)

/-- A graded domain of finite type over its actual degree zero has a projective Proj structure map. -/
theorem s2_projective_toSpecZero_of_finiteType {A : Type} [CommRing A] [IsDomain A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsProjective (Proj.toSpecZero 𝒜) := by
  classical
  obtain ⟨s, hs, hhom⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose d hd hv using (fun i : s => hhom i.val i.property)
  exact s2_projective_of_positive_homogeneous_generators 𝒜
    (fun i : s => i.val) d (fun i => Nat.pos_of_ne_zero (hd i)) hv
    (by
      have hrange : Set.range (fun i : s => i.val) = (s : Set A) := by
        ext a
        exact ⟨fun ⟨i, hi⟩ => hi ▸ i.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
      rw [hrange]
      exact hs)

end HodgeLean.Foundations.Program
