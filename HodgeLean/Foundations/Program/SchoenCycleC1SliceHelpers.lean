import HodgeLean.Foundations.Program.SchoenCycleC11
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Sections over an actual projective slice
The finite etale hypotheses here concern the actual scheme pullback.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Applying projective etale splitting to the actual inverse image gives
immersed copies whose ranges exhaust that inverse image on all scheme points. -/
theorem s2e_c1_slice_sections (k : ℕ) (W B : Over (Spec ↧ℂ))
    (β : W ⟶ B)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left] [IsFinite β.left]
    [Etale (pullback.snd β.left ℓ.left)]
    [Surjective (pullback.snd β.left ℓ.left)] :
    ∃ (n : ℕ) (_ : 0 < n)
      (ι : Fin n → (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ W)),
      (∀ i, IsClosedImmersion (ι i).left) ∧
      (∀ i, ι i ≫ β = ℓ) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (ι i).left) (Set.range (ι j).left)) ∧
      (∀ w : W.left, β.left w ∈ Set.range ℓ.left ↔
        ∃ i, w ∈ Set.range (ι i).left) := by
  let P := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let T : Over (Spec ↧ℂ) :=
    Over.mk (pullback.snd β.left ℓ.left ≫ P.hom)
  let π : T ⟶ P := Over.homMk (pullback.snd β.left ℓ.left)
  let j : T ⟶ W := Over.homMk (pullback.fst β.left ℓ.left) (by
    rw [← Over.w β, ← Category.assoc, pullback.condition, Category.assoc, Over.w ℓ]
    rfl)
  have hj : j ≫ β = π ≫ ℓ := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  haveI : IsFinite π.left := inferInstanceAs (IsFinite (pullback.snd β.left ℓ.left))
  haveI : Etale π.left := inferInstanceAs (Etale (pullback.snd β.left ℓ.left))
  haveI : Surjective π.left := inferInstanceAs (Surjective (pullback.snd β.left ℓ.left))
  haveI : IsClosedImmersion j.left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst β.left ℓ.left))
  obtain ⟨n, hn, s, hs, hsec, hdis, hex⟩ :=
    s2e_chain_projective_etale_sections k T π
  let ι (i : Fin n) := s i ≫ j
  refine ⟨n, hn, ι, ?_, ?_, ?_, ?_⟩
  · intro i
    haveI := hs i
    change IsClosedImmersion ((s i).left ≫ j.left)
    infer_instance
  · intro i
    change (s i ≫ j) ≫ β = ℓ
    rw [Category.assoc, hj, ← Category.assoc, hsec i, Category.id_comp]
  · intro i l hil
    apply Set.disjoint_left.mpr
    rintro w ⟨x, hx⟩ ⟨y, hy⟩
    have hxy : (s i).left x = (s l).left y :=
      j.left.isClosedEmbedding.injective (hx.trans hy.symm)
    exact Set.disjoint_left.mp (hdis i l hil) ⟨x, rfl⟩ ⟨y, hxy.symm⟩
  · intro w
    constructor
    · intro hw
      have hw' : w ∈ Set.range j.left := by
        change w ∈ Set.range (pullback.fst β.left ℓ.left)
        rw [Scheme.Pullback.range_fst]
        exact hw
      obtain ⟨v, hv⟩ := hw'
      obtain ⟨i, x, hx⟩ := hex v
      exact ⟨i, x, (congrArg j.left hx).trans hv⟩
    · rintro ⟨i, x, rfl⟩
      refine ⟨(π.left ((s i).left x)), ?_⟩
      exact (congrArg (fun f : T ⟶ B => f.left ((s i).left x)) hj).symm

end HodgeLean.Foundations.Program
