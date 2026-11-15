import HodgeLean.Foundations.Program.SchoenCycleCoefficientCharts
import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

/-! # Marked block sets and their exact coefficient products -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical BigOperators
namespace HodgeLean.Foundations.Program

/-- The indices of one collision block are exactly the coordinates equal to its marked point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, printed pp. 13–14;
Lemma 2.4, printed p. 15. -/
theorem s2e_mixed_block_indices
    (Z : Over (Spec ↧ℂ)) (n : ℕ) (x : ComplexPoint (g3_power Z n))
    (b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (p : Fin b → ComplexPoint Z) (hp : Function.Injective p)
    (hx : ∀ a i, Point.map (g3_proj Z n (ι ⟨a, i⟩)) x = p a) (a : Fin b) :
    ∀ i, i ∈ Finset.univ.image (fun j : Fin (m a) => ι ⟨a, j⟩) ↔
      Point.map (g3_proj Z n i) x = p a := by
  intro i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hx a j
  · intro hi
    obtain ⟨⟨l, j⟩, rfl⟩ := ι.surjective i
    have hla : l = a := hp ((hx l j).symm.trans hi)
    subst l
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- The signed block constant coefficient is exactly its coordinate product over the retained index set.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Macdonald, Symmetric Functions and Hall Polynomials, Chapter I, §2. -/
theorem s2e_mixed_block_constant_product
    (n b : ℕ) (m : Fin b → ℕ) (ι : (Σ a, Fin (m a)) ≃ Fin n)
    (a : Fin b) (z : Fin n → ℂ) :
    aeval (fun j : Fin (m a) => z (ι ⟨a, j⟩)) (esymm (Fin (m a)) ℂ (m a)) =
      ∏ i ∈ Finset.univ.image (fun j : Fin (m a) => ι ⟨a, j⟩), z i := by
  have hinj : Function.Injective (fun j : Fin (m a) => ι ⟨a, j⟩) := by
    intro i j hij
    exact eq_of_heq ((Sigma.mk.inj_iff.mp (ι.injective hij)).2)
  have htop := s2e_top_elementary_coefficient (Fin (m a)) ℂ
  simp only [Fintype.card_fin] at htop
  rw [htop]
  simp only [map_prod, aeval_X]
  exact (Finset.prod_image (fun i _ j _ hij => hinj hij)).symm

end HodgeLean.Foundations.Program
