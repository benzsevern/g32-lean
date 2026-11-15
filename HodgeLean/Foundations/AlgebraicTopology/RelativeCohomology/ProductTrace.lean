import HodgeLean.Foundations.AlgebraicTopology.RelativeCohomology.Proofs

/-!
Rational relative transport and the normalized oriented torus trace.
Source: Hatcher, Algebraic Topology, §§2.1, 3.1–3.2, Theorem 3.15.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.RelativeTrace

/-- Forget naturality.
Source: Hatcher §3.1; CompensationAssemblyRelativeProduct.cq_relativeToAbsolute_naturality.
-/
theorem forget_naturality {P Q : TopPair.{0}} (a : P ⟶ Q) (n : ℕ)
    (c : RelativeCohomology ℚ Q n) :
    relativeCohomologyToAbsolute ℚ P n (relativeCohomologyMap ℚ n a c) =
      cohomologyMap ℚ n (TopPair.Hom.fst a) (relativeCohomologyToAbsolute ℚ Q n c) := forget_naturality_aux a n c

example {P Q : TopPair.{0}} (a : P ⟶ Q) :
    relativeCohomologyToAbsolute ℚ P 1 (relativeCohomologyMap ℚ 1 a 0) =
      cohomologyMap ℚ 1 (TopPair.Hom.fst a) (relativeCohomologyToAbsolute ℚ Q 1 0) := by
  simp only [map_zero]

/-- Product transport inverse.
Source: Hatcher §3.1, functoriality; CompensationAssemblyRelativeProduct.cq_pairProduct.
-/
theorem product_transport_inverse {P Q : TopPair.{0}} {Y : TopCat.{0}}
    (e : Q ≅ pairProduct P Y) (n : ℕ) (c : RelativeCohomology ℚ Q n) :
    productTransport e n (relativeCohomologyMap ℚ n e.inv c) = c := product_transport_inverse_aux e n c

example {P Q : TopPair.{0}} {Y : TopCat.{0}} (e : Q ≅ pairProduct P Y) :
    productTransport e 1 (relativeCohomologyMap ℚ 1 e.inv 0) = 0 := by
  simp only [map_zero]

/-- Product transport forget.
Source: Hatcher §§2.1, 3.1; CompensationAssemblyRelativeProduct.cq_relativeToAbsolute_naturality.
-/
theorem product_transport_forget {P Q : TopPair.{0}} {Y : TopCat.{0}}
    (e : Q ≅ pairProduct P Y) (n : ℕ)
    (c : RelativeCohomology ℚ (pairProduct P Y) n) :
    relativeCohomologyToAbsolute ℚ Q n (productTransport e n c) =
      cohomologyMap ℚ n (TopPair.Hom.fst e.hom)
        (relativeCohomologyToAbsolute ℚ (pairProduct P Y) n c) := product_transport_forget_aux e n c

example {P Q : TopPair.{0}} {Y : TopCat.{0}} (e : Q ≅ pairProduct P Y) :
    relativeCohomologyToAbsolute ℚ Q 1 (productTransport e 1 0) = 0 := by
  simp only [map_zero]

/-- Tower trace forget.
Source: Hatcher §3.2, Theorem 3.15; CompensationAssemblyRelativeTorus.cq_relativeTorusTrace_absolute.
-/
theorem tower_trace_forget (P : TopPair.{0}) (k n : ℕ)
    (c : RelativeCohomology ℚ (cq_pairCircleTower P k) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (cq_relativeTorusTrace P k n c) =
      cq_torusTrace P.fst k n
        (relativeCohomologyToAbsolute ℚ (cq_pairCircleTower P k) (n + k) c) := tower_trace_forget_aux P k n c

example (P : TopPair.{0}) :
    relativeCohomologyToAbsolute ℚ P 0 (cq_relativeTorusTrace P 1 0 0) = 0 := by
  simp only [map_zero]

/-- Product trace forget.
Source: Hatcher §3.2, Theorem 3.15; CompensationAssemblyRelativeProduct.cq_relativeProductTorusTrace_absolute.
-/
theorem product_trace_forget (P : TopPair.{0}) (k n : ℕ)
    (c : RelativeCohomology ℚ (pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k)) :
    relativeCohomologyToAbsolute ℚ P n (productTorusTrace P k n c) =
      cq_productTorusTrace P.fst k n
        (relativeCohomologyToAbsolute ℚ
          (pairProduct P (TopCat.of (UnitAddTorus (Fin k)))) (n + k) c) := product_trace_forget_aux P k n c

example (P : TopPair.{0}) :
    relativeCohomologyToAbsolute ℚ P 0 (productTorusTrace P 1 0 0) = 0 := by
  simp only [map_zero]

end AlgebraicTopology.Singular.RelativeTrace
