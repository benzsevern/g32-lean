import HodgeLean.Foundations.Program.CompensationAssemblyRelativeProduct
import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupportDefs

/-!
Rational relative transport and the normalized oriented torus trace.
Source: Hatcher, Algebraic Topology, §§2.1, 3.1–3.2, Theorem 3.15.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace AlgebraicTopology.Singular.RelativeTrace

/-- Product of an embedded topological pair with a space, retaining the existing carrier.
Source: CompensationAssemblyRelativeProduct.cq_pairProduct; Hatcher §2.1.
-/
abbrev pairProduct := cq_pairProduct

example (P : TopPair.{0}) (Y : TopCat.{0}) :
    (pairProduct P Y).fst = TopCat.of (P.fst × Y) := rfl

/-- Contravariant transport through a specified isomorphism of embedded pairs.
Both component maps of the isomorphism specify homeomorphisms.
Source: Hatcher §3.1; relativeCohomologyMap.
-/
abbrev productTransport {P Q : TopPair.{0}} {Y : TopCat.{0}}
    (e : Q ≅ pairProduct P Y) (n : ℕ) := relativeCohomologyMap ℚ n e.hom

example {P Q : TopPair.{0}} {Y : TopCat.{0}} (e : Q ≅ pairProduct P Y) :
    productTransport e 1 0 = 0 := map_zero _

/-- Trace for the chosen ordered circle generators, with degree shift equal to dimension.
Source: CompensationAssemblyRelativeProduct.cq_relativeProductTorusTrace;
Hatcher §3.2, Theorem 3.15.
-/
abbrev productTorusTrace := cq_relativeProductTorusTrace

example (P : TopPair.{0}) : productTorusTrace P 1 0 0 = 0 := map_zero _

end AlgebraicTopology.Singular.RelativeTrace
