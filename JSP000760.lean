import JSP000760.Proof

/-!
# JSP-000760 / Erdős Problem 916

Thomassen proved that every finite simple graph with `n` vertices and at least
`2n - 2` edges contains a cycle together with a vertex outside that cycle
which is adjacent to three distinct vertices of the cycle.

Reference: C. Thomassen, "A minimal condition implying a special
K4-subdivision in a graph", Archiv der Mathematik 25 (1974), 210-215.
-/

namespace JSP000760

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cycle with a vertex outside it that has three distinct neighbours on it. -/
abbrev HasThreeSpokeCycle (G : SimpleGraph V) : Prop :=
  HasThreeSpokeCycleTest G

/-- The extremal form: a graph without a three-spoke cycle has at most
`2n - 3` edges. -/
theorem edge_ncard_le_of_not_hasThreeSpokeCycle (G : SimpleGraph V)
    (hV : 2 ≤ Fintype.card V) (hfree : ¬HasThreeSpokeCycle G) :
    G.edgeSet.ncard ≤ 2 * Fintype.card V - 3 := by
  classical
  by_contra hbound
  apply hfree
  letI : DecidableRel G.Adj := Classical.decRel _
  apply erdos_916_test G hV
  rw [← Set.ncard_coe_finset, coe_edgeFinset]
  omega

/-- Erdős Problem 916, proved by Thomassen in 1974. -/
theorem erdos_916 (G : SimpleGraph V)
    (hV : 2 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard ≥ 2 * Fintype.card V - 2) :
    HasThreeSpokeCycle G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  apply erdos_916_test G hV
  simpa only [← Set.ncard_coe_finset, coe_edgeFinset] using hE

/-- The exact-edge-count formulation appearing on the Erdős Problems page. -/
theorem erdos_916_exact (G : SimpleGraph V)
    (hV : 2 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard = 2 * Fintype.card V - 2) :
    HasThreeSpokeCycle G := by
  exact erdos_916 G hV hE.ge

end JSP000760
