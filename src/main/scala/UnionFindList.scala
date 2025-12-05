import stainless.lang._
import stainless.collection._
import stainless.annotation._

/**
 * Formal Specifications for Union-Find (Stainless)
 * =================================================
 * Based on: "Verifying the Correctness and Amortized Complexity of a Union-Find
 * Implementation in Separation Logic with Time Credits" (Charguéraud & Pottier)
 *
 * SIMPLIFIED: We focus on functional correctness only, NOT complexity.
 * Therefore we use: UF D R (no capacity N, no time credits)
 *
 * Where:
 *   D = domain (set of elements created via make)
 *   R = representative function (maps each element to its root)
 *
 * Key properties (UF_properties):
 *   1. ∀x, R(R(x)) = R(x)             -- R is idempotent
 *   2. x ∈ D → R(x) ∈ D               -- representatives are in the domain
 *   3. x ∉ D → R(x) = x               -- elements outside domain are their own rep
 */

object UnionFindStainless {

  // ===========================================================================
  // Data Types - Using BigInt indices into a List (array-like)
  // This avoids the map lookup termination issues
  // ===========================================================================

  sealed trait Node
  case class Child(parent: BigInt) extends Node
  case class Root(rank: BigInt) extends Node

  // UF stores nodes at indices 0..size-1
  // An element x is in domain iff 0 <= x < nodes.size
  case class UF(nodes: List[Node]) {

    def size: BigInt = nodes.size

    def contains(x: BigInt): Boolean = x >= 0 && x < size

    def get(x: BigInt): Node = {
      require(contains(x))
      nodes(x)
    }

    def updated(x: BigInt, n: Node): UF = {
      require(contains(x))
      UF(nodes.updated(x, n))
    }

    // ===========================================================================
    // OPERATION: make
    // Spec: Adds a new element at index = current size, as its own root
    // ===========================================================================
    def make(): (UF, BigInt) = {
      val newIdx = size
      (UF(nodes :+ Root(BigInt(0))), newIdx)
    }.ensuring { case (res, idx) =>
      res.contains(idx) &&
      res.size == size + 1 &&
      res.get(idx) == Root(BigInt(0))
    }

    // ===========================================================================
    // OPERATION: find
    // Spec: Returns R(x) - the root of x
    // Uses fuel/depth bound for termination proof
    // ===========================================================================
    def findBounded(x: BigInt, fuel: BigInt): BigInt = {
      require(contains(x))
      require(fuel >= 0)
      decreases(fuel)
      if (fuel == 0) x
      else get(x) match {
        case Root(_) => x
        case Child(p) =>
          if (contains(p)) findBounded(p, fuel - 1)
          else x  // invalid parent, treat as root
      }
    }

    def find(x: BigInt): BigInt = {
      require(contains(x))
      findBounded(x, size)  // size is max depth
    }

    // ===========================================================================
    // OPERATION: equiv
    // Spec: Returns true ↔ R(x) = R(y)
    // ===========================================================================
    def equiv(x: BigInt, y: BigInt): Boolean = {
      require(contains(x) && contains(y))
      find(x) == find(y)
    }

    // ===========================================================================
    // OPERATION: link (merge two roots by rank)
    // ===========================================================================
    def link(rx: BigInt, ry: BigInt): UF = {
      require(contains(rx) && contains(ry))
      if (rx == ry) this
      else {
        val rank1 = get(rx) match { case Root(r) => r; case _ => BigInt(0) }
        val rank2 = get(ry) match { case Root(r) => r; case _ => BigInt(0) }

        if (rank1 < rank2)
          updated(rx, Child(ry))
        else if (rank1 > rank2)
          updated(ry, Child(rx))
        else
          updated(ry, Child(rx)).updated(rx, Root(rank1 + 1))
      }
    }

    // ===========================================================================
    // OPERATION: union
    // Spec: Merges equivalence classes of x and y
    // ===========================================================================
    def union(x: BigInt, y: BigInt): UF = {
      require(contains(x) && contains(y))
      link(find(x), find(y))
    }
  }

  // ===========================================================================
  // Empty UF
  // ===========================================================================
  def empty: UF = UF(Nil[Node]())

  // ===========================================================================
  // Lemmas / Properties (to be proven)
  // ===========================================================================

  // Property: R is idempotent (find(find(x)) == find(x))
  def idempotentLemma(uf: UF, x: BigInt): Boolean = {
    require(uf.contains(x))
    val r = uf.find(x)
    !uf.contains(r) || uf.find(r) == r
  }.holds

}


