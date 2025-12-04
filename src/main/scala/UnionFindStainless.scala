import stainless.lang._
import stainless.collection._

/**
 * Union-Find implementation using Stainless-compatible types.
 * WITH PATH COMPRESSION.
 * 
 * Elements are represented as BigInt indices (0, 1, 2, ...).
 * The data structure stores nodes in a List, where index i corresponds to element i.
 */

object UnionFindStainless {

  sealed trait Node
  case class Child(parent: BigInt) extends Node
  case class Root(rank: BigInt) extends Node

  case class UF(nodes: List[Node]) {

    def size: BigInt = nodes.size

    def contains(x: BigInt): Boolean = x >= BigInt(0) && x < size

    def get(x: BigInt): Node = {
      require(contains(x))
      nodes(x)
    }

    def updated(x: BigInt, n: Node): UF = {
      require(contains(x))
      UF(nodes.updated(x, n))
    }.ensuring(res => res.size == size)

    // ===========================================================================
    // OPERATION: make
    // Adds a new element as its own root, returns (new UF, new element's index)
    // ===========================================================================
    def make(): (UF, BigInt) = {
      val newIdx = size
      (UF(nodes :+ Root(BigInt(0))), newIdx)
    }

    // ===========================================================================
    // OPERATION: find WITH PATH COMPRESSION
    // Returns (updated UF, root index)
    // After find, x points directly to its root
    // ===========================================================================
    def findBounded(x: BigInt, fuel: BigInt): (UF, BigInt) = {
      require(contains(x))
      require(fuel >= BigInt(0))
      decreases(fuel)
      if (fuel == BigInt(0)) (this, x)
      else get(x) match {
        case Root(_) => (this, x)
        case Child(p) =>
          if (contains(p)) {
            val (uf1, root) = findBounded(p, fuel - BigInt(1))
            if (p == root) {
              // p is already the root, no compression needed
              (uf1, root)
            } else {
              // Path compression: point x directly to root
              (uf1.updated(x, Child(root)), root)
            }
          } else (this, x)  // invalid parent, treat as root
      }
    }.ensuring(res => res._1.size == size && res._1.contains(res._2))

    def find(x: BigInt): (UF, BigInt) = {
      require(contains(x))
      findBounded(x, size)
    }.ensuring(res => res._1.size == size && res._1.contains(res._2))

    // ===========================================================================
    // OPERATION: equiv
    // Returns true iff x and y have the same representative
    // ===========================================================================
    def equiv(x: BigInt, y: BigInt): Boolean = {
      require(contains(x) && contains(y))
      val (uf1, rx) = find(x)
      val (_, ry) = uf1.find(y)
      rx == ry
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
          updated(ry, Child(rx)).updated(rx, Root(rank1 + BigInt(1)))
      }
    }

    // ===========================================================================
    // OPERATION: union
    // Merges the equivalence classes of x and y
    // ===========================================================================
    def union(x: BigInt, y: BigInt): UF = {
      require(contains(x) && contains(y))
      val (uf1, rx) = find(x)
      val (uf2, ry) = uf1.find(y)
      uf2.link(rx, ry)
    }
  }

  def empty: UF = UF(Nil[Node]())
}
