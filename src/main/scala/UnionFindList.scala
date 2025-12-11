import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._


object UnionFindStainless {

  sealed trait Node
  case class Child(parent: BigInt) extends Node
  case class Root(rank: BigInt) extends Node

  def myParentIsInTheList(x: Node, nodes: List[Node]): Boolean = {
      //require(contains(x))
      x match {
        case Child(p) => 0 <= p && p < nodes.size
        case _ => true
      }
    }

  case class UF(nodes: List[Node]) {
    require(nodes.forall(n => myParentIsInTheList(n, nodes)))
    /* require(size >= 0) */

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

    def isRoot(x: BigInt): Boolean = {
      require(contains(x))
      get(x) match {
        case Root(r) => true
        case _ => false
      }
    }

    def make(): (UF, BigInt) = {
      val newIdx = size
      val newNode = Root(BigInt(0))
      val newNodes = nodes :+ newNode
      ListSpecs.snocIndex(nodes, newNode, size)
      assert(newNodes(size) == newNode)
      assert(myParentIsInTheList(newNode, newNodes))
      (UF(newNodes), newIdx)
    }.ensuring { case (res, idx) =>
      res.get(idx) == Root(BigInt(0))
    }

    def findBounded(x: BigInt, fuel: BigInt): Option[BigInt] = {
      require(contains(x))
      require(fuel >= 0)
      require(nodes.forall(n => myParentIsInTheList(n, nodes)))

      decreases(fuel)
      if (fuel == 0) None()
      else get(x) match {
        case Root(_) => 
          check(contains(x))
          check(isRoot(x))
          Some(x)
        case nx @ Child(p) =>
          assert(nodes.contains(nx))
          assert(p < nodes.size)
          assert(myParentIsInTheList(nx, nodes))
          assert(contains(p))
          findBounded(p, fuel - 1)
          /* if (contains(p)) findBounded(p, fuel - 1)
          else
            assert(p < size)
            x  // invalid parent, treat as root */
      }
    }.ensuring(y => 
      y match{
        case Some(x) => isRoot(x)
        case _ => true
      }
    )

    def find(x: BigInt): BigInt = {
      require(contains(x))
      findBounded(x, size) match {
        case Some(value) => value
        case None() => BigInt(-1)
      }
    }.ensuring(y => !contains(y) || isRoot(y))

    def equiv(x: BigInt, y: BigInt): Boolean = {
      require(contains(x) && contains(y))
      find(x) == find(y)
    }

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

    def union(x: BigInt, y: BigInt): UF = {
      require(contains(x) && contains(y))
      link(find(x), find(y))
    }
  }

  // def empty: UF = UF(Nil[Node]())


  def idempotentLemma(uf: UF, x: BigInt): Boolean = {
    require(uf.contains(x))
    val r = uf.find(x)
    !uf.contains(r) || uf.find(r) == r
  }.holds

}


