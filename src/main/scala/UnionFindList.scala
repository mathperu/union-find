import stainless.lang._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._


object UnionFindStainless {

  sealed trait Node
  case class Child(parent: BigInt) extends Node
  case class Root(rank: BigInt) extends Node

  case class UF(nodes: List[Node]) {
    require(nodes.forall(n => myParentIsInTheList(n)))
    require(size >= 0)

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


    def myParentIsInTheList(x: BigInt): Boolean = {
      require(contains(x))
      get(x) match {
        case Child(p) => contains(p)
        case _ => true
      }
    }.holds

    def make(): (UF, BigInt) = {
      val newIdx = size
      val newNodes = nodes :+ Root(BigInt(0))
      ListSpecs.snocIndex(nodes, Root(BigInt(0)), size)
      assert(newNodes(size) == Root(BigInt(0)))
      (UF(newNodes), newIdx)
    }.ensuring { case (res, idx) =>
      res.get(idx) == Root(BigInt(0))
    }

    def findBounded(x: BigInt, fuel: BigInt): BigInt = {
      require(contains(x))
      require(fuel >= 0)
      decreases(fuel)
      if (fuel == 0) x
      else get(x) match {
        case Root(_) => x
        case Child(p) =>
          if (contains(p)) findBounded(p, fuel - 1)
          else
            assert(p < size)
            x  // invalid parent, treat as root
      }
    }.ensuring(y => isRoot(y))

    def find(x: BigInt): BigInt = {
      require(contains(x))
      findBounded(x, size)
    }.ensuring(y => isRoot(y))

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


