import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import stainless.collection.Cons
import org.w3c.dom.ls.LSInput

object UnionFindStainless {
  // NOTE: addr = value (in this specific case only!)
  sealed trait Node:
    val addr: BigInt

  case class Child(addr: BigInt, parent: BigInt) extends Node
  case class Root(addr: BigInt, rank: BigInt) extends Node

  // NOTE: F => F logic here: if n is not in nodes then neither is its parent
  def myParentIsInTheList(n: Node, nodes: List[Node]): Boolean = {
    if (0 <= n.addr && n.addr < nodes.size) then
      n match {
        case Child(_, p) => 0 <= p && p < nodes.size
        case _           => true
      }
    else false
  }

  def addrAndHeapMatch(n: Node, nodes: List[Node]): Boolean = {
    if 0 <= n.addr && n.addr < nodes.size then nodes(n.addr) == n
    else true
  }

  case class UF(nodes: List[Node]) {

    val parentFunc = (nodes: List[Node]) => n => myParentIsInTheList(n, nodes)
    val parentPred = parentFunc(nodes)
    val parentInv = nodes.forall(parentPred)
    require(parentInv)

    val addrFunc = (nodes: List[Node]) => n => addrAndHeapMatch(n, nodes)
    val addrPred = addrFunc(nodes)
    val addrInv = nodes.forall(addrPred)
    require(addrInv)

    // require(addrAndHeapMatch())

    def size: BigInt = nodes.size

    def contains(x: BigInt): Boolean = 0 <= x && x < size

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
        case Root(v, r) => true
        case _          => false
      }
    }

    // lemma: nodes.forall(p) && 0 <= p.addr < nodes.size + 1  => (oldNode :+ newNode).forall(p')
    def snocAppendParentInList(nodes: List[Node], newNode: Node) = {
      val multi = parentFunc(nodes)
      // require(0 <= newNode.addr && newNode.addr < nodes.size + 1)
      require(newNode.addr == nodes.size)
      require(
        nodes.forall(multi)
      ) // class invariant, should work out of the box

      // need to show that if we add an element to the list,
      // my myParentIsInTheList will work with both
      val added = (nodes :+ newNode)

      // ListSpecs.snocIsAppend(nodes, newNode)

      assert(nodes.forall(myParentIsInTheList(_, nodes)))
      // assert(nodes.forall({
      //   case Child(_, p) => 0 <= p && p < nodes.size
      //   case _           => true
      // }))

    }.ensuring(_ => {
      val newPred = parentFunc(nodes :+ newNode)
      (nodes :+ newNode).forall(newPred)
    })

    def snocAppendAddr(nodes: List[Node], newNode: Node) = {
      val multi = addrFunc(nodes)
      require(nodes.forall(multi))
      require(newNode.addr == nodes.size)
    }.ensuring(_ => {
      val newPred = addrFunc(nodes :+ newNode)
      (nodes :+ newNode).forall(newPred)
    })

    def make(): (UF, BigInt) = {
      if size == 0 then (UF(List(Root(0, BigInt(0)))), BigInt(0))
      else
        val newIdx = size
        val newNode = Root(newIdx, BigInt(0))
        val newNodes = nodes :+ newNode

        ListSpecs.snocIndex(nodes, newNode, size)
        assert(newNodes(size) == newNode)
        assert(myParentIsInTheList(newNode, newNodes))
        ListSpecs.snocIsAppend(nodes, newNode)

        // need to prove:
        // oldNodes.forall(p) && p(newNode) => (oldNode :+ newNode).forall(p)

        val newParentPred = parentFunc(newNodes)
        val newAddrPred = addrFunc(newNodes)
        // snocPartial(nodes, part, newNode)
        ListSpecs.subsetRefl(newNodes)

        snocAppendParentInList(nodes, newNode)
        snocAppendAddr(nodes, newNode)

        assert(newNodes.forall(newParentPred))
        assert(newNodes.forall(newAddrPred))

        ListSpecs.forallContained(newNodes, newParentPred, newNode)

        val newUF = UF(newNodes)

        (newUF, newIdx)
    }.ensuring { case (res, idx) =>
      res.get(idx) == Root(idx, BigInt(0))
    }

    def findBounded(x: BigInt, fuel: BigInt): Option[BigInt] = {
      require(contains(x))
      require(fuel >= 0)

      decreases(fuel)
      if (fuel == 0) None()
      else
        get(x) match {
          case Root(_, _) =>
            check(contains(x))
            check(isRoot(x))
            Some(x)
          case nx @ Child(_, p) =>
            assert(nodes.contains(nx))
            assert(parentInv)
            ListSpecs.forallContained(nodes, parentPred, nx)
            assert(myParentIsInTheList(nx, nodes))

            assert(contains(p))

            findBounded(p, fuel - 1)
        }
    }.ensuring {
      case Some(v) => isRoot(v)
      case None()  => true
    }

    def find(x: BigInt): BigInt = {
      require(contains(x))
      findBounded(x, size) match {
        case Some(value) => value
        case None()      => BigInt(-1)
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
        val (v1, rank1) = get(rx) match {
          case Root(v, r) => (v, r); case Child(v, _) => (v, BigInt(0))
        }
        val (v2, rank2) = get(ry) match {
          case Root(v, r) => (v, r); case Child(v, _) => (v, BigInt(0))
        }

        if (rank1 < rank2)
          updated(rx, Child(v2, ry))
        else if (rank1 > rank2)
          updated(ry, Child(v1, rx))
        else
          updated(ry, Child(v1, rx)).updated(rx, Root(v1, rank1 + 1))
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
