package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import stainless.annotation._

import ourlistspecs.OurListSpecs
import InvariantsHelpers._

object UnionFindList {

  sealed trait Node[T] {
    val addr: BigInt
    val rank: BigInt
    val value: T

    require(addr >= 0)
    require(rank >= 0)
  }

  case class Child[T](addr: BigInt, value: T, rank: BigInt, parentAddr: BigInt)
      extends Node[T] {
    require(addr != parentAddr)
  }
  case class Root[T](addr: BigInt, value: T, rank: BigInt) extends Node[T]

  // required to instantiate dist >= 0 proofs
  def instantiateRank[T](n: Node[T]): Unit = {}.ensuring(n.rank >= 0)

  def isRoot[T](n: Node[T]): Boolean = {
    n match {
      case Root(a, v, r) => true
      case _             => false
    }
  }

  def hasRoot[T](heap: List[Node[T]]): Boolean = {
    decreases(heap)

    heap match
      case Cons(h, t) =>
        h match
          case Child(_, _, _, _) => false || hasRoot(t)
          case Root(_, _, _)     => true
      case Nil() => false
  }

  case class UF[T](heap: List[Node[T]]) {

    val addresses: List[BigInt] = heap.map(n => n.addr)
    val size: BigInt = heap.size
    val domain: List[T] = heap.map(n => n.value)

    // Invariant I: parent address is always in the heap
    val parentFuncOnHeap = parentFunc(heap)
    require(heap.forall(parentFuncOnHeap))

    // Invariant II: address matches position in heap
    val addrFuncOnHeap = addrFunc(heap)
    require(heap.forall(addrFuncOnHeap))

    // Invariant III: addresses are correct
    require(addresses == List.range(0, size))

    // Invariant IV: rank of a node is less than or equal to its parent's rank
    val rankFuncOnHeap = rankFunc(heap)
    val rankInv = heap.forall(rankFuncOnHeap)
    require(heap.forall(rankFuncOnHeap))

    // Invariant VI
    val boundedRankFuncOnHeap = boundedRankFunc(heap)
    require(heap.forall(boundedRankFuncOnHeap))

    def isValidAddr(addr: BigInt): Boolean =
      0 <= addr && addr < size

    @inline
    def nodeAt(addr: BigInt): Node[T] = {
      require(isValidAddr(addr))
      heap(addr)
    }.ensuring(n => heap.contains(n))

    def getParentAddr(n: Node[T]): BigInt =
      n match {
        case Child(addr, value, _, parentAddr) => parentAddr
        case Root(addr, value, rank)           => addr
      }

    private def set(addr: BigInt, n: Node[T]): UF[T] =
      require(isValidAddr(addr))
      require(isValidAddr(n.addr))
      require(n.addr == addr)
      // for invariant I
      require(parentFuncOnHeap(n))
      // for invariant IV
      require(rankFuncOnHeap(n))
      require(isRoot(heap(addr)))
      require(heap(addr).rank <= n.rank)
      require(isRoot(n) || heap(addr).rank == n.rank)
      // for invariant VI
      require(boundedRankFuncOnHeap(n))
      require(!isRoot(n) || isRoot(heap(addr)))

      val newHeap = heap.updated(addr, n)
      val prevNode = heap(addr)

      // invariant III
      OurListSpecs.mapAtIndex(heap, addr, _.addr)
      OurListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(0, heap.size, addr)
      OurListSpecs.mapUpdate(heap, addr, n, _.addr)

      // Invariant I and II
      rangeInvImpliesAddrInv(newHeap)
      parentInvUpdate(heap, addr, n)

      // Invariant IV
      rankInvUpdate(heap, addr, n)
      assert(newHeap.forall(rankFunc(newHeap)))

      // Invariant VI
      boundedRankUpdate(heap, addr, n)

      // Invariant II
      rangeInvImpliesAddrInv(newHeap)
      // Invariant I
      parentInvUpdate(heap, addr, n)

      UF(newHeap)

    def nodeAtIsRoot(addr: BigInt): Boolean = {
      if (isValidAddr(addr)) then isRoot(nodeAt(addr))
      else true
    }

    def rankIs(n: Node[T], x: BigInt): Boolean = {
      n match {
        case Child(addr, value, rank, parentAddr) => rank == x
        case Root(addr, value, rank)              => rank == x
      }

    }

    // invariant timeout in stainless
    def make(value: T): (UF[T], Node[T]) = {
      require(!domain.contains(value))

      val addr = size
      val newNode = Root(addr, value, 0)
      val newHeap = heap :+ newNode

      // Invariant I: parent address is always in the heap
      assert(parentFunc(newHeap)(newNode))
      parentInvAppend(heap, newNode)

      // Invariant II: address matches position in head
      OurListSpecs.appendedElementIsAtIndexOldSize(heap, newNode)
      assert(addrFunc(newHeap)(newNode))
      addrInvAppend(heap, newNode)

      // Invariant III: addresses are correct
      OurListSpecs.rangeAppend(0, heap.size)
      OurListSpecs.mapDistributesOverAppend(heap, newNode, _.addr)

      // Invariant IV: rank of a node is less than or equal to its parent's rank
      assert(rankFunc(newHeap)(newNode))
      (!heap.contains(newNode)) because {
        OurListSpecs.mapContains(
          heap,
          n => n.value,
          newNode
        )
        trivial
      }
      rankInvAppend(heap, newNode)

      // Invariant VI
      assert(boundedRankFunc(newHeap)(newNode))
      boundedRankAppend(heap, newNode)

      (UF(newHeap), newNode)
    }

    // helper to prove unionMergedTheSets
    def buildParentChain(addr: BigInt): List[Node[T]] = {
      require(isValidAddr(addr))

      // preconds for nodeAt(addr).rank enable proof for non-negative measure
      def parentChainInner(addr: BigInt): List[Node[T]] = {
        require(isValidAddr(addr))
        val f = nodeAt(addr)
        require(f.rank >= 0)
        require(f.rank <= heap.size)
        decreases(heap.size - f.rank)

        nodeAt(addr) match {
          case c @ Child(addr, value, dist, parentAddr) => {
            ListSpecs.forallContained(heap, parentFuncOnHeap, f)
            val parent = nodeAt(parentAddr)
            check(rankInv)

            ListSpecs.forallContained(heap, rankFuncOnHeap, f)
            instantiateRank(parent)
            check(parent.rank >= 0)

            ListSpecs.forallContained(heap, boundedRankFuncOnHeap, parent)
            OurListSpecs.weakenBoundOnListSize(
              heap,
              e => !isRoot(e),
              parent.rank
            )
            check(parent.rank <= size)

            // TODO fix here !
            val chain = parentChainInner(parentAddr)
            // need to re-check here after recursive call
            check(chain.head.addr == find(addr))
            OurListSpecs.snocMaintainsPredOnHead(
              chain,
              c,
              _.addr == find(addr)
            )
            check((chain :+ c).head.addr == find(addr))
            chain :+ c
          }
          case r @ Root(addr, value, rank) => {
            instantiateRank(r)
            ListSpecs.forallContained(heap, addrFuncOnHeap, r)
            check(r.addr == find(addr)) // this passes
            val li = List[Node[T]](r)
            check(li.head.addr == find(addr))
            li
          }
        }
      }.ensuring(l =>
        nodeAtIsRoot(l.head.addr) && isValidAddr(l.head.addr) &&
          nodeAt(addr).rank <= nodeAt(l.head.addr).rank &&
          l.head.addr == find(addr)
      )

      // Invoke invariants on Node[T]
      val f = nodeAt(addr)
      instantiateRank(f)
      ListSpecs.forallContained(heap, boundedRankFuncOnHeap, f)
      OurListSpecs.weakenBoundOnListSize(heap, e => !isRoot(e), f.rank)

      val chain = parentChainInner(addr)
      assert(chain.head.addr == find(addr))
      chain
    }.ensuring(l =>
      nodeAtIsRoot(l.head.addr) && isValidAddr(l.head.addr)
        && nodeAt(addr).rank <= nodeAt(l.head.addr).rank
        && l.head.addr == find(addr)
    )

    // no path compression
    // provide address and finds parent's address
    def find(addr: BigInt): BigInt = {
      require(isValidAddr(addr))

      // preconds for nodeAt(addr).rank enable proof for non-negative measure
      def findInner(addr: BigInt): BigInt = {
        require(isValidAddr(addr))
        val f = nodeAt(addr)
        require(f.rank >= 0)
        require(f.rank <= heap.size)
        decreases(heap.size - f.rank)

        nodeAt(addr) match {
          case Child(addr, value, dist, parentAddr) => {
            ListSpecs.forallContained(heap, parentFuncOnHeap, f)
            val parent = nodeAt(parentAddr)
            check(rankInv)

            ListSpecs.forallContained(heap, rankFuncOnHeap, f)
            instantiateRank(parent)
            check(parent.rank >= 0)

            ListSpecs.forallContained(heap, boundedRankFuncOnHeap, parent)
            OurListSpecs.weakenBoundOnListSize(
              heap,
              e => !isRoot(e),
              parent.rank
            )
            check(parent.rank <= size)

            findInner(parentAddr)
          }
          case r @ Root(addr, value, rank) => {
            instantiateRank(r)
            ListSpecs.forallContained(heap, addrFuncOnHeap, r)
            addr
          }
        }
      }.ensuring(y =>
        nodeAtIsRoot(y) && isValidAddr(y) && nodeAt(addr).rank <= nodeAt(y).rank
      )

      // Invoke invariants on Node[T]
      val f = nodeAt(addr)
      instantiateRank(f)
      ListSpecs.forallContained(heap, boundedRankFuncOnHeap, f)
      OurListSpecs.weakenBoundOnListSize(heap, e => !isRoot(e), f.rank)

      findInner(addr)
    }.ensuring(y =>
      nodeAtIsRoot(y) && isValidAddr(y) && nodeAt(addr).rank <= nodeAt(y).rank
    )

    def equiv(a1: BigInt, a2: BigInt): Boolean = {
      require(isValidAddr(a1))
      require(isValidAddr(a2))
      find(a1) == find(a2)
    }

    def link(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
      require(
        isValidAddr(a1) && isValidAddr(a2) && nodeAtIsRoot(a1) && nodeAtIsRoot(
          a2
        )
      )

      val n1 = nodeAt(a1)
      val n2 = nodeAt(a2)

      instantiateRank(n1)
      instantiateRank(n2)

      ListSpecs.forallContained(heap, boundedRankFuncOnHeap, n1)
      ListSpecs.forallContained(heap, boundedRankFuncOnHeap, n2)

      if a1 == a2 then (this, a1)
      else
        (n1, n2) match {
          case (Root(ad1, v1, r1), Root(ad2, v2, r2)) =>
            if r1 < r2 then
              val newNode1 = Child(a1, v1, r1, a2)
              val newUF = this.set(a1, newNode1)
              (newUF, a2)
            else if r1 > r2 then
              val newNode2 = Child(a2, v2, r2, a1)
              val newUF = this.set(a2, newNode2)
              (newUF, a1)
            else
              (setTwo(a1, Root(a1, v1, r1 + 1), a2, Child(a2, v2, r2, a1)), a1)

          case (_, _) =>
            assert(nodeAtIsRoot(a1) && nodeAtIsRoot(a2))
            (this, BigInt(-1))
        }
    }

    private def setTwo(
        ar: BigInt,
        r: Root[T],
        ac: BigInt,
        c: Child[T]
    ): UF[T] = {
      require(isValidAddr(ar))
      require(isValidAddr(r.addr))
      require(r.addr == ar)

      require(isValidAddr(ac))
      require(isValidAddr(c.addr))
      require(c.addr == ac)

      require(ar != ac)

      // for invariant I
      require(parentFuncOnHeap(r))
      require(parentFuncOnHeap(c))

      // for invariant IV
      require(heap(ac).rank == c.rank)
      require(c.parentAddr == ar)
      require(heap(ar).rank == heap(ac).rank)

      // for invariant VI
      require(r.rank == heap(ar).rank + 1)
      require(isRoot(heap(ar))) // !isRoot(r) || isRoot(heap(ar))
      require(boundedRankFuncOnHeap(c))
      require(isRoot(heap(ac)))

      // Add r first and check invariants I to IV

      val newHeapRootFirstTemp = heap.updated(ar, r)
      val newHeapRootFirst = newHeapRootFirstTemp.updated(ac, c)
      // Invariant III
      OurListSpecs.mapAtIndex(heap, ar, _.addr)
      OurListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(0, heap.size, ar)
      OurListSpecs.mapUpdate(heap, ar, r, _.addr)
      OurListSpecs.mapAtIndex(newHeapRootFirstTemp, ac, _.addr)
      OurListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(
        0,
        newHeapRootFirstTemp.size,
        ac
      )
      OurListSpecs.mapUpdate(newHeapRootFirstTemp, ac, c, _.addr)
      // Invariant II
      rangeInvImpliesAddrInv(newHeapRootFirstTemp)
      rangeInvImpliesAddrInv(newHeapRootFirst)
      // Invariant I
      parentInvUpdate(heap, ar, r)
      parentInvUpdate(newHeapRootFirstTemp, ac, c)
      // Invariant IV
      OurListSpecs.predicateIsPreservedOnNonUpdatedElements(
        heap,
        ar,
        r,
        isRoot,
        ac
      )
      OurListSpecs.predicateIsPreservedOnNonUpdatedElements(
        heap,
        ar,
        r,
        e => e.rank == c.rank,
        ac
      )
      rankInvUpdate(heap, ar, r)
      rankInvUpdate(newHeapRootFirstTemp, ac, c)

      // Add c first and check invariant VI

      val newHeapChildFirstTemp = heap.updated(ac, c)
      val newHeapChildFirst = newHeapRootFirstTemp.updated(ar, r)
      // Invariant VI
      OurListSpecs.predicateIsPreservedOnNonUpdatedElements(
        heap,
        ac,
        c,
        isRoot,
        ar
      )

      OurListSpecs.updatedFilterSizeIncreases2(heap, ac, c, e => !isRoot(e))
      ListSpecs.forallContained(
        heap,
        e => e.rank <= heap.filter(e => !isRoot(e)).size,
        heap(ar)
      )
      assert(heap(ar).rank <= heap.filter(e => !isRoot(e)).size)
      assert(
        newHeapChildFirstTemp.filter(e => !isRoot(e)).size == heap
          .filter(e => !isRoot(e))
          .size + 1
      )
      assert(boundedRankFunc(newHeapChildFirstTemp)(r))
      boundedRankUpdate(heap, ac, c)
      boundedRankUpdate(newHeapChildFirstTemp, ar, r)

      // Order of operations does not matter
      OurListSpecs.updateOrderDoesNotMatter(heap, ar, r, ac, c)

      UF(newHeapRootFirst)
    }

    def union(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
      require(isValidAddr(a1) && isValidAddr(a2))
      val r1 = find(a1)
      val r2 = find(a2)
      assert(nodeAtIsRoot(r1) && nodeAtIsRoot(r2))
      assert(isValidAddr(r1) && isValidAddr(r2))

      link(r1, r2)
    }

  }

}
