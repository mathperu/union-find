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
      extends Node[T]
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
    require(rankInv)

    // Invariant V: rank of a node is bounded by the size of the heap it's in
    //    TODO this is technically covered by distFunc, it might be better to derive this as a lemma
    val boundedFuncOnHeap = boundedFunc(heap)
    val boundedInv = heap.forall(boundedFuncOnHeap)
    require(boundedInv)

    // invariant XXX-A: any traversal finishes at a root
    // require(heap.forall(finishAtRoot(_, heap)))

    // invariant XXX-B: any traversal is bounded by the heap's size
    // require(heap.forall(traverseBounded(_, heap)))

    def isValidAddr(addr: BigInt): Boolean =
      0 <= addr && addr < size

    def nodeAt(addr: BigInt): Node[T] =
      require(isValidAddr(addr))
      heap(addr)

    def getParentAddr(n: Node[T]): BigInt =
      n match {
        case Child(addr, value, _, parentAddr) => parentAddr
        case Root(addr, value, rank)           => addr
      }

    def set(addr: BigInt, n: Node[T]): UF[T] =
      require(isValidAddr(addr))
      require(isValidAddr(n.addr))
      require(n.addr == addr)
      require(parentFuncOnHeap(n))

      val newHeap = heap.updated(addr, n)

      // invariant IV
      OurListSpecs.mapAtIndex(heap, addr, _.addr)
      OurListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(0, heap.size, addr)
      OurListSpecs.mapUpdate(heap, addr, n, _.addr)

      rangeInvImpliesAddrInv(newHeap)
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
      OurListSpecs.mapAppend(heap, newNode, _.addr)

      // Invariant IV: rank of a node is less than or equal to its parent's rank
      assert(rankFunc(newHeap)(newNode))
      rankInvAppend(heap, newNode)

      (UF(newHeap), newNode)
    }

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
            // prove: isValidAddr(parentAddr) using parentInv
            isValidAddr(parentAddr) because {
              heap.contains(f)
              ListSpecs.forallContained(heap, parentFuncOnHeap, f)
              parentIsInHeap(f, heap)
            }

            check(isValidAddr(parentAddr))
            val parent = nodeAt(parentAddr)
            check(rankInv)

            (parent.rank > dist) because {
              heap.contains(f)
              ListSpecs.forallContained(heap, rankFuncOnHeap, f)
              rankDecreasesAlongEdges(f, heap)
            }

            instantiateRank(parent)
            check(parent.rank >= 0)
            (parent.rank <= size) because {
              heap.contains(parent)
              ListSpecs.forallContained(heap, boundedFuncOnHeap, parent)
              trivial
            }
            check(parent.rank <= size)

            findInner(parentAddr)
          }
          case r @ Root(addr, value, rank) => {
            instantiateRank(r)
            isValidAddr(addr) because {
              heap.contains(r)
              ListSpecs.forallContained(heap, addrFuncOnHeap, r)
              addrAndHeapMatch(r, heap)
              trivial
            }
            addr
          }
        }
      }.ensuring(y => nodeAtIsRoot(y) && isValidAddr(y))

      // Invoke invariants on Node[T]
      val f = nodeAt(addr)
      (f.rank >= 0) because { instantiateRank(f); trivial }
      (f.rank <= size) because {
        heap.contains(f)
        ListSpecs.forallContained(heap, boundedFuncOnHeap, f)
        trivial
      }
      findInner(addr)
    }.ensuring(y => nodeAtIsRoot(y) && isValidAddr(y))

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

      if a1 == a2 then (this, a1)
      else
        (nodeAt(a1), nodeAt(a2)) match {
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
              val newNode1 = Child(a1, v1, r1, a2)
              val newUF1 = this.set(a1, newNode1)
              val newNode2 = Root(a2, v2, r2 + 1)
              val newUF2 = newUF1.set(a2, newNode2)
              (newUF2, a2)

          case (_, _) =>
            assert(nodeAtIsRoot(a1) && nodeAtIsRoot(a2))
            (this, BigInt(-1))
        }
    }

    def union(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
      require(isValidAddr(a1) && isValidAddr(a2))
      val r1 = find(a1)
      val r2 = find(a2)
      // findReturnsRoot(a1) provided by find
      // findReturnsRoot(a2)
      assert(nodeAtIsRoot(r1) && nodeAtIsRoot(r2))
      // findReturnsValidAddr(a1) provided by find
      // findReturnsValidAddr(a2)
      assert(isValidAddr(r1) && isValidAddr(r2))

      link(find(a1), find(a2))
    }

    // TODO bye bye findRec
    def findRec(addr: BigInt, fuel: BigInt): BigInt = {
      require(fuel >= 0)
      decreases(fuel)
      if fuel == 0 then -1
      else if isValidAddr(addr) then
        nodeAt(addr) match {
          case Child(addr, value, _, parentAddr) =>
            findRec(parentAddr, fuel - 1)
          case Root(ad, value, rank) => addr
        }
      else addr
    }

    def findReturnsRoot(addr: BigInt): Unit = {
      require(isValidAddr(addr))
    }.ensuring(
      nodeAtIsRoot(find(addr))
    )
    def findReturnsValidAddr(addr: BigInt): Unit = {
      require(isValidAddr(addr))
    }.ensuring(
      isValidAddr(find(addr))
    )

    def makeAddsValueToDomain(value: T): Unit = {
      require(!domain.contains(value))
      val (newUF, newNode) = make(value)

      // Lemma: Prove that mapping over an appended list distributes the operation
      def mapSnoc(l: List[Node[T]], e: Node[T]): Unit = {
        decreases(l)
        l match {
          case Nil()      => ()
          case Cons(h, t) => mapSnoc(t, e)
        }
      }.ensuring(_ => (l :+ e).map(_.value) == l.map(_.value) :+ e.value)

      mapSnoc(heap, newNode)

      assert(newUF.domain == domain :+ value)
      assert(newUF.domain.contains(value))
    }.ensuring(_ => make(value)._1.domain.contains(value))

    def makeReturnsASingletonSet(value: T): Unit = {
      require(!domain.contains(value))
    }.ensuring(_ =>
      isRoot(make(value)._2)
        && (find(make(value)._2.addr) == BigInt(-1) || find(
          make(value)._2.addr
        ) == make(value)._2.addr)
        && rankIs(make(value)._2, BigInt(0))
    )

    def linkReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(
        isValidAddr(a1) && isValidAddr(a2) && nodeAtIsRoot(a1) && nodeAtIsRoot(
          a2
        )
      )
    }.ensuring(_ => link(a1, a2)._2 == a1 || link(a1, a2)._2 == a2)

    def unionReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(isValidAddr(a1) && isValidAddr(a2))
    }.ensuring(_ =>
      union(a1, a2)._2 == find(a1) || union(a1, a2)._2 == find(a2)
    )

    def unionMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(isValidAddr(a1))
      require(isValidAddr(a2))
      require(isValidAddr(b))
    }.ensuring(_ =>
      (!(equiv(a1, b) || equiv(a2, b)) || find(b) == union(a1, a2)._2)
        && ((equiv(a1, b) || equiv(a2, b)) || find(b) != union(a1, a2)._2)
    )

  }

}
