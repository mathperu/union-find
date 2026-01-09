package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import stainless.annotation._

import ourlistspecs.MoreListSpecs._
import InvariantsHelpers._

object UnionFindList {

  /** A node in the union-find structure. Can be one of two subtypes: [[Child]]
    * or [[Root]].
    */
  sealed trait Node[T] {
    val addr: BigInt
    val rank: BigInt
    val value: T

    require(addr >= 0)
    require(rank >= 0)
  }

  /** A child node in the union-find structure.
    *
    * @param addr
    *   the address of the node. Must match its index in the heap.
    * @param value
    *   the value stored in the node.
    * @param rank
    *   the number of tree levels below the node. Used for union by rank and
    *   termination.
    * @param parentAddr
    *   the address of the parent node. Must be different from addr.
    */
  case class Child[T](addr: BigInt, value: T, rank: BigInt, parentAddr: BigInt)
      extends Node[T] {
    require(addr != parentAddr)
  }

  /** A root node in the union-find structure.
    *
    * @param addr
    *   the address of the node. Must match its index in the heap.
    * @param value
    *   the value stored in the node.
    * @param rank
    *   the number of tree levels below the node. Used for union by rank and
    *   termination.
    */
  case class Root[T](addr: BigInt, value: T, rank: BigInt) extends Node[T]

  /** Invariant lemma required to instantiate dist >= 0 proofs
    */
  def instantiateRank[T](n: Node[T]): Unit = {}.ensuring(n.rank >= 0)

  /** Checks whether a node is a root node
    *
    * @param n
    *   the node to be checked
    * @return
    *   true if the node is a root, false otherwise
    */
  def isRoot[T](n: Node[T]): Boolean = {
    n match {
      case Root(a, v, r) => true
      case _             => false
    }
  }

  /** Checks whether the heap contains at least one root node
    *
    * @param heap
    *   the heap to be checked
    * @return
    *   true if the heap contains a root node, false otherwise
    */
  def hasRoot[T](heap: List[Node[T]]): Boolean = {
    decreases(heap)

    heap match
      case Cons(h, t) =>
        h match
          case Child(_, _, _, _) => false || hasRoot(t)
          case Root(_, _, _)     => true
      case Nil() => false
  }

  /** Union-Find structure implemented as a list of nodes
    *
    * @param heap
    *   the list of nodes representing the union-find structure, organized as a
    *   heap store. The index of each node in the list corresponds to its
    *   address.
    */
  case class UF[T](heap: List[Node[T]]) {

    /** The list of addresses in the union-find structure
      */
    val addresses: List[BigInt] = heap.map(n => n.addr)

    /** The size of the union-find structure (number of nodes)
      */
    val size: BigInt = heap.size

    /** The domain (subset of [[T]]) of the union-find structure
      */
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
      ListSpecs.mapAtIndex(heap, addr, _.addr)
      ListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(0, heap.size, addr)
      ListSpecs.mapUpdate(heap, addr, n, _.addr)

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

    /** Checks whether the node at the given address is a root node.
      * @param addr
      *   the address of the node to be checked.
      * @return
      *   true if the node at the given address is a root node, false otherwise.
      */
    def nodeAtIsRoot(addr: BigInt): Boolean = {
      if (isValidAddr(addr)) then isRoot(nodeAt(addr))
      else true
    }

    /** Checks whether the given node has the specified rank.
      *
      * @param n
      *   the node to be checked
      * @param x
      *   the rank to be compared against
      * @return
      *   true if the node has the specified rank, false otherwise
      */
    def rankIs(n: Node[T], x: BigInt): Boolean = {
      n match {
        case Child(addr, value, rank, parentAddr) => rank == x
        case Root(addr, value, rank)              => rank == x
      }

    }

    /** Adds the given value to the domain (subset of [[T]]) of the union-find
      * structure.
      *
      * @param value
      *   the value to be added as a new element.
      * @return
      *   a tuple containing the updated union-find structure and the new node.
      */
    def make(value: T): (UF[T], Node[T]) = {
      require(!domain.contains(value))

      val addr = size
      val newNode = Root(addr, value, 0)
      val newHeap = heap :+ newNode

      // Invariant I: parent address is always in the heap
      assert(parentFunc(newHeap)(newNode))
      parentInvAppend(heap, newNode)

      // Invariant II: address matches position in head
      ListSpecs.appendedElementIsAtIndexOldSize(heap, newNode)
      assert(addrFunc(newHeap)(newNode))
      addrInvAppend(heap, newNode)

      // Invariant III: addresses are correct
      ListSpecs.rangeAppend(0, heap.size)
      ListSpecs.mapDistributesOverAppend(heap, newNode, _.addr)

      // Invariant IV: rank of a node is less than or equal to its parent's rank
      assert(rankFunc(newHeap)(newNode))
      (!heap.contains(newNode)) because {
        ListSpecs.mapContains(
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

    /** Finds the root node address for the given address in the union-find.
      * Does not perform path compression.
      *
      * @param addr
      *   an arbitrary address in the union-find structure.
      * @return
      *   the address of the root node corresponding to the given address.
      */
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
            ListSpecs.weakenBoundOnListSize(
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
      (f.rank >= 0) because { instantiateRank(f); trivial }
      ListSpecs.forallContained(heap, boundedRankFuncOnHeap, f)
      ListSpecs.weakenBoundOnListSize(heap, e => !isRoot(e), f.rank)
      findInner(addr)
    }.ensuring(y =>
      nodeAtIsRoot(y) && isValidAddr(y) && nodeAt(addr).rank <= nodeAt(y).rank
    )

    /** Checks whether two addresses are in the same set.
      *
      * @param a1
      *   the first address
      * @param a2
      *   the second address
      * @return
      *   true if both addresses belong to the same set, false otherwise
      */
    def equiv(a1: BigInt, a2: BigInt): Boolean = {
      require(isValidAddr(a1))
      require(isValidAddr(a2))
      find(a1) == find(a2)
    }

    /** Links two root nodes together, returning the new union-find structure
      *
      * @param a1
      *   the first root node
      * @param a2
      *   the second root node
      * @return
      *   a tuple containing the updated union-find structure and the address of
      *   the new root node
      */
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

    // Helper method for link when ranks are equal
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
      ListSpecs.mapAtIndex(heap, ar, _.addr)
      ListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(0, heap.size, ar)
      ListSpecs.mapUpdate(heap, ar, r, _.addr)
      ListSpecs.mapAtIndex(newHeapRootFirstTemp, ac, _.addr)
      ListSpecs.rangeAtIndexPlusStartIsIndexPlusStart(
        0,
        newHeapRootFirstTemp.size,
        ac
      )
      ListSpecs.mapUpdate(newHeapRootFirstTemp, ac, c, _.addr)
      // Invariant II
      rangeInvImpliesAddrInv(newHeapRootFirstTemp)
      rangeInvImpliesAddrInv(newHeapRootFirst)
      // Invariant I
      parentInvUpdate(heap, ar, r)
      parentInvUpdate(newHeapRootFirstTemp, ac, c)
      // Invariant IV
      ListSpecs.predicateIsPreservedOnNonUpdatedElements(
        heap,
        ar,
        r,
        isRoot,
        ac
      )
      ListSpecs.predicateIsPreservedOnNonUpdatedElements(
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
      ListSpecs.predicateIsPreservedOnNonUpdatedElements(
        heap,
        ac,
        c,
        isRoot,
        ar
      )

      ListSpecs.updatedFilterSizeIncreases2(heap, ac, c, e => !isRoot(e))
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
      ListSpecs.updateOrderDoesNotMatter(heap, ar, r, ac, c)

      UF(newHeapRootFirst)
    }

    /** Unites the sets containing the two given addresses, returning the new
      * union-find structure.
      *
      * @param a1
      *   the first address
      * @param a2
      *   the second address
      * @return
      *   a tuple containing the updated union-find structure and the address of
      *   the new root node
      */
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
