package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
import stainless.annotation._
import stainless.collection.Cons

import UnionFindList._
import morelistspecs.MoreListSpecs
import scala.annotation.internal.Child

object InvariantsHelpers {

  /** Helper method to check if an address is valid in the given heap.
    */
  def isValidAddr[T](addr: BigInt, heap: List[Node[T]]): Boolean = {
    addr >= 0 && addr < heap.size
  }

  /** Invariant I: parent address is always in the heap
    *
    * @param n
    * @param heap
    * @return
    */
  @inline
  def parentIsInHeap[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    (0 <= n.addr && n.addr < heap.size) &&
    (n match {
      case Child(_, _, _, pA) => 0 <= pA && pA < heap.size
      case _                  => true
    })
  }
  @inline
  def parentFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => parentIsInHeap[T](n, heap)

  def parentInvAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(parentFunc(l)) && parentFunc(l :+ n)(n))

    def parentInvAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(l.forall(parentFunc(heap)))
      l match {
        case Nil()      => ()
        case Cons(h, t) => parentInvAppendRec(t, heap, n)
      }
    }.ensuring(l.forall(parentFunc(heap :+ n)))

    parentInvAppendRec(l, l, n)
    MoreListSpecs.snocForallAppend(l, n, parentFunc(l :+ n))
  }.ensuring(_ => (l :+ n).forall(parentFunc(l :+ n)))

  def parentInvUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
    require(l.forall(parentFunc(l)) && parentFunc(l)(n))
    require(0 <= addr && addr < l.size)

    def parentInvUpdateRec(
        heap: List[Node[T]],
        l: List[Node[T]],
        addr: BigInt,
        n: Node[T]
    ): Unit = {
      require(0 <= addr && addr < heap.size)
      require(l.forall(parentFunc(heap)))

      l match {
        case Nil()      => ()
        case Cons(h, t) => parentInvUpdateRec(heap, t, addr, n)
      }
    }.ensuring(l.forall(parentFunc(heap.updated(addr, n))))

    parentInvUpdateRec(l, l, addr, n)
    MoreListSpecs.forallUpdate(l, addr, n, parentFunc(l.updated(addr, n)))
  }.ensuring { _ =>
    (l.updated(addr, n)).forall(parentFunc(l.updated(addr, n)))
  }

  /** Invariant II: address matches position in heap.
    *
    * @param n
    *   an arbitrary node
    * @param heap
    *   the heap of nodes
    * @return
    *   true if n's address matches its position in heap, false otherwise
    */
  @inline
  def addrAndHeapMatch[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    0 <= n.addr && n.addr < heap.size && heap(n.addr) == n
  }
  @inline
  def addrFunc[T] = (heap: List[Node[T]]) => n => addrAndHeapMatch[T](n, heap)

  def addrInvAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(addrFunc(l)) && addrFunc(l :+ n)(n))

    def addrInvAppendElem(l: List[Node[T]], n: Node[T], e: Node[T]): Boolean = {
      require(addrFunc(l)(e))
      addrFunc((l :+ n))(e) because {
        assert(0 <= e.addr && e.addr < l.size)
        MoreListSpecs.appendPreservesIndices(l, n, e.addr)
        assert(l(e.addr) == e)

        (0 <= e.addr && e.addr < (l :+ n).size) && (l :+ n)(e.addr) == e
      }
    }.holds
    def addrInvAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(l.forall(addrFunc(heap)))
      l match {
        case Nil()      => ()
        case Cons(h, t) =>
          assert(addrFunc(heap)(h))
          assert(addrInvAppendElem(heap, n, h))
          addrInvAppendRec(t, heap, n)
      }
    }.ensuring(l.forall(addrFunc(heap :+ n)))

    addrInvAppendRec(l, l, n)
    MoreListSpecs.snocForallAppend(l, n, addrFunc(l :+ n))
  }.ensuring { _ => (l :+ n).forall(addrFunc(l :+ n)) }

  // Invariant III implies invariant II
  def rangeInvImpliesAddrInv[T](l: List[Node[T]]): Unit = {
    require(l.map(_.addr) == List.range(0, l.size))

    def rangeInvImpliesAddrInvRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        from: BigInt
    ): Unit = {
      require(heap.map(_.addr) == List.range(0, heap.size))
      require(l.map(_.addr) == List.range(from, from + l.size))
      require(0 <= from)
      require(from + l.size == heap.size)
      require(l == heap.slice(from, heap.size))
      l match {
        case Nil()      => ()
        case Cons(h, t) =>
          MoreListSpecs.sliceAtIndex(l, heap, from, heap.size, h.addr)
          assert(addrFunc(heap)(h))
          MoreListSpecs.sliceTail(l, heap, from, heap.size)
          rangeInvImpliesAddrInvRec(t, heap, from + 1)
      }
    }.ensuring(_ => l.forall(addrFunc(heap)))

    MoreListSpecs.sliceZeroSize(l)
    rangeInvImpliesAddrInvRec(l, l, 0)
  }.ensuring(_ => l.forall(addrFunc(l)))

  /** Invariant IV: parent's rank is always strictly greater than child's rank
    *
    * @param n
    *   an arbitrary node
    * @param heap
    *   the heap of nodes
    *
    * Requirements/side-effects:
    *   - n's parent must be in heap (if n is a Child)
    *   - any root must have rank less than or equal to heap size
    */
  @inline
  def rankDecreasesAlongEdges[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    isValidAddr(n.addr, heap) && (n match {
      case Child(addr, value, rank, parentAddr) =>
        isValidAddr(parentAddr, heap) && heap(parentAddr).rank > n.rank
      case Root(addr, value, rank) => true
    })
  }

  @inline
  def rankFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => rankDecreasesAlongEdges[T](n, heap)

  /** Lemma: Invariant IV is preserved by appending a new root to the heap
    *
    * @param l
    * @param n
    */
  def rankInvAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(rankFunc(l)) && rankFunc(l :+ n)(n))
    require(isRoot(n))
    require(!l.contains(n))

    def rankInvAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(heap.forall(rankFunc(heap)))
      require(l.forall(rankFunc(heap)))
      require(isRoot(n))
      require(!heap.contains(n))

      l match {
        case Nil()      => ()
        case Cons(h, t) => {
          h match {
            case Child(addr, value, rank, parentAddr) =>
              MoreListSpecs.appendPreservesIndices(heap, n, parentAddr)
            case Root(addr, value, rank) => ()
          }
          rankInvAppendRec(t, heap, n)
        }
      }
    }.ensuring(l.forall(rankFunc(heap :+ n)))

    rankInvAppendRec(l, l, n)
    MoreListSpecs.snocForallAppend(l, n, rankFunc(l :+ n))
  }.ensuring { _ => (l :+ n).forall(rankFunc(l :+ n)) }

  def rankInvUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
    require(l.forall(rankFunc(l)))
    require(rankFunc(l)(n))
    require(l.forall(addrFunc(l)))
    require(0 <= addr && addr < l.size)
    require(isRoot(l(addr)) ==> (l(addr).rank <= n.rank))
    require(isRoot(l(addr)) ==> (isRoot(n) || l(addr).rank == n.rank))
    require(!isRoot(l(addr)) ==> (!isRoot(n) && l(addr).rank == n.rank))

    def rankInvUpdateElem[T](
        l: List[Node[T]],
        n: Node[T],
        addr: BigInt,
        e: Node[T]
    ): Unit = {
      require(0 <= addr && addr < l.size)
      require(l.contains(e))
      require(parentIsInHeap(e, l))
      require(addrFunc(l)(e))
      require(rankFunc(l)(e))
      require(rankFunc(l)(n))
      require(isRoot(l(addr)) ==> (l(addr).rank <= n.rank))
      require(!isRoot(l(addr)) ==> (l(addr).rank == n.rank))

      e match
        case Root(a, v, rank)          => ()
        case Child(a, v, rank, parent) =>
          if parent == addr then ()
          else if a == addr then
            MoreListSpecs.updatePreservesIndices(l, addr, n, parent)
          else
            MoreListSpecs.predicatePreservedOnNonUpdatedPair(
              l,
              a,
              parent,
              addr,
              n,
              (c: Node[T], p: Node[T]) => c.rank < p.rank
            )

            MoreListSpecs.updatePreservesIndices(l, addr, n, a)
    }.ensuring(rankFunc(l.updated(addr, n))(e))

    def rankInvUpdateRec(
        heap: List[Node[T]],
        addr: BigInt,
        l: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(0 <= addr && addr < heap.size)
      require(l.forall(rankFunc(heap)) && rankFunc(heap)(n))
      require(l.forall(addrFunc(heap)))
      require(isRoot(heap(addr)) ==> (heap(addr).rank <= n.rank))
      require(!isRoot(heap(addr)) ==> (heap(addr).rank == n.rank))

      l match {
        case Nil()      =>
        case Cons(h, t) =>
          rankInvUpdateElem(heap, n, addr, h)
          rankInvUpdateRec(heap, addr, t, n)
      }
    }.ensuring(l.forall(rankFunc(heap.updated(addr, n))))

    n match
      case Root(a, _, _) =>
        assert(rankFunc(l.updated(addr, n))(n))
      case Child(a, _, r, p) =>
        MoreListSpecs.updatePreservesIndices(l, addr, n, p)

    rankInvUpdateRec(l, addr, l, n)
    MoreListSpecs.forallUpdate(l, addr, n, rankFunc(l.updated(addr, n)))
  }.ensuring { _ =>
    (l.updated(addr, n)).forall(rankFunc(l.updated(addr, n)))
  }

  /** Invariant V: rank is bounded by number of children
    *
    * @param n
    * @param heap
    * @return
    */
  @inline
  def rankIsBoundedByNumberOfChildren[T](
      n: Node[T],
      heap: List[Node[T]]
  ): Boolean =
    n.rank <= heap.filter(n => !isRoot(n)).size

  @inline
  def boundedRankFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => rankIsBoundedByNumberOfChildren(n, heap)

  def boundedRankAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(boundedRankFunc(l)))
    require(boundedRankFunc(l :+ n)(n))

    def boundedRankAppendElem(
        l: List[Node[T]],
        n: Node[T],
        elem: Node[T]
    ): Unit = {
      require(boundedRankFunc(l)(elem))
      n match {
        case Child(_, _, r, _) =>
          MoreListSpecs.appendFilterSizeDecreases(l, n, e => !isRoot(e))
        case Root(_, _, r) =>
          MoreListSpecs.appendFilterSizePreserved(l, n, e => !isRoot(e))
      }
    }.ensuring { _ => boundedRankFunc(l :+ n)(elem) }

    def boundedRankAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(l.forall(boundedRankFunc(heap)))

      l match {
        case Nil()      => ()
        case Cons(h, t) =>
          boundedRankAppendElem(heap, n, h)
          boundedRankAppendRec(t, heap, n)
      }
    }.ensuring { _ => l.forall(boundedRankFunc(heap :+ n)) }

    boundedRankAppendRec(l, l, n)
    MoreListSpecs.snocForallAppend(l, n, boundedRankFunc(l :+ n))
  }.ensuring { _ => (l :+ n).forall(boundedRankFunc(l :+ n)) }

  def boundedRankUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
    require(0 <= addr && addr < l.size)
    require(l.forall(boundedRankFunc(l)))
    require(boundedRankFunc(l)(n))
    require(!isRoot(n) || isRoot(l(addr)))

    def boundedRankUpdateElem(
        heap: List[Node[T]],
        addr: BigInt,
        n: Node[T],
        elem: Node[T]
    ): Unit = {
      require(0 <= addr && addr < heap.size)
      require(boundedRankFunc(heap)(elem))
      require(!isRoot(n) || isRoot(heap(addr)))

      n match {
        case Child(_, _, r, _) =>
          MoreListSpecs.updatedFilterSizeIncreases(
            heap,
            addr,
            n,
            e => !isRoot(e)
          )
        case Root(_, _, r) =>
          MoreListSpecs.updatedFilterSizeIncreases(
            heap,
            addr,
            n,
            e => !isRoot(e)
          )
      }
    }.ensuring { _ => boundedRankFunc(heap.updated(addr, n))(elem) }

    def boundedRankUpdateRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        addr: BigInt,
        n: Node[T]
    ): Unit = {
      require(0 <= addr && addr < heap.size)
      require(l.forall(boundedRankFunc(heap)))
      require(!isRoot(n) || isRoot(heap(addr)))

      l match {
        case Nil()      => ()
        case Cons(h, t) =>
          boundedRankUpdateElem(heap, addr, n, h)
          boundedRankUpdateRec(t, heap, addr, n)
      }
    }.ensuring { _ => l.forall(boundedRankFunc(heap.updated(addr, n))) }

    boundedRankUpdateRec(l, l, addr, n)
    MoreListSpecs.forallUpdate(l, addr, n, boundedRankFunc(l.updated(addr, n)))
  }.ensuring { _ =>
    (l.updated(addr, n)).forall(boundedRankFunc(l.updated(addr, n)))
  }

  /** Corollary VI: rank of a node is less than or equal to the size of the
    * heap.
    *
    * *Implied by Invariant V*
    */
  @inline
  def boundedFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => (n.rank <= heap.size)

  def boundedAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(boundedFunc(l)))
    require(boundedFunc(l :+ n)(n))

    def boundedRankAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(l.forall(boundedFunc(heap)))

      l match {
        case Nil()      => ()
        case Cons(h, t) => boundedRankAppendRec(t, heap, n)
      }
    }.ensuring(l.forall(boundedFunc(heap :+ n)))

    boundedRankAppendRec(l, l, n)
    MoreListSpecs.snocForallAppend(l, n, boundedFunc(l :+ n))
  }.ensuring { _ => (l :+ n).forall(boundedFunc(l :+ n)) }

  def boundedUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
    require(l.forall(boundedFunc(l)))
    require(boundedFunc(l)(n))
    require(0 <= addr && addr < l.size)

    def boundedRankUpdateRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        addr: BigInt,
        n: Node[T]
    ): Unit = {
      require(l.forall(boundedFunc(heap)))
      require(0 <= addr && addr < heap.size)

      l match {
        case Nil()      => ()
        case Cons(h, t) => boundedRankUpdateRec(t, heap, addr, n)
      }
    }.ensuring { _ => l.forall(boundedFunc(heap.updated(addr, n))) }

    boundedRankUpdateRec(l, l, addr, n)
    MoreListSpecs.forallUpdate(l, addr, n, boundedFunc(l.updated(addr, n)))
  }.ensuring { _ => l.updated(addr, n).forall(boundedFunc(l.updated(addr, n))) }

}
