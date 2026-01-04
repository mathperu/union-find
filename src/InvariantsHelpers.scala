package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
import stainless.annotation._
import stainless.collection.Cons

import ourlistspecs.OurListSpecs
import UnionFindList._
import ourlistspecs.OurListSpecs.forallAppend
import scala.annotation.internal.Child

object InvariantsHelpers {

  def isValidAddr[T](addr: BigInt, heap: List[Node[T]]): Boolean = {
    addr >= 0 && addr < heap.size
  }

  // Invariant I: parent address is always in the heap
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
    OurListSpecs.forallAppend(l, n, parentFunc(l :+ n))
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
        case Nil()      =>
        case Cons(h, t) => parentInvUpdateRec(heap, t, addr, n)
      }
    }.ensuring(l.forall(parentFunc(heap.updated(addr, n))))

    parentInvUpdateRec(l, l, addr, n)
    OurListSpecs.forallUpdate(l, addr, n, parentFunc(l.updated(addr, n)))
  }.ensuring { _ =>
    (l.updated(addr, n)).forall(parentFunc(l.updated(addr, n)))
  }

  // Invariant II: address matches position in heap
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
        OurListSpecs.appendPreservesIndices(l, n, e.addr)
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
    OurListSpecs.forallAppend(l, n, addrFunc(l :+ n))
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
          OurListSpecs.sliceAtIndex(l, heap, from, heap.size, h.addr)
          assert(addrFunc(heap)(h))
          OurListSpecs.sliceTail(l, heap, from, heap.size)
          rangeInvImpliesAddrInvRec(t, heap, from + 1)
      }
    }.ensuring(_ => l.forall(addrFunc(heap)))

    OurListSpecs.sliceZeroSize(l)
    rangeInvImpliesAddrInvRec(l, l, 0)
  }.ensuring(_ => l.forall(addrFunc(l)))

  /** Invariant IV: parent's rank is always strictly greater than child's rank
    *
    * @param n
    * @param heap
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
      case Root(addr, value, rank) => rank <= heap.size
    })
  }

  @inline
  def rankFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => rankDecreasesAlongEdges[T](n, heap)

  // lemma: invariant IV is preserved by appending a root to the heap
  def rankInvAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
    require(l.forall(rankFunc(l)) && rankFunc(l :+ n)(n))
    require(isRoot(n))

    // def rankInvAppendElem(l: List[Node[T]], n: Node[T], e: Node[T]): Boolean = {
    //   require(rankFunc(l)(e))
    //   rankFunc((l :+ n))(e) because {
    //     assert(0 <= e.rank && e.rank <= l.size)
    //     OurListSpecs.appendPreservesIndices(l, n, e.rank)
    //     assert(l(e.addr) == e)
    //     (0 <= e.rank && e.rank < (l :+ n).size) && (l :+ n)(e.rank) == e
    //   }
    // }.holds

    // TODO might have to pass the new heap's size !
    def rankInvAppendRec(
        l: List[Node[T]],
        heap: List[Node[T]],
        n: Node[T]
    ): Unit = {
      require(l.forall(rankFunc(heap)))
      require(isRoot(n))
      // require l to be a subset of heap
      require(l.content.subsetOf(heap.content))
      l match {
        case Nil()      => ()
        case Cons(h, t) => {
          assert(rankFunc(heap)(h))
          // rankInvAppendRec(t, heap, n)
          h match {
            case Child(addr, value, rank, parentAddr) =>
              assert(isValidAddr(parentAddr, heap))
              assert(heap(parentAddr).rank > rank)
              assert(isValidAddr(parentAddr, heap :+ n))

              // TODO need a way to show that the child doesn't get any new parents
              // fails because stainless thinks new root can be parent
              // check(parentAddr != n.addr)
              check(heap.contains(h))
              ListSpecs.forallContained(heap, rankFunc(heap), h)
              check(heap(parentAddr) != n)
              check(
                (heap :+ n)(parentAddr) == heap(parentAddr)
              ) // this is what we need to prove
              assert((heap :+ n)(parentAddr).rank > rank)

              // we want to get to this:
              assert(rankFunc(heap :+ n)(h))
              rankInvAppendRec(t, heap, n)

            case Root(addr, value, rank) =>
              assert(rank <= heap.size)
              assert(rank <= (heap :+ n).size)

              // we want to get to this:
              assert(rankFunc(heap :+ n)(h))
              rankInvAppendRec(t, heap, n)
          }
        }
      }
    }.ensuring(l.forall(rankFunc(heap :+ n)))

    rankInvAppendRec(l, l, n)
    OurListSpecs.forallAppend(l, n, rankFunc(l :+ n))
  }.ensuring { _ => (l :+ n).forall(rankFunc(l :+ n)) }

  // Invariant V: rank of a node is less than or equal to the size of the heap
  @inline
  def boundedFunc[T] = (heap: List[Node[T]]) =>
    (n: Node[T]) => (n.rank <= heap.size)

// Invariant IV implies invariant V
  def rankDecreasesInvImpliesBoundedInv[T](l: List[Node[T]]): Unit = {
    require(l.forall(rankFunc(l)))
    require(hasRoot(l))

    /* def rec(l: List[Node[T]], heap: List[Node[T]]): Unit = {
require(l.forall(rankFunc(heap)))
require(heap.forall(parentFunc(heap)))
decreases(l)
l match {
    case Nil() => ()
    case Cons(h, t) =>
    val rep = find(h.addr)
    assert(nodeAt(rep).rank >= h.rank)
    assert()
}
}.ensuring{_ => l.forall(boundedFunc(heap))}

rec(heap, heap) */

    /* decreases(l)
l match {
case Nil() => ()
case Cons(h, t) => h match {
    case Child(addr, value, rank, parentAddr) =>
        isValidAddr(parentAddr, l) && l(parentAddr).rank > rank
    case Root(addr, value, rank) => rank <= l.size
    }
    rankDecreasesInvImpliesBoundedInv(t)
} */
  }.ensuring { _ => l.forall(boundedFunc(l)) }

  // maybe other invariants?
  // domain is a list

  /* // invariant III-A: any traversal finishes at a root
    // invariant idea A: traversal is bounded by the heap's size
    def traverseBounded[T](start: Node[T], heap: List[Node[T]]): Boolean = {
        def traverseBoundedRec(n: Node[T], fuel: BigInt): BigInt = {
        require(fuel >= 0)
        decreases(fuel)
        if (fuel == 0) BigInt(0)
        else
            n match
            case Child(addr, value, parentAddr) =>
                if (parentAddr >= 0 && parentAddr < heap.size)
                traverseBoundedRec(heap(parentAddr), fuel - 1) + 1
                else BigInt(1)
            case Root(addr, value, rank) => BigInt(0)
        }

        traverseBoundedRec(start, heap.size) < heap.size
    }
    def rootInvAppend(l: List[Node[T]], n: Node[T]): Unit = {
        require(l.forall(finishAtRoot(_, l)) && finishAtRoot(n, l :+ n))
    }.ensuring{_ => (l :+ n).forall(finishAtRoot(_, l :+ n))}

    // invariant idea B: going up will always end up on a root
    def finishAtRoot[T](start: Node[T], heap: List[Node[T]]): Boolean = {
        def inner(n: Node[T], fuel: BigInt): Node[T] = {
        require(fuel >= 0)
        decreases(fuel)
        if (fuel == 0) n
        else
            n match
            case Child(addr, value, parentAddr) =>
                if (parentAddr >= 0 && parentAddr < heap.size)
                inner(heap(parentAddr), fuel - 1)
                else n
            case r @ Root(addr, value, rank) => r
        }

        isRoot(inner(start, heap.size))
    } */

}
