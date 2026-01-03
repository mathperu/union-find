package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
import stainless.annotation._
import stainless.collection.Cons

import ourlistspecs.OurListSpecs
import UnionFindList2._

object InvariantsHelpers {

    // Invariant I: parent address is always in the heap
    @inline
    def parentIsInHeap[T](n: Node[T], heap: List[Node[T]]): Boolean = {
        (0 <= n.addr && n.addr < heap.size) &&
        (n match {
            case Child(_, _, pA) => 0 <= pA && pA < heap.size
            case _               => true
        })
    }
    @inline
    def parentFunc[T] = (heap: List[Node[T]]) => (n: Node[T]) => parentIsInHeap[T](n, heap)

    def parentInvAppend[T](l: List[Node[T]], n: Node[T]): Unit = {
        require(l.forall(parentFunc(l)) && parentFunc(l :+ n)(n))

        def parentInvAppendElem(l: List[Node[T]], n: Node[T], e: Node[T]): Boolean = {
            require(parentFunc(l)(e))
            parentFunc((l :+ n))(e) because {
                assert(0 <= e.addr && e.addr < l.size)
                e match {
                    case Child(_, _, pA) => assert(0 <= pA && pA < l.size)
                    case _ => ()
                }

                (0 <= e.addr && e.addr < (l :+ n).size) &&
                (e match {
                    case Child(_, _, pA) => 0 <= pA && pA < (l :+ n).size
                    case _               => true
                })
            }
        }.holds
        def parentInvAppendRec(l: List[Node[T]], heap: List[Node[T]], n: Node[T]): Unit = {
            require(l.forall(parentFunc(heap)))
            l match {
                case Nil() => ()
                case Cons(head, tl) => 
                    assert(parentFunc(heap)(head))
                    assert(parentInvAppendElem(heap, n, head))
                    parentInvAppendRec(tl, heap, n)
            }
        }.ensuring(l.forall(parentFunc(heap :+ n)))
        
        assert(l.forall(parentFunc(l)))
        parentInvAppendRec(l, l, n)
        assert(l.forall(parentFunc(l :+ n)))
        OurListSpecs.forallAppend(l, n, parentFunc(l :+ n))
    }.ensuring(_ => (l :+ n).forall(parentFunc(l :+ n)))

    def parentInvUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
        require(l.forall(parentFunc(l)) && parentFunc(l)(n))
        require(0 <= addr && addr < l.size)
    }.ensuring{_ => (l.updated(addr, n)).forall(parentFunc(l.updated(addr, n)))}


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
        def addrInvAppendRec(l: List[Node[T]], heap: List[Node[T]], n: Node[T]): Unit = {
            require(l.forall(addrFunc(heap)))
            l match {
                case Nil() => ()
                case Cons(head, tl) => 
                    assert(addrFunc(heap)(head))
                    assert(addrInvAppendElem(heap, n, head))
                    addrInvAppendRec(tl, heap, n)
            }
        }.ensuring(l.forall(addrFunc(heap :+ n)))
        
        assert(l.forall(addrFunc(l)))
        addrInvAppendRec(l, l, n)
        assert(l.forall(addrFunc(l :+ n)))
        OurListSpecs.forallAppend(l, n, addrFunc(l :+ n))
    }.ensuring{_ => (l :+ n).forall(addrFunc(l :+ n))}

    def addrInvUpdate[T](l: List[Node[T]], addr: BigInt, n: Node[T]): Unit = {
        require(l.forall(addrFunc(l)))
        require(0 <= n.addr && n.addr < l.size)
        require(0 <= addr && addr < l.size)
        require(addr == n.addr)
        require(l.map(_.addr) == List.range(0, l.size))
    }.ensuring(_ => (l.updated(addr, n)).forall(addrFunc(l.updated(addr, n))))

    /* def updatePreservesInvariants(l: List[Node[T]], addr: BigInt, n: Node[T], heap: List[Node[T]]): Unit = {
        require(l.forall(addrFunc(heap)) && l.forall(parentFunc(heap)))
        require(addrFunc(heap)(n) && parentFunc(heap)(n))
        require(0 <= addr && addr < l.size)
        //require(n.addr == addr)
        decreases(l)
        l match {
          case Nil() => ()
          case Cons(h, t) => 
            if (addr == 0) then 
              assert(addrFunc(heap)(n) && parentFunc(heap)(n))
              updatePreservesInvariants(t, addr-1, n, heap)
            else 
              assert(addrFunc(heap)(h))
              assert(parentFunc(heap)(h))
              updatePreservesInvariants(t, addr-1, n, heap)
        }
      }.ensuring((l.updated(addr, n)).forall(addrFunc(l.updated(addr, n))) 
                  && (l.updated(addr, n)).forall(parentFunc(l.updated(addr, n))))

      updatePreservesInvariants(heap, addr, n, heap) */


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
