import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import stainless.collection.Cons
import org.w3c.dom.ls.LSInput

object UnionFindInvariantIdeas {

  sealed trait Node[T] {
    val addr: BigInt
    val value: T
  }

  case class Child[T](addr: BigInt, value: T, parentAddr: BigInt)
      extends Node[T]
  case class Root[T](addr: BigInt, value: T, rank: BigInt) extends Node[T]

  def parentIsInHeap[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    if (0 <= n.addr && n.addr < heap.size) then
      n match {
        case Child(_, _, pA) => 0 <= pA && pA < heap.size
        case _               => true
      }
    else false
  }

  def addrAndHeapMatch[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    if 0 <= n.addr && n.addr < heap.size then heap(n.addr) == n
    else false
  }

  // invariant idea A: traversal is bounded by the heap's size
  def traverseBounded[T](start: Node[T], heap: List[Node[T]]): Boolean = {
    def traverseBoundedRec(n: Node[T]): BigInt = {
      n match
        case Child(addr, value, parentAddr) =>
          traverseBoundedRec(heap(addr)) + 1
        case Root(addr, value, rank) => BigInt(0)
    }

    traverseBoundedRec(start) < heap.size
  }

  // invariant idea B: going up will always end up on a root
  def finishAtRoot[T](start: Node[T], heap: List[Node[T]]): Boolean = {
    def inner(n: Node[T]): Node[T] = {
      n match
        case Child(addr, value, parentAddr) => inner(heap(addr))
        case r @ Root(addr, value, rank)    => r
    }

    isRoot(inner(start))
  }

  def isRoot[T](n: Node[T]): Boolean = {
    n match {
      case Root(a, v, r) => true
      case _             => false
    }
  }

  case class UF[T](heap: List[Node[T]]) {
    // invariant A
    require(heap.forall(finishAtRoot(_, heap)))

    // invariant B
    require(heap.forall(traverseBounded(_, heap)))
  }
}
