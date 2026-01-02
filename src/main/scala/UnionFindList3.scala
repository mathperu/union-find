import stainless.lang._
import stainless.proof._
import stainless.collection.{Cons, Nil}
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import org.w3c.dom.ls.LSInput

object UnionFindList3 {

  // Potential improvement: use rank as opposite of dist and decreases(heap.size - rank)
  sealed trait Node[T] {
    val addr: BigInt
    val dist: BigInt
    val value: T
  }

  case class Child[T](addr: BigInt, value: T, dist: BigInt, parentAddr: BigInt)
      extends Node[T] {
    require(dist > 0)
  }
  case class Root[T](addr: BigInt, value: T, dist: BigInt, rank: BigInt)
      extends Node[T] {
    require(dist == 0)
  }

  def parentIsInHeap[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    if (0 <= n.addr && n.addr < heap.size) then
      n match {
        case Child(_, _, _, pA) => 0 <= pA && pA < heap.size
        case _                  => true
      }
    else false
  }

  def addrAndHeapMatch[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    if 0 <= n.addr && n.addr < heap.size then heap(n.addr) == n
    else false
  }

  // TODO: look for a cleaner way to do this… we essentially want to avoid a case where Stainless makes a list with:
  // Root[T](BigInt("0"), T#67, BigInt("66")) and Root[T](BigInt("0"), T#67, BigInt("66")) at different addresses
  def noDuplicates[T](heap: List[Node[T]]): Boolean = {
    def containsDuplicates[T](l: List[Node[T]]): Boolean = {
      decreases(l)
      l match
        case Cons(h, t) => t.contains(h) || containsDuplicates(t)
        case Nil()      => false

    }

    !containsDuplicates(heap)
  }

  def hasRoot[T](heap: List[Node[T]]): Boolean = {
    decreases(heap)

    heap match
      case Cons(h, t) =>
        h match
          case Child(_, _, _, _) => false || hasRoot(t)
          case Root(_, _, _, _)  => true
      case Nil() => false
  }

  def parentDecreases[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    require(heap.contains(n))
    // TODO refactor

    // require parent to be in heap as well !!
    require(n match
      case Child(addr, value, dist, parentAddr) => parentAddr < heap.size
      case Root(addr, value, dist, rank)        => true)

    n match
      case Child(addr, value, dist, parentAddr) =>
        n.dist == heap(parentAddr).dist + 1
      case Root(addr, value, dist, rank) => true
  }

  // invariant idea A: traversal is bounded by the heap's size
  def traverseBounded[T](start: Node[T], heap: List[Node[T]]): Boolean = {
    require(hasRoot(heap))
    require(heap.contains(start))
    require(heap.forall(addrAndHeapMatch(_, heap)))
    require(noDuplicates(heap))
    require(heap.forall(parentDecreases(_, heap)))

    def traverseBoundedRec(n: Node[T]): BigInt = {
      require(heap.contains(n))
      decreases(n.dist)

      n match
        case Child(addr, value, _, parentAddr) =>
          traverseBoundedRec(heap(parentAddr)) + 1
        case Root(addr, value, _, rank) => BigInt(0)
    }

    traverseBoundedRec(start) < heap.size
  }

  case class UF[T](heap: List[Node[T]]) {
    val parentFunc = (heap: List[Node[T]]) => n => parentIsInHeap[T](n, heap)
    val parentFuncOnHeap = parentFunc(heap)
    val parentInHeapInvariant = heap.forall(parentFuncOnHeap)
    require(parentInHeapInvariant)

    val addrFunc = (heap: List[Node[T]]) => n => addrAndHeapMatch[T](n, heap)
    val addrFuncOnHeap = addrFunc(heap)
    val addrInvariant = heap.forall(addrFuncOnHeap)
    require(addrInvariant)

    val distFunc = (heap: List[Node[T]]) => n => parentDecreases[T](n, heap)
    val distFuncOnHeap = distFunc(heap)
    val distInv = heap.forall(distFuncOnHeap)
    require(distInv)

    // val travFunc = (heap: List[Node[T]]) => n => traverseBounded[T](n, heap)
    // val travFuncOnHeap = travFunc(heap)
    // val travFuncInvariant = heap.forall(travFuncOnHeap)
    // require(travFuncInvariant)

    def size: BigInt = heap.size
    def domain: List[T] = heap.map(n => n.value)

    def isValidAddr(addr: BigInt): Boolean =
      addr >= 0 && addr < size

    def nodeAt(addr: BigInt): Node[T] =
      require(isValidAddr(addr))
      heap(addr)

    def getParentAddr(n: Node[T]): BigInt =
      n match {
        case Child(addr, value, _, parentAddr) => parentAddr
        case Root(addr, value, _, rank)        => addr
      }

    def set(addr: BigInt, n: Node[T]): UF[T] =
      require(isValidAddr(addr))
      require(n.addr == addr)
      require(isValidAddr(getParentAddr(n)))

      UF(heap.updated(addr, n))

    def isRoot(n: Node[T]): Boolean = {
      n match {
        case Root(a, v, _, r) => true
        case _                => false
      }
    }

    def nodeAtIsRoot(addr: BigInt): Boolean = {
      if (isValidAddr(addr)) then isRoot(nodeAt(addr))
      else true
    }

    def rankIs(n: Node[T], x: BigInt): Boolean = {
      n match {
        case Child(addr, value, _, parentAddr) => false
        case Root(addr, value, _, rank)        => rank == x
      }

    }

    // invariant timeout in stainless
    def make(value: T): (UF[T], Node[T]) = {
      require(!domain.contains(value))

      val addr = size
      val newNode = Root(addr, value, 0, 0)
      val newHeap = heap :+ newNode
      (UF(newHeap), newNode)
    }

    // no path compression
    // provide address and finds parent's address
    def find(addr: BigInt): BigInt = {
      //   def findRec(addr: BigInt, fuel: BigInt): BigInt = {
      //     require(fuel >= 0)
      //     decreases(fuel)
      //     if fuel == 0 then -1
      //     else if isValidAddr(addr) then
      //       nodeAt(addr) match {
      //         case Child(addr, value, parentAddr) => findRec(parentAddr, fuel - 1)
      //         case Root(ad, value, rank)          => addr
      //       }
      //     else addr
      //   }
      //   findRec(addr, size)
      decreases(nodeAt(addr).dist)

      nodeAt(addr) match {
        case Child(addr, value, _, parentAddr) => find(parentAddr)
        case Root(addr, value, _, rank)        => addr
      }
    }

    def equiv(a1: BigInt, a2: BigInt): Boolean = {
      find(a1) == find(a2)
    }

    def link(a1: BigInt, a2: BigInt): (UF[T], BigInt) = {
      require(
        isValidAddr(a1) && isValidAddr(a2) && nodeAtIsRoot(a1) && nodeAtIsRoot(
          a2
        )
      )

      if a1 == a2 then (this, a1)
      else
        (nodeAt(a1), nodeAt(a2)) match {
          case (Root(ad1, v1, d1, r1), Root(ad2, v2, d2, r2)) =>
            if r1 < r2 then
              val newNode1 = Child(a1, v1, d1 + 1, a2)
              val newUF = this.set(a1, newNode1)
              (newUF, a2)
            else if r1 > r2 then
              val newNode2 = Child(a2, v2, d2 + 1, a1)
              val newUF = this.set(a2, newNode2)
              (newUF, a1)
            else
              val newNode1 = Child(a1, v1, d1 + 1, a2)
              val newUF1 = this.set(a1, newNode1)
              val newNode2 = Root(a2, v2, d2, r2 + 1)
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
      findReturnsRoot(a1)
      findReturnsRoot(a2)
      assert(nodeAtIsRoot(r1) && nodeAtIsRoot(r2))
      findReturnsValidAddr(a1)
      findReturnsValidAddr(a2)
      assert(isValidAddr(r1) && isValidAddr(r2))

      link(find(a1), find(a2))
    }

    // invalid in stainless: measure missing
    def findReturnsRoot(addr: BigInt): Unit = {
      def findReturnsRootRec(addr: BigInt, fuel: BigInt): Unit = {
        require(fuel >= 0)
        if fuel == 0 then ()
        else if isValidAddr(addr) then
          nodeAt(addr) match {
            case nc @ Child(addr, value, _, parentAddr) =>
              assert(heap.contains(nc))
              assert(parentInHeapInvariant)
              ListSpecs.forallContained(heap, parentFuncOnHeap, nc)
              assert(parentIsInHeap(nc, heap))
              assert(addrInvariant)
              assert(isValidAddr(parentAddr))
              findReturnsRoot(parentAddr)
            case Root(ad, value, _, rank) =>
              assert(isValidAddr(addr))
              assert(nodeAtIsRoot(addr))
          }
        else
          assert(!isValidAddr(addr))
          assert(nodeAtIsRoot(addr))
      }
    }.ensuring(_ => !isValidAddr(find(addr)) || nodeAtIsRoot(find(addr)))

    def makeAddsValueToDomain(value: T): Unit = {
      require(!domain.contains(value))
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

    def findReturnsValidAddr(addr: BigInt): Unit = {}.ensuring(_ =>
      find(addr) == BigInt(-1) || (!isValidAddr(addr) || isValidAddr(
        find(addr)
      ))
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
      require(isValidAddr(a1) && isValidAddr(a2))
    }.ensuring(_ =>
      (!(equiv(a1, b) || equiv(a2, b)) || find(b) == union(a1, a2)._2)
        && ((equiv(a1, b) || equiv(a2, b)) || find(b) != union(a1, a2)._2)
    )

  }

}
