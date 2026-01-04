import stainless.lang._
import stainless.proof._
import stainless.collection.{Cons, Nil}
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import org.w3c.dom.ls.LSInput

object UnionFindRank {

  // decreases(heap.size - rank)
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
          case Root(_, _, _)     => true
      case Nil() => false
  }

  def isValidAddr[T](addr: BigInt, heap: List[Node[T]]): Boolean = {
    addr >= 0 && addr < heap.size
  }

  /** Invariant: parent's rank is always strictly greater than child's rank
    *
    * @param n
    * @param heap
    *
    * Requirements:
    *   - n's parent must be in heap (if n is a Child)
    */
  def parentDecreases[T](n: Node[T], heap: List[Node[T]]): Boolean = {
    if heap.isEmpty then true
    // else if !isValidAddr(n.addr, heap) then false <- not necessarily needed…
    else
      n match
        case Child(addr, value, dist, parentAddr) =>
          if isValidAddr(parentAddr, heap) then heap(parentAddr).rank > n.rank
          else false
        case Root(addr, value, rank) => rank <= heap.size
  }

  case class UF[T](heap: List[Node[T]]) {
    require(hasRoot(heap))

    val parentFunc = (heap: List[Node[T]]) => n => parentIsInHeap[T](n, heap)
    val parentFuncOnHeap = parentFunc(heap)
    val parentInHeapInvariant = heap.forall(parentFuncOnHeap)
    require(parentInHeapInvariant)

    val addrFunc = (heap: List[Node[T]]) => n => addrAndHeapMatch[T](n, heap)
    val addrFuncOnHeap = addrFunc(heap)
    val addrInvariant = heap.forall(addrFuncOnHeap)
    require(addrInvariant)

    val rankFunc = (heap: List[Node[T]]) => n => parentDecreases[T](n, heap)
    val rankFuncOnHeap = rankFunc(heap)
    val rankInv = heap.forall(rankFuncOnHeap)
    require(rankInv)

    // TODO this is technically covered by distFunc, it might be better to derive this as a lemma
    val boundedFunc = (heap: List[Node[T]]) =>
      (n: Node[T]) => n.rank <= heap.size
    val boundedFuncOnHeap = boundedFunc(heap)
    val boundedInv = heap.forall(boundedFuncOnHeap)
    require(boundedInv)

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
        case Root(addr, value, rank)           => addr
      }

    def set(addr: BigInt, n: Node[T]): UF[T] =
      require(isValidAddr(addr))
      require(n.addr == addr)
      require(isValidAddr(getParentAddr(n)))

      UF(heap.updated(addr, n))

    def isRoot(n: Node[T]): Boolean = {
      n match {
        case Root(a, v, r) => true
        case _             => false
      }
    }

    def nodeAtIsRoot(addr: BigInt): Boolean = {
      if (isValidAddr(addr)) then isRoot(nodeAt(addr))
      else true
    }

    def rankIs(n: Node[T], x: BigInt): Boolean = {
      n match {
        case Child(addr, value, _, parentAddr) => false
        case Root(addr, value, rank)           => rank == x
      }
    }

    // invariant timeout in stainless
    def make(value: T): (UF[T], Node[T]) = {
      require(!domain.contains(value))

      val addr = size
      val newNode = Root(addr, value, 0)
      val newHeap = heap :+ newNode
      (UF(newHeap), newNode)
    }

    // def boundedRank(n: Node[T]) = {
    //   require(heap.contains(n))
    //   (n.rank <= heap.size) because {
    //     ListSpecs.forallContained(heap, distFuncOnHeap, n)
    //     parentDecreases(n, heap)
    //   }
    //   ()
    // }.ensuring(n.rank <= heap.size)

    // no path compression
    // provide address and finds parent's address
    def find(addr: BigInt): BigInt = {
      require(isValidAddr(addr))
      val f = nodeAt(addr)
      require(f.rank >= 0)
      require(f.rank <= heap.size)
      decreases(size - f.rank)

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
            parentDecreases(f, heap)
          }

          instantiateRank(parent)
          check(parent.rank >= 0)
          // parent.rank <= heap.size should be trivial
          (parent.rank <= size) because {
            heap.contains(parent)
            ListSpecs.forallContained(heap, boundedFuncOnHeap, parent)
            trivial
          }
          check(parent.rank <= size)

          find(parentAddr)
        }
        case r @ Root(addr, value, rank) => {
          instantiateRank(r)
          addr
        }
      }
    }

    def equiv(a1: BigInt, a2: BigInt): Boolean = {
      require(isValidAddr(a1))
      require(isValidAddr(a2))

      instantiateRank(nodeAt(a1))
      instantiateRank(nodeAt(a2))

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
              // in case of equal rank, make one root the child of the other and increment the rank of the new root
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
            case Root(ad, value, rank) =>
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
