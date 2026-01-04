import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import stainless.collection.Cons

import OurListSpecs._

object UnionFindListMakeTest {

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

    // TODO this is a hack (if start not in heap, then trivially true)
    if !heap.contains(start) then true else isRoot(inner(start, heap.size))
  }

  def isRoot[T](n: Node[T]): Boolean = {
    n match {
      case Root(a, v, r) => true
      case _             => false
    }
  }

  case class UF[T](heap: List[Node[T]]) {
    // Invariant I: parent address is always in the heap
    val parentFunc = (heap: List[Node[T]]) => n => parentIsInHeap[T](n, heap)
    val parentFuncOnHeap = parentFunc(heap)
    val parentInHeapInvariant = heap.forall(parentFuncOnHeap)
    require(parentInHeapInvariant)

    // parentFunc(oldHeap)(n) => parentFunc(oldHeap :+ t)(n) for all n in old heap
    // - in particular prove that parentFunc(oldHeap :+ t)(t) holds
    def parentInvAppend(l: List[Node[T]], n: Node[T]): Unit = {
      require(l.forall(parentFunc(l)) && parentFunc(l :+ n)(n))
    }.ensuring { _ => (l :+ n).forall(parentFunc(l :+ n)) }

    // Invariant II: address matches position in heap
    val addrFunc = (heap: List[Node[T]]) => n => addrAndHeapMatch[T](n, heap)
    val addrFuncOnHeap = addrFunc(heap)
    val addrInvariant = heap.forall(addrFuncOnHeap)
    require(addrInvariant)

    // addrFunc(oldHeap)(n) => addrFunc(oldHeap :+ t)(n) for all n in old heap
    // - in particular prove that addrFunc(oldHeap :+ t)(t) holds
    def addrInvAppend(l: List[Node[T]], n: Node[T]): Unit = {
      require(l.forall(addrFunc(l)) && addrFunc(l :+ n)(n))

      // To prove : every elem in l has address in the bounds in l :+ n
      assert(
        l.forall(n =>
          if (0 <= n.addr && n.addr < l.size) then l(n.addr) == n else false
        )
      ) // TO
      assert(l.forall(n => 0 <= n.addr && n.addr < l.size && l(n.addr) == n))
      assert(
        l.forall(n =>
          0 <= n.addr && n.addr < l.size && 0 <= n.addr && n.addr < l.size && l(
            n.addr
          ) == n
        )
      )
      @inline
      def p: Node[T] => Boolean = n => 0 <= n.addr && n.addr < l.size
      @inline
      def q: Node[T] => Boolean =
        n => 0 <= n.addr && n.addr < l.size && l(n.addr) == n
      assert(l.forall(n => p(n) && q(n)))
      OurListSpecs.weakenForAll(l, p, q)
      assert(l.forall(p))
      assert(l.forall(n => 0 <= n.addr && n.addr < l.size))
      @inline
      def f: Node[T] => BigInt = n => n.addr
      OurListSpecs.staysBoundedAppend(l, n, f)

      // To prove : every elem in l has address corresponding to its index in l :+ n

      assert(l.forall(addrFunc(l :+ n)))
      OurListSpecs.forallAppend(l, n, addrFunc(l :+ n))
    }.ensuring { _ => (l :+ n).forall(addrFunc(l :+ n)) }

    // invariant III-A: any traversal finishes at a root
    val finishRootFunc = (heap: List[Node[T]]) => n => finishAtRoot[T](n, heap)
    val finishRootFuncOnHeap = finishRootFunc(heap)
    val finishRootInvariant = heap.forall(finishRootFuncOnHeap)
    require(heap.forall(finishAtRoot(_, heap)))

    def rootInvAppend(l: List[Node[T]], n: Node[T]): Unit = {
      require(l.forall(finishAtRoot(_, l)) && finishAtRoot(n, l :+ n))
    }.ensuring { _ => (l :+ n).forall(finishAtRoot(_, l :+ n)) }

    // invariant III-B: any traversal is bounded by the heap's size
    require(heap.forall(traverseBounded(_, heap)))

    def size: BigInt = heap.size
    def domain: List[T] = heap.map(n => n.value)

    def isValidAddr(addr: BigInt): Boolean =
      addr >= 0 && addr < size

    def nodeAt(addr: BigInt): Node[T] =
      require(isValidAddr(addr))
      heap(addr)

    def getParentAddr(n: Node[T]): BigInt =
      n match {
        case Child(addr, value, parentAddr) => parentAddr
        case Root(addr, value, rank)        => addr
      }

    def set(addr: BigInt, n: Node[T]): UF[T] =
      require(isValidAddr(addr))
      require(n.addr == addr)
      require(isValidAddr(getParentAddr(n)))

      UF(heap.updated(addr, n))

    def nodeAtIsRoot(addr: BigInt): Boolean = {
      if (isValidAddr(addr)) then isRoot(nodeAt(addr))
      else true
    }

    def rankIs(n: Node[T], x: BigInt): Boolean = {
      n match {
        case Child(addr, value, parentAddr) => false
        case Root(addr, value, rank)        => rank == x
      }

    }

    def lemmaFinishAtRoot[A](
        oldHeap: List[Node[A]],
        newNode: Node[A]
    ): Unit = {
      // TODO only works for roots!
      require(oldHeap.forall(finishAtRoot(_, oldHeap)))
      require(isRoot(newNode))
      // require(finishAtRoot(newNode, oldHeap :+ newNode))
    }.ensuring(oldHeap.forall(finishAtRoot(_, oldHeap :+ newNode)))

    def lemmaTraverseBounded[A](
        oldHeap: List[Node[A]],
        newNode: Node[A]
    ): Unit = {
      // TODO only works for roots!
      require(oldHeap.forall(traverseBounded(_, oldHeap)))
      require(isRoot(newNode))
      // require(traverseBounded(newNode, oldHeap :+ newNode))
    }.ensuring(oldHeap.forall(traverseBounded(_, oldHeap :+ newNode)))

    // Lemma : Snoc Forall
    // Proves that if P holds for list L and element X, it holds for L :+ X
    def lemmaSnocForall[A](l: List[A], x: A, p: A => Boolean): Unit = {
      require(l.forall(p))
      require(p(x))

      ListSpecs.listAppendValidProp(List(x), l, p)
      ListSpecs.snocIsAppend(l, x)
      ()
    }.ensuring(_ => (l :+ x).forall(p))

    // invariant timeout in stainless
    def make(value: T): (UF[T], Node[T]) = {
      require(!domain.contains(value))

      val addr = size
      val newNode = Root(addr, value, 0)
      val newHeap = heap :+ newNode

      // val singleton: List[Node[T]] = List(newNode)

      // // Define predicates to check
      // val checkFinish = (n: Node[T]) => finishAtRoot(n, newHeap)
      // val checkBound  = (n: Node[T]) => traverseBounded(n, newHeap)
      // val checkAddr   = (n: Node[T]) => addrAndHeapMatch(n, newHeap)
      // val checkParent = (n: Node[T]) => parentIsInHeap(n, newHeap)

      // ListSpecs.snocIsAppend(heap, newNode)

      // // // Explicitly assert that both parts satisfy the predicates
      // assert(singleton.forall(checkFinish))
      // assert(heap.forall(checkFinish))
      // lemmaSnocForall(heap, newNode, checkFinish)
      // ListSpecs.listAppendValidProp(singleton, heap, checkFinish)

      // assert(singleton.forall(checkBound))
      // assert(heap.forall(checkBound))
      // ListSpecs.listAppendValidProp(singleton, heap, checkBound)

      // ListSpecs.snocIndex(heap, newNode, size)
      // assert(newHeap(size) == newNode) // sanity check
      // assert(singleton.forall(checkAddr))
      // assert(heap.forall(checkAddr))
      // ListSpecs.listAppendValidProp(singleton, heap, checkAddr)

      // assert(singleton.forall(checkParent))
      // assert(heap.forall(checkParent))
      // ListSpecs.listAppendValidProp(singleton, heap, checkParent)

      // check all invariants

      // Invariant I: parent address is always in the heap
      assert(parentFunc(heap :+ newNode)(newNode)) // newHeap
      parentInvAppend(heap, newNode)

      // Invariant II: address matches position in head
      OurListSpecs.appendedElementIsAtIndexOldSize(heap, newNode)
      assert(addrFunc(heap :+ newNode)(newNode))
      addrInvAppend(heap, newNode)

      // invariant III-A: any traversal finishes at a root
      assert(finishAtRoot(newNode, heap :+ newNode))
      rootInvAppend(heap, newNode)
      assert(heap.forall(finishAtRoot(_, heap)))
      lemmaFinishAtRoot(
        heap,
        newNode
      ) // h.forall(finishAtRoot(_, h)) => h.forall(finishAtRoot(_, h :+ t)) (trivial)
      assert(heap.forall(finishAtRoot(_, heap :+ newNode)))
      // assert(
      //   forall((n: Node[T]) =>
      //     finishAtRoot(n, newHeap) == finishAtRoot(n, heap :+ newNode)
      //   )
      // )
      // assert(
      //   forall((n: Node[T]) => !newHeap.contains(n) || finishAtRoot(n, newHeap))
      // )
      // assert(heap.forall(finishAtRoot(_, newHeap))) // timeout here
      lemmaSnocForall(heap, newNode, finishAtRoot(_, heap :+ newNode))
      assert((heap :+ newNode).forall(finishAtRoot(_, heap :+ newNode)))
      // we're good up to here, we can just pass heap :+ newNode as newHeap

      // assert(
      //   newHeap.forall(finishAtRoot(_, newHeap))
      // ) // TO, maybe should define invariant III like I and II ?

      // invariant III-B: any traversal is bounded by the heap's size
      assert(traverseBounded(newNode, heap :+ newNode))
      // lemmaTraverseBounded: h.forall(traverseBounded(_, h)) => h.forall(traverseBounded(_, h :+ t))
      lemmaTraverseBounded(heap, newNode)
      lemmaSnocForall(
        heap,
        newNode,
        traverseBounded(_, heap :+ newNode)
      ) // newNode instead of heap :+ newNode
      assert(
        (heap :+ newNode).forall(traverseBounded(_, heap :+ newNode))
      )
      // assert(newHeap.forall(traverseBounded(_, newHeap))) // TO

      // Proofs needed, for a new node t, where newHeap = oldHeap :+ N
      //
      // addrFunc(oldHeap)(n) => addrFunc(oldHeap :+ t)(n) for all n in old heap
      // - in particular prove that addrFunc(oldHeap :+ t)(t) holds
      //
      // parentFunc(oldHeap)(n) => parentFunc(oldHeap :+ t)(n) for all n in old heap
      // - in particular prove that parentFunc(oldHeap :+ t)(t) holds
      //
      // finishAtRoot(n, oldHeap) => finishAtRoot(n, oldHeap :+ n) for all n in old heap
      // - trivial for stainless: finishAtRoot(t, oldHeap :+ t) holds
      //
      // traverseBounded(n, oldHeap) => traverseBounded(n, oldHeap +: n) for all n in old heap
      // - trivial for stainless: traverseBounded(t, oldHeap :+ t) holds

      assert(newHeap == heap :+ newNode)
      // (UF(heap :+ newNode), newNode)
      val newUF = this.copy(heap :+ newNode)
      (newUF, newNode)
    }

    // no path compression
    // provide address and finds parent's address

    def findRec(addr: BigInt, fuel: BigInt): BigInt = {
      require(fuel >= 0)
      decreases(fuel)
      if fuel == 0 then -1
      else if isValidAddr(addr) then
        nodeAt(addr) match {
          case Child(addr, value, parentAddr) => findRec(parentAddr, fuel - 1)
          case Root(ad, value, rank)          => addr
        }
      else addr
    }

    def find(addr: BigInt): BigInt = {
      findRec(addr, size)
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
          case (Root(ad1, v1, r1), Root(ad2, v2, r2)) =>
            if r1 < r2 then
              val newNode1 = Child(a1, v1, a2)
              val newUF = this.set(a1, newNode1)
              (newUF, a2)
            else if r1 > r2 then
              val newNode2 = Child(a2, v2, a1)
              val newUF = this.set(a2, newNode2)
              (newUF, a1)
            else
              val newNode1 = Child(a1, v1, a2)
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

    def findReturnsRoot(addr: BigInt): Unit = {
      def findReturnsRootRec(addr: BigInt, fuel: BigInt): Unit = {
        require(fuel >= 0)
        decreases(fuel)

        if fuel == 0 then ()
        else if isValidAddr(addr) then
          nodeAt(addr) match {
            case nc @ Child(addr, value, parentAddr) =>
              ListSpecs.forallContained(heap, parentFuncOnHeap, nc)

              findReturnsRootRec(parentAddr, fuel - 1)

            case Root(ad, value, rank) =>
              ()
          }
        else ()
      }.ensuring(_ =>
        !isValidAddr(findRec(addr, fuel)) ||
          nodeAtIsRoot(findRec(addr, fuel))
      )

      findReturnsRootRec(addr, size)
    }.ensuring(_ => !isValidAddr(find(addr)) || nodeAtIsRoot(find(addr)))

    // invalid in stainless: measure missing
    def findReturnsValidAddr(addr: BigInt): Unit = {
      def findReturnsValidAddrRec(addr: BigInt, fuel: BigInt): Unit = {
        require(fuel >= 0)
        decreases(fuel)

        if fuel == 0 then ()
        else if isValidAddr(addr) then
          nodeAt(addr) match {
            case nc @ Child(_, _, parentAddr) =>
              assert(heap.contains(nc))

              ListSpecs.forallContained(heap, parentFuncOnHeap, nc)

              assert(parentIsInHeap(nc, heap))

              assert(isValidAddr(parentAddr))

              findReturnsValidAddrRec(parentAddr, fuel - 1)

            case Root(_, _, _) =>
              ()
          }
        else ()
      }.ensuring(_ =>
        findRec(addr, fuel) == -1 ||
          (!isValidAddr(addr) || isValidAddr(findRec(addr, fuel)))
      )

      findReturnsValidAddrRec(addr, size)
    }.ensuring(_ =>
      find(addr) == -1 || (!isValidAddr(addr) || isValidAddr(find(addr)))
    )

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
