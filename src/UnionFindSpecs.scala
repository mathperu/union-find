package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import stainless.annotation._

import ourlistspecs.OurListSpecs
import UnionFindList._
import InvariantsHelpers._

object UnionFindSpecs {

  extension [T](uf: UF[T]) {
    def findReturnsRoot(addr: BigInt): Unit = {
      require(uf.isValidAddr(addr))
    }.ensuring(
      uf.nodeAtIsRoot(uf.find(addr))
    )
    def findReturnsValidAddr(addr: BigInt): Unit = {
      require(uf.isValidAddr(addr))
    }.ensuring(
      uf.isValidAddr(uf.find(addr))
    )

    def makeAddsValueToDomain(value: T): Unit = {
      require(!uf.domain.contains(value))
      val (newUF, newNode) = uf.make(value)
      OurListSpecs.mapDistributesOverAppend(uf.heap, newNode, _.value)

      assert(newUF.domain == uf.domain :+ value)
      assert(newUF.domain.contains(value))
    }.ensuring(_ => uf.make(value)._1.domain.contains(value))

    def makeReturnsASingletonSet(value: T): Unit = {
      require(!uf.domain.contains(value))
      val (newUF, newNode) = uf.make(value)
    }.ensuring(_ =>
      val (newUF, newNode) = uf.make(value)
      isRoot(newNode)
      && newUF.find(newNode.addr) == newNode.addr
      && uf.rankIs(newNode, BigInt(0))
    )

    def linkReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(
        uf.isValidAddr(a1) && uf.isValidAddr(a2) && uf.nodeAtIsRoot(a1) && uf
          .nodeAtIsRoot(
            a2
          )
      )
    }.ensuring(_ => uf.link(a1, a2)._2 == a1 || uf.link(a1, a2)._2 == a2)

    def unionReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(uf.isValidAddr(a1) && uf.isValidAddr(a2))
    }.ensuring(_ =>
      uf.union(a1, a2)._2 == uf.find(a1) || uf.union(a1, a2)._2 == uf.find(a2)
    )

    def updatedListPreservesFind(
        rootAddr: BigInt,
        n: Node[T],
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(rootAddr))
      require(uf.isValidAddr(b))
      require(uf.find(b) == rootAddr)

      // val updatedUF = UF(uf.heap.updated(addr, n))

      // if uf.find(b) == addr then assert(updatedUF.find(b) == n.parent)
      // else assert(updatedUF.find(b) == uf.find(b))
    }.ensuring(_ => {
      val updatedUF = UF(uf.heap.updated(rootAddr, n))
      updatedUF.find(b) == rootAddr
    })

    // def findEquivToListTraversal(addr: BigInt) = {

    // }.ensuring(
    //   uf.find(addr) == uf.heap.
    // )

    // other ideas
    // if uf.find(b) == a1 then after link newUF.find(b) == newRoot

    def linkPreservesParentChain(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      require(uf.nodeAtIsRoot(a1))
      require(uf.nodeAtIsRoot(a2))

      def inner(tail1: List[Node[T]], tail2: List[Node[T]]): Unit = {
        (tail1, tail2) match {
          case (Nil(), Nil())               => ()
          case (Cons(h1, t1), Cons(h2, t2)) =>
            assert(h1 == h2)
            inner(t1, t2)
          case _ => ()
        }
      }.ensuring(_ => tail1.tail == tail2.tail)

      val (newUF, newRoot) = uf.link(a1, a2)
      inner(uf.buildParentChain(b).tail, newUF.buildParentChain(b).tail)
    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)
      uf.buildParentChain(b).tail == newUF.buildParentChain(b).tail
    })

    /** Lemma: updating a node that isn't b's root implies invariance of find(b):
      *
      *  ```uf.find(b) != addr => uf.set(addr, n).find(b) == uf.find(b)```
      *
      * @param addr
      *   the address to update
      * @param n
      *   the new node to set at addr
      * @param b
      *   the address whose find result should be preserved
      */
    def setMaintainsFind(addr: BigInt, n: Node[T], b: BigInt): Unit = {
      require(uf.isValidAddr(addr))
      require(uf.isValidAddr(b))
      require(addr == n.addr)

      // TODO assert a bunch of invariants on n, or copy paste from set

      require(uf.nodeAtIsRoot(addr))
      require(uf.find(b) != addr)
    }.ensuring(_ => {
      val newUF = uf.set(addr, n)
      newUF.nodeAtIsRoot(addr)
      newUF.find(b) == uf.find(b)
    })

    def parentChainSublistImpliesFind(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      require(uf.nodeAtIsRoot(a1))
      require(uf.nodeAtIsRoot(a2))
      require(
        uf.buildParentChain(b)
          .content
          .subsetOf(uf.link(a1, a2)._1.buildParentChain(b).content)
      )

      // val parentsBefore = uf.buildParentChain(b)
      // val (newUF, newRoot) = uf.link(a1, a2)
      // val parentsAfter = newUF.buildParentChain(b)
    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)
      val parentsBefore = uf.buildParentChain(b)
      val parentsAfter = newUF.buildParentChain(b)

      parentsAfter.head.addr == newRoot
      // implies newUF.find(b) = newRoot
    })

    def setTwoFind(
        ar: BigInt,
        r: Root[T],
        ac: BigInt,
        c: Child[T],
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(ar))
      require(uf.isValidAddr(r.addr))
      require(r.addr == ar)

      require(uf.isValidAddr(ac))
      require(uf.isValidAddr(c.addr))
      require(c.addr == ac)

      require(uf.find(b) == ar || uf.find(b) == ac)

      require(ar != ac)
    }.ensuring(_ => {
      val newUF = uf.setTwo(ar, r, ac, c)
      newUF.find(b) == ar
    })

    def linkPreservesOneRoot(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      require(uf.nodeAtIsRoot(a1))
      require(uf.nodeAtIsRoot(a2))

      require(uf.find(b) == a1 || uf.find(b) == a2)

      val (newUF, newRoot) = uf.link(a1, a2)
      val parentsBefore = uf.buildParentChain(b)
      val parentsAfter = newUF.buildParentChain(b)

      (uf.nodeAt(a1), uf.nodeAt(a2)) match {
        case (n1, n2) =>
          if n1.rank < n2.rank then
            // (newRoot == a2) passes
            // (newUF.heap.contains(uf.nodeAt(b))) doesn't pass
            val newChild = Child(a1, n1.value, n1.rank, a2)
            assert(
              newUF.heap == uf.heap.updated(a1, newChild)
            ) // passes

            assert(
              parentsBefore.head.addr == a1 || parentsBefore.head.addr == a2
            ) // passes

            // assert(parentsAfter.head.addr == a1 || parentsAfter.head.addr == a2)

            // assert(parentsAfter.head.addr == newRoot)
            // assert(parentsBefore.content.subsetOf(parentsAfter.content))

            // disjunction: uf.buildParentChain(b)
            linkPreservesParentChain(a1, a2, b)

            if uf.find(b) == a1 then
              // TODO: set is on same root as b
              assert(parentsBefore.content.subsetOf(parentsAfter.content))
              parentChainSublistImpliesFind(a1, a2, b)
              assert(newUF.find(b) == a2)
            else setMaintainsFind(a1, newUF.nodeAt(a1), b)
          else if n1.rank > n2.rank then
            assert(newRoot == a1)
            // assert(newUF.heap.contains(uf.nodeAt(b)))
            // updatedListPreservesFind(a1, newUF.nodeAt(a1), b)
            if uf.find(b) == a2 then
              // TODO: set is on same root as b
              assert(newUF.find(b) == a1)
              assert(parentsBefore.content.subsetOf(parentsAfter.content))
              parentChainSublistImpliesFind(a1, a2, b)
            else setMaintainsFind(a2, newUF.nodeAt(a2), b)
          else
            assert(newRoot == a1)
            // assert(newUF.heap.contains(uf.nodeAt(b)))
            // updatedListPreservesFind(a1, newUF.nodeAt(a1), b)
            // TODO: rank increased
            // OurListSpecs.updateOrderDoesNotMatter(
            //   uf.heap,
            //   a1,
            //   Root(a1, n1.value, n1.rank + 1),
            //   a2,
            //   Child(a2, n2.value, n2.rank, a1)
            // )

            assert(a1 != a2)
            setTwoFind(
              a1,
              Root(a1, n1.value, n1.rank + 1),
              a2,
              Child(a2, n2.value, n2.rank, a1),
              b
            )
            assert(newUF.find(b) == a1)
      }

    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)
      newUF.find(b) == a1 || newUF.find(b) == a2
    })

    def linkNeitherRoot(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      require(uf.nodeAtIsRoot(a1))
      require(uf.nodeAtIsRoot(a2))

      require(uf.find(b) != a1 && uf.find(b) != a2)
    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)
      newUF.find(b) != a1 && newUF.find(b) != a2
    })

    // if b is represented by either a1 or a2 then after union b it is represented by their union
    def unionMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      val r1 = uf.find(a1)
      val r2 = uf.find(a2)
      val (newUF, newRoot) = uf.union(a1, a2)

      if uf.equiv(a1, b) || uf.equiv(a2, b) then
        // assert(uf.nodeAtIsRoot(r1) || uf.nodeAtIsRoot(r2))
        // check(uf.find(b) == r1 || uf.find(b) == r2)
        linkPreservesOneRoot(r1, r2, b)
        // check(newRoot == r1 || newRoot == r2)
        // check(newUF.find(b) == r1 || newUF.find(b) == r2)
      else
        // check(!uf.equiv(a1, b) && !uf.equiv(a2, b))
        // check(uf.find(b) != r1 && uf.find(b) != r2)
        linkNeitherRoot(r1, r2, b)
        // assert(newUF.find(b) != newRoot)

      // a1 and a2 in same set => their roots are the same
    }.ensuring(_ => {
      val (newUF, newRoot) = uf.union(a1, a2)

      (!(uf.equiv(a1, b) || uf.equiv(a2, b)) || newUF
        .find(b) == newRoot)
      && ((uf.equiv(a1, b) || uf.equiv(a2, b)) || newUF
        .find(b) != newRoot)
    })
  }

}
