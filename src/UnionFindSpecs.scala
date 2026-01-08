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
        uf.isValidAddr(a1) && uf.isValidAddr(a2) &&
          uf.nodeAtIsRoot(a1) && uf.nodeAtIsRoot(a2)
      )
    }.ensuring(_ => uf.link(a1, a2)._2 == a1 || uf.link(a1, a2)._2 == a2)

    def unionReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(uf.isValidAddr(a1) && uf.isValidAddr(a2))
    }.ensuring(_ =>
      uf.union(a1, a2)._2 == uf.find(a1) || uf.union(a1, a2)._2 == uf.find(a2)
    )

    def unionPreservesAdressValidity(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))
    }.ensuring(_ =>
      val (newUF, newRoot) = uf.union(a1, a2)
      newUF.isValidAddr(b)
    )

    // non-verified :

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
    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)
      uf.buildParentChain(b).tail == newUF.buildParentChain(b).tail
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
            // OurListSpecs.mapAtIndex(newUF.heap, a1, _.parent == a2)
            // OurListSpecs.mapAtIndex(newUF.heap, a2, _.rank == n2.rank)
            // assert(newRoot == a2)
            // assert(newUF.heap.contains(uf.nodeAt(b)))
            val newChild = Child(a1, n1.value, n1.rank, a2)
            // assert(newUF.heap == uf.heap.updated(a1, newChild))
            // updatedListPreservesFind(a2, newUF.nodeAt(a2), b)

            assert(
              parentsBefore.head.addr == a1 || parentsBefore.head.addr == a2
            )
            // linkPreservesParentChain(a1, a2, b)
            // assert(parentsAfter.head.addr == a1 || parentsAfter.head.addr == a2)

            // assert(parentsAfter.head.addr == newRoot)

            // disjunction: uf.buildParentChain(b)
            if uf.find(b) == a1 then assert(newUF.find(b) == a2)
            else
              assert(parentsBefore.content.subsetOf(parentsAfter.content))
              // assert(parentsAfter.head.addr == )
              assert(newUF.find(b) == a2)
          else if n1.rank > n2.rank then
            // OurListSpecs.mapAtIndex(newUF.heap, a2, _.parent == a1)
            // OurListSpecs.mapAtIndex(newUF.heap, a1, _.rank == n1.rank)
            assert(newRoot == a1)
            assert(newUF.heap.contains(uf.nodeAt(b)))
            // updatedListPreservesFind(a1, newUF.nodeAt(a1), b)
            assert(newUF.find(b) == a1)
          else
            // OurListSpecs.mapAtIndex(newUF.heap, a2, _.parent == a1)
            // OurListSpecs.mapAtIndex(newUF.heap, a1, _.rank == n1.rank + 1)
            assert(newRoot == a1)
            assert(newUF.heap.contains(uf.nodeAt(b)))
            // updatedListPreservesFind(a1, newUF.nodeAt(a1), b)
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

    def lemma(r1: BigInt, r2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(r1))
      require(uf.isValidAddr(r2))
      require(uf.isValidAddr(b))
      require(uf.nodeAtIsRoot(r1))
      require(uf.nodeAtIsRoot(r2))
      require(uf.union(r1, r2)._2 == r1)
      require(uf.equiv(r1, b))
    }.ensuring(_ =>
      val (newUF, newRoot) = uf.union(r1, r2)
      newUF.find(b) == r1
    )

    def hasSameRootAsAncestors(a1: BigInt, a2: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.ancestors(a1).contains(a2))
    }.ensuring(_ => uf.equiv(a1, a2))

    def unionOnRootsIsUnionOnAny(
        a1: BigInt,
        a2: BigInt,
        r1: BigInt,
        r2: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(r1))
      require(uf.isValidAddr(r2))
      require(uf.find(a1) == r1)
      require(uf.find(a2) == r2)
    }.ensuring(_ => uf.union(a1, a2) == uf.union(r1, r2))

    def unionMergedTheSets1(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))
      require(uf.equiv(a1, b) || uf.equiv(a2, b))

      val r1 = uf.find(a1)
      val r2 = uf.find(a2)
      val rb = uf.find(b)
      val (newUF, newRoot) = uf.union(a1, a2)

      unionPreservesAdressValidity(a1, a2, b)
      unionPreservesAdressValidity(a1, a2, a1)
      unionPreservesAdressValidity(a1, a2, a2)
      unionPreservesAdressValidity(a1, a2, r1)
      unionPreservesAdressValidity(a1, a2, r2)

      unionOnRootsIsUnionOnAny(a1, a2, r1, r2)

      if uf.equiv(a1, b) then
        unionReturnsARootOfInput(a1, a2)
        assert(newRoot == r1 || newRoot == r2)
        assert(rb == r1)
        if newRoot == r1 then
          assert(uf.union(r1, r2)._1 == newUF)
          lemma(r1, r2, b)
          assert(rb == newUF.find(b))
          assert(newUF.find(b) == r1)
          assert(newUF.find(b) == newRoot)
        else
          assert(newRoot == r2)
          assert(newUF.ancestors(b).contains(r1))
          newUF.nodeAt(r1) match
            case Root(_, _, _)      => ()
            case Child(_, _, _, pa) => assert(pa == r2)

          assert(newUF.find(a1) == newRoot)
          assert(newUF.find(b) == newUF.find(a1))
          assert(newUF.find(b) == newRoot)
      else if uf.equiv(a2, b) then
        unionReturnsARootOfInput(a1, a2)
        assert(newRoot == uf.find(a1) || newRoot == uf.find(a2))
        assert(uf.find(b) == uf.find(a2))
        if newRoot == uf.find(a2) then assert(newUF.find(b) == newRoot)
        else
          assert(newRoot == uf.find(a1))
          assert(newUF.find(a2) == newRoot)
          assert(newUF.find(b) == newUF.find(a2))
          assert(newUF.find(b) == newRoot)

    }.ensuring(_ =>
      val (newUF, newRoot) = uf.union(a1, a2)
      unionPreservesAdressValidity(a1, a2, b)
      newUF.find(b) == newRoot
    )

    def unionPreservesRootForElementsInNeitherSets(
        a1: BigInt,
        a2: BigInt,
        b: BigInt
    ): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))
      require(!uf.equiv(a1, b) && !uf.equiv(a2, b))

      val r1 = uf.find(a1)
      val r2 = uf.find(a2)
      val (newUF, newRoot) = uf.union(a1, a2)

      val bRoot = uf.find(b)

      unionPreservesAdressValidity(a1, a2, b)

    }.ensuring(_ =>
      val (newUF, newRoot) = uf.union(a1, a2)
      unionPreservesAdressValidity(a1, a2, b)
      newUF.find(b) == uf.find(b)
    )

    def unionMergedTheSets2(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))
      require(!uf.equiv(a1, b) && !uf.equiv(a2, b))

      val r1 = uf.find(a1)
      val r2 = uf.find(a2)
      val (newUF, newRoot) = uf.union(a1, a2)
      unionReturnsARootOfInput(a1, a2)
      unionPreservesAdressValidity(a1, a2, b)
      unionPreservesRootForElementsInNeitherSets(a1, a2, b)

    }.ensuring(_ =>
      val (newUF, newRoot) = uf.union(a1, a2)
      newUF.find(b) != newRoot
    )

    // if b is represented by either a1 or a2 then after union b it is represented by their union
    def unionMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      val r1 = uf.find(a1)
      val r2 = uf.find(a2)
      val (newUF, newRoot) = uf.union(a1, a2)

      if uf.equiv(a1, b) then
        unionReturnsARootOfInput(a1, a2)
        assert(newRoot == uf.find(a1) || newRoot == uf.find(a2))
        assert(uf.find(b) == uf.find(a1))
        if newRoot == uf.find(a1) then ()
        else
          assert(newRoot == uf.find(a2))
          assert(newUF.find(a1) == newRoot)
          assert(newUF.find(b) == newUF.find(a1))
      else if uf.equiv(a2, b) then ()
      // assert(uf.nodeAtIsRoot(r1) || uf.nodeAtIsRoot(r2))
      // check(uf.find(b) == r1 || uf.find(b) == r2)
      /* linkPreservesOneRoot(r1, r2, b)
        unionReturnsARootOfInput(a1, a2) */

      // check(newRoot == r1 || newRoot == r2)
      // check(newUF.find(b) == r1 || newUF.find(b) == r2)
      else
        val bRoot = uf.find(b)
        assert(bRoot != r1 && bRoot != r2)
        unionReturnsARootOfInput(a1, a2)
        // check(!uf.equiv(a1, b) && !uf.equiv(a2, b))
        // check(uf.find(b) != r1 && uf.find(b) != r2)
        // linkNeitherRoot(r1, r2, b)
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
