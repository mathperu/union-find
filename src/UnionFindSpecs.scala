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
    }.ensuring(_ =>
      isRoot(uf.make(value)._2)
        && (uf.find(uf.make(value)._2.addr) == BigInt(-1) || uf.find(
          uf.make(value)._2.addr
        ) == uf.make(value)._2.addr)
        && uf.rankIs(uf.make(value)._2, BigInt(0))
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

    def linkMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      require(uf.nodeAtIsRoot(a1))
      require(uf.nodeAtIsRoot(a2))

    }.ensuring(_ => {
      val (newUF, newRoot) = uf.link(a1, a2)

      (!(uf.equiv(a1, b) || uf.equiv(a2, b)) || newUF
        .find(b) == newRoot)
      && ((uf.equiv(a1, b) || uf.equiv(a2, b)) || newUF
        .find(b) != newRoot)
    })

    // if b is represented by either a1 or a2 then after union b it is represented by their union
    def unionMergedTheSets(a1: BigInt, a2: BigInt, b: BigInt): Unit = {
      require(uf.isValidAddr(a1))
      require(uf.isValidAddr(a2))
      require(uf.isValidAddr(b))

      linkMergedTheSets(uf.find(a1), uf.find(a2), b)
      if uf.equiv(a1, b) || uf.equiv(a2, b) then
        val (newUF, newRoot) = uf.union(a1, a2)
        assert(newUF.find(b) == newRoot)
      else
        val (newUF, newRoot) = uf.union(a1, a2)
        assert(newUF.find(b) != newRoot)

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
