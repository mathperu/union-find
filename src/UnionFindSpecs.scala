package unionfind

import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import stainless.annotation._

import ourlistspecs.MoreListSpecs._
import UnionFindList._
import InvariantsHelpers._

object UnionFindSpecs {

  extension [T](uf: UF[T]) {

    /** Find returns a root node
      *
      * @param addr
      *   an arbitrary address in the union-find structure
      */
    def findReturnsRoot(addr: BigInt): Unit = {
      require(uf.isValidAddr(addr))
    }.ensuring(
      uf.nodeAtIsRoot(uf.find(addr))
    )

    /** Find returns a valid address
      *
      * @param addr
      *   an arbitrary address in the union-find structure
      */
    def findReturnsValidAddr(addr: BigInt): Unit = {
      require(uf.isValidAddr(addr))
    }.ensuring(
      uf.isValidAddr(uf.find(addr))
    )

    /** Make adds the given value to the domain (subset of [[T]]) of the
      * union-find structure
      *
      * @param value
      *   the value to be added
      */
    def makeAddsValueToDomain(value: T): Unit = {
      require(!uf.domain.contains(value))
      val (newUF, newNode) = uf.make(value)
      ListSpecs.mapDistributesOverAppend(uf.heap, newNode, _.value)

      assert(newUF.domain == uf.domain :+ value)
      assert(newUF.domain.contains(value))
    }.ensuring(_ => uf.make(value)._1.domain.contains(value))

    /** Make returns a singleton set containing the given value
      *
      * @param value
      *   the value to be added
      */
    def makeReturnsASingletonSet(value: T): Unit = {
      require(!uf.domain.contains(value))
      val (newUF, newNode) = uf.make(value)
    }.ensuring(_ =>
      val (newUF, newNode) = uf.make(value)
      isRoot(newNode)
      && newUF.find(newNode.addr) == newNode.addr
      && uf.rankIs(newNode, BigInt(0))
    )

    /** Link returns a root node
      *
      * @param a1
      *   the first root node
      * @param a2
      *   the second root node
      */
    def linkReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(
        uf.isValidAddr(a1) && uf.isValidAddr(a2) && uf.nodeAtIsRoot(a1) && uf
          .nodeAtIsRoot(
            a2
          )
      )
    }.ensuring(_ => uf.link(a1, a2)._2 == a1 || uf.link(a1, a2)._2 == a2)

    /** Union returns a root node
      *
      * @param a1
      *   the first arbitrary node
      * @param a2
      *   the second arbitrary node
      */
    def unionReturnsARootOfInput(a1: BigInt, a2: BigInt): Unit = {
      require(uf.isValidAddr(a1) && uf.isValidAddr(a2))
    }.ensuring(_ =>
      uf.union(a1, a2)._2 == uf.find(a1) || uf.union(a1, a2)._2 == uf.find(a2)
    )
  }
}
