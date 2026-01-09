import unionfind.UnionFindList._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import unionfind.morelistspecs.MoreListSpecs

object UFExample {

  /** ```
    *      0    2                      0
    *     /      \    union(3, 4)     / \
    *    1        4   ──────────►   1    2
    *   /                          /      \
    *  3                          3        4
    * ```
    */
  def exampleUsage(): Unit = {
    val uf = emptyUF[BigInt]()

    assert(uf.domain == Nil())
    val (uf1, _) = uf.make(0)
    MoreListSpecs.appendToNil(uf.domain, 0)
    MoreListSpecs.singletonList(uf.domain :+ 0, 0)
    assert(uf1.domain == uf.domain :+ 0)
    assert(uf1.domain == Nil() :+ 0)
    assert(uf1.domain == Cons(0, Nil()))
    val (uf2, _) = uf1.make(1)
    val (uf3, _) = uf2.make(2)
    val (uf4, _) = uf3.make(3)
    val (uf5, _) = uf4.make(4)

    // val domain = stainless.collection.List[BigInt](0, 1, 2, 3, 4)
    // val rootUF = domain.foldLeft(uf) { (currentUF, value) =>
    //   val (newUF, node) = currentUF.make(value)
    //   newUF
    // }

    // val unions =
    //   stainless.collection.List[(BigInt, BigInt)]((0, 1), (1, 3), (2, 4))
    // val ufSep = unions.foldLeft(uf1) { (currentUF, pair) =>
    //   val (a, b) = pair
    //   val (newUF, _) = currentUF.union(a, b)
    //   newUF
    // }

    val (ufSep1, _) = uf5.union(0, 1)
    val (ufSep2, _) = ufSep1.union(1, 3)
    val (ufSep3, _) = ufSep2.union(2, 4)

    val (ufFinal, _) = ufSep3.union(3, 4)
  }
}
