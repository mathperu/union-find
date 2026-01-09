import unionfind.UnionFindList._
import stainless.collection.{List, ListSpecs, Nil, Cons}
import unionfind.morelistspecs.MoreListSpecs
import unionfind.morelistspecs.MoreListSpecs.snocNil
import unionfind.UnionFindSpecs
import unionfind.InvariantsHelpers.isValidAddr
import stainless.annotation.ghost

object UFExample {

  /** ```
    *      0    2                      0
    *     /      \    union(3, 4)     / \
    *    1        4   ──────────►   1    2
    *   /                          /      \
    *  3                          3        4
    * ```
    */
  def exampleUsage()(implicit @ghost state: stainless.io.State): Unit = {
    val uf = emptyUF[BigInt]()

    val (uf1, _) = uf.make(0)

    // needed to prove that the domain is correctly initialized
    MoreListSpecs.snocNil(0)

    val (uf2, _) = uf1.make(1)
    val (uf3, _) = uf2.make(2)
    val (uf4, _) = uf3.make(3)
    val (uf5, _) = uf4.make(4)

    val (ufSep1, _) = uf5.union(0, 1)
    val (ufSep2, _) = ufSep1.union(1, 3)
    val (ufSep3, _) = ufSep2.union(2, 4)
    val (ufFinal, _) = ufSep3.union(3, 4)
  }
}
