import stainless.lang._
import stainless.collection._
import UnionFindStainless._

/**
 * Tests for the Stainless-compatible Union-Find implementation.
 * Run with: stainless src/main/scala/UnionFindStainless.scala src/main/scala/UnionFindStainlessTest.scala
 */
object UnionFindStainlessTest {

  // Test: make creates elements correctly
  def testMake(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()
    val (uf3, idx2) = uf2.make()

    idx0 == BigInt(0) &&
    idx1 == BigInt(1) &&
    idx2 == BigInt(2) &&
    uf3.size == BigInt(3) &&
    uf3.contains(idx0) &&
    uf3.contains(idx1) &&
    uf3.contains(idx2)
  }.holds

  // Test: initially each element is its own representative
  def testInitialFind(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()
    val (uf3, idx2) = uf2.make()

    val (_, r0) = uf3.find(idx0)
    val (_, r1) = uf3.find(idx1)
    val (_, r2) = uf3.find(idx2)

    r0 == idx0 &&
    r1 == idx1 &&
    r2 == idx2
  }.holds

  // Test: initially different elements are not equivalent
  def testInitialNotEquiv(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()

    !uf2.equiv(idx0, idx1)
  }.holds

  // Test: element is equivalent to itself
  def testSelfEquiv(): Boolean = {
    val (uf1, idx0) = empty.make()

    uf1.equiv(idx0, idx0)
  }.holds

  // Test: union makes elements equivalent
  def testUnionEquiv(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()

    val uf3 = uf2.union(idx0, idx1)

    uf3.equiv(idx0, idx1)
  }.holds

  // Test: union is transitive
  def testUnionTransitive(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()
    val (uf3, idx2) = uf2.make()

    val uf4 = uf3.union(idx0, idx1)  // 0 ~ 1
    val uf5 = uf4.union(idx1, idx2)  // 1 ~ 2, so 0 ~ 2

    uf5.equiv(idx0, idx2)
  }.holds

  // Test: union of disjoint sets
  def testUnionDisjoint(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()
    val (uf3, idx2) = uf2.make()
    val (uf4, idx3) = uf3.make()

    val uf5 = uf4.union(idx0, idx1)  // {0,1}
    val uf6 = uf5.union(idx2, idx3)  // {2,3}

    // {0,1} and {2,3} are disjoint
    !uf6.equiv(idx0, idx2) &&
    !uf6.equiv(idx1, idx3) &&
    uf6.equiv(idx0, idx1) &&
    uf6.equiv(idx2, idx3)
  }.holds

  // Test: merging two disjoint sets
  def testMergeSets(): Boolean = {
    val (uf1, idx0) = empty.make()
    val (uf2, idx1) = uf1.make()
    val (uf3, idx2) = uf2.make()
    val (uf4, idx3) = uf3.make()

    val uf5 = uf4.union(idx0, idx1)  // {0,1}
    val uf6 = uf5.union(idx2, idx3)  // {2,3}
    val uf7 = uf6.union(idx1, idx2)  // merge: {0,1,2,3}

    uf7.equiv(idx0, idx3)
  }.holds
}
