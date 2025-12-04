object UnionFindTest {
  def main(args: Array[String]): Unit = {
    val uf0 = UnionFind.empty[Int]

    // create elements 1..5
    val uf1 = (1 to 5).foldLeft(uf0)((u, v) => u.make(v))

    // Initially none are equivalent (except same element)
    assert(uf1.equiv(1, 1))
    assert(!uf1.equiv(1, 2))

    // Union some pairs and test
    val uf2 = uf1.union(1, 2)
    assert(uf2.equiv(1, 2))

    val uf3 = uf2.union(3, 4)
    assert(uf3.equiv(3, 4))

    val uf4 = uf3.union(2, 4) // join the sets {1,2} and {3,4}
    assert(uf4.equiv(1, 3) && uf4.equiv(2, 4))

    // union with unknown element should be a no-op (unknowns not present)
    val uf5 = uf4.union(10, 1)
    assert(!uf5.findRoot(10).isDefined)

    // Test path compression: after find, node should point directly to root
    val ufChain = UnionFind.empty[Int]
      .make(1).make(2).make(3).make(4)
      .union(1, 2)  // 1 -> 2 (or 2 -> 1)
      .union(2, 3)  // chain extends
      .union(3, 4)  // longer chain


    // Find from node 1 - should compress the path
    val (ufCompressed, root1) = ufChain.find(1)
    assert(root1.isDefined)

    // After compression, node 1 should point directly to the root
    val node1After = ufCompressed.r.get(1)
    node1After match {
      case Some(Child(parent)) => assert(parent == root1.get, s"Path compression failed: 1 -> $parent, expected 1 -> ${root1.get}")
      case Some(_: Root[Int]) => () // 1 is the root, that's fine
      case None => assert(false, "Node 1 should exist")
    }

    println("All basic UnionFind tests passed (with path compression).")
  }
}
