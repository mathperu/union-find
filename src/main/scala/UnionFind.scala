import scala.collection.immutable.Map

sealed trait Node[T]

case class Child[T](parent: T) extends Node[T]
case class Root[T](rank: Int) extends Node[T]

class UnionFind[T](val r: Map[T, Node[T]]) {
  def this() = this(Map.empty)

  def make(value: T): UnionFind[T] = {
    if (r.contains(value)) this
    else new UnionFind(r + (value -> Root[T](0)))
  }

  // Find the representative (root) of `value` WITH path compression.
  // Returns (updated UnionFind, Option[root]).
  // After calling find, the node `value` points directly to its root.
  def find(value: T): (UnionFind[T], Option[T]) = {
    r.get(value) match {
      case None => (this, None)
      case Some(_: Root[T]) => (this, Some(value))
      case Some(Child(parent)) =>
        val (uf1, rootOpt) = find(parent)
        rootOpt match {
          case None => (uf1, None)
          case Some(root) =>
            if (parent == root) {
              // parent is already the root, no compression needed
              (uf1, Some(root))
            } else {
              // Path compression: point `value` directly to `root`
              val uf2 = new UnionFind(uf1.r + (value -> Child[T](root)))
              (uf2, Some(root))
            }
        }
    }
  }

  // Convenience: find without needing the updated UF (loses path compression benefit)
  def findRoot(value: T): Option[T] = find(value)._2

  def equiv(value1: T, value2: T): Boolean = {
    val (uf1, r1) = find(value1)
    val (_, r2) = uf1.find(value2)
    r1 == r2
  }

  // Version of equiv that also returns the updated UF with compressed paths
  def equivWithCompression(value1: T, value2: T): (UnionFind[T], Boolean) = {
    val (uf1, r1) = find(value1)
    val (uf2, r2) = uf1.find(value2)
    (uf2, r1 == r2)
  }

  // `link` takes optional representatives (as returned by `find`).
  def link(o1: Option[T], o2: Option[T]): UnionFind[T] = (o1, o2) match {
    case (Some(root1), Some(root2)) =>
      if (root1 == root2) this
      else {
        val rank1 = r(root1) match { case Root(rank) => rank; case _ => 0 }
        val rank2 = r(root2) match { case Root(rank) => rank; case _ => 0 }

        if (rank1 < rank2)
          new UnionFind(r + (root1 -> Child[T](root2)))
        else if (rank1 > rank2)
          new UnionFind(r + (root2 -> Child[T](root1)))
        else
          new UnionFind(r + (root2 -> Child[T](root1)) + (root1 -> Root[T](rank1 + 1)))
      }
    case _ => this
  }

  def union(value1: T, value2: T): UnionFind[T] = {
    val (uf1, r1) = find(value1)
    val (uf2, r2) = uf1.find(value2)
    uf2.link(r1, r2)
  }

  override def toString: String = r.toString
}

object UnionFind {
  def empty[T]: UnionFind[T] = new UnionFind[T]()
}
