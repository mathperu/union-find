package union_find

import scala.collection.immutable.Map
sealed trait Node

case class Child[T](parent: T) extends Node
case class Root(rank: Int) extends Node

// val child: Node = Child(5)
// val root: Node = Root(2)

class UnionFind[T] (r: Map[T, Node]){
    def make(value: T): UnionFind[T] = {
        if r.contains(value) then
            this
        else
            new UnionFind(r + (value -> Root(0)))
    }

    def find(value: T): Option[T] = {
        r.get(value) match {
            case None => None
            case Some(Root(x)) => Some(value)
            case Some(Child(parent)) => find(parent)
        }
    }

    def eq(value1: T, value2: T): Boolean = find(value1) == find(value2)

    def link(value1: T, value2: T): UnionFind[T] = {
        (value1, value2) match {
            case (Some(root1), Some(root2)) 
                if root1 == root2 then this 
                else then
                    val rank1 = r(root1) match { case Root(rank) => rank }
                    val rank2 = r(root2) match { case Root(rank) => rank }

                    if rank1 < rank2 then
                        new UnionFind(r + (root1 -> Child(root2)))
                    else if rank1 > rank2 then
                        new UnionFind(r + (root2 -> Child(root1)))
                    else
                        new UnionFind(r + (root2 -> Child(root1)) + (root1 -> Root(rank1 + 1)))
            case _ => this
        }
    }

    def union(value1: T, value2: T): UnionFind[T] = link(find(value1), find(value2))
     
    def contains(v: T): Boolean = r.contains(v)

    def isRoot(x: T): Boolean = r.get(v) match
        case Option(Root(_)) => true
        case _ => false
    
}