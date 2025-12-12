import stainless.lang._
import stainless.proof._
import stainless.collection._
import stainless.annotation._

object UnionFindRec {

    sealed abstract class Node[T]
    case class Child[T](value: T, parent: Node[T], rank: BigInt) extends Node[T]
    case class Root[T](value: T, rank: BigInt) extends Node[T]

    def containsParent[T](node: Node[T], nodes: List[Node[T]]): Boolean = {
        require(nodes.contains(node))
        node match {
            case Child(value, parent, rank) => nodes.contains(node)
            case Root(value, rank) => true
        }
    }

    case class UFRec[T](nodes: List[Node[T]]){
        // if node in uf, then parent in uf too
        val pred = (nodes: List[Node[T]]) => (n: Node[T]) => (!nodes.contains(n) || containsParent[T](n, nodes))
        val invariant = nodes.forall(pred(nodes))
        require(invariant)

        def domain = nodes.map(n => 
            n match {
                case Child(v, _, _) => v
                case Root(v, _) => v
            }
        )
        
        def contains(elem: T) = domain.contains(elem)

        def containsNode(node: Node[T]) = nodes.contains(node)

        def isRoot(node: Node[T]): Boolean =
            node match {
                case Child(value, parent, rank) => false
                case Root(value, rank) => true
            }

        def make(elem: T): UFRec[T] = {
            val newNode = Root[T](elem, 0)
            val newNodes = Cons(newNode, nodes)
            assert(containsParent(newNode, newNodes))
            /* forallContains(newNodes)
            forallContains(nodes) */
            ListSpecs.subsetRefl(nodes)
            ListSpecs.subsetRefl(newNodes)
            assert(newNodes.forall(x => newNodes.contains(x)))
            // need to show that if parent is in nodes, then parent is in new nodes
            ListSpecs.applyForAll(newNodes, newNodes.size - 1, pred(newNodes))
            assert(Nil[T]().forall(x => x == x))
            assert(newNodes.forall(pred(newNodes)))
            val newUF = UFRec(newNodes)
            newUF
        }

        def find(node: Node[T]): Node[T] = {
            node match {
                case Child(value, parent, rank) => find(parent)
                case Root(_, _) => node
            }
        }.ensuring(y => isRoot(y))

        
        
        def link = ???
        def union = ???
    }
}
