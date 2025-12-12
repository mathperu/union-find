import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._

object UnionFindRec {

   /*  def listspec[T](list: List[T], elem: T, prop: T => Boolean): Unit = {
        require(list.forall(prop) && prop(elem))

    }.ensuring((list :+ elem).forall(prop)) */

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
            val newNodes = nodes :+ newNode
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
