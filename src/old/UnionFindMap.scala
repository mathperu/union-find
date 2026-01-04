package unionfind

//import stainless.lang._
//import Map._
import stainless.lang.{Option, None, Some, decreases, Map}
import stainless.collection._
import stainless.annotation._


object UnionFindMap {

  sealed trait Node[T]
  case class Child[T](parent: T) extends Node[T]
  case class Root[T](rank: BigInt) extends Node[T]

  case class UF[T](r: Map[T, Node[T]], size: BigInt) {
    require(size >= 0)

    def contains(x: T): Boolean = r.contains(x)

    def make(value: T): UF[T] = {
      if (r.contains(value)) this
      else new UF(r + (value -> Root[T](0)), size + 1)
    }    

    def simpleFind(value: T): T = {
      def simpleFindDecreases(value: T, maxDepth: BigInt): T = {
        require(maxDepth >= 0 && maxDepth <= size && (maxDepth > 0 || isRoot(value)))
        decreases(maxDepth)
        if maxDepth == 0 then value
        else
          r.get(value) match {
            case Some(Child(parent)) => simpleFindDecreases(parent, maxDepth-1)
            case _ => value
          }
      }.ensuring(y => isRoot(y))
      simpleFindDecreases(value, size)
    }.ensuring(y => isRoot(y))

    def simpleEquiv(x: T, y: T): Boolean = {
      // TODO extend to elements not in set ?
      require(contains(x) && contains(y))
      simpleFind(x) == simpleFind(y)
    } // TODO change to find when possible


    def link(v1: T, v2: T): UF[T] = 
      require(isRoot(v1) && isRoot(v2))
      
      if (v1 == v2) this
      else {
        val rank1: BigInt = getRank(v1)
        val rank2: BigInt = getRank(v2)

        if (rank1 < rank2)
          UF(r + (v1 -> Child[T](v2)), size)
        else if (rank1 > rank2)
          UF(r + (v2 -> Child[T](v1)), size)
        else
          UF(r + (v2 -> Child[T](v1)) + (v1 -> Root[T](rank1 + 1)), size)
      }

    def simpleUnion(x: T, y: T): UF[T] = {
      require(contains(x) && contains(y))
      link(simpleFind(x), simpleFind(y))
    }

    def isRoot(x: T): Boolean = {
      r.get(x) match {
        case Some(Root(r)) => true
        case None() => true
        case _ => false
      }
    }

    def getRank(x: T): BigInt = {
      require(isRoot(x))
      r.get(x) match {
        case Some(Root(rank)) => rank
        case _ => 0
      }
    }
  } 

  def empty[T]: UF[T] = UF(Map[T, Node[T]](), 0)

  /* def idempotentLemma[T](uf: UF[T], x: T): Boolean = {
    require(uf.contains(x))
    val r = uf.simpleFind(x).get
    !uf.contains(r) || uf.simpleFind(r) == r
  } */

}


