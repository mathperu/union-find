import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs}
import stainless.annotation._
import stainless.collection.Cons

object OurListSpecs {
    def appendedElementIsAtIndexOldSize[T](l: List[T], elem: T): Unit = {
    }.ensuring{_ => (l :+ elem)(l.size) == elem}

    def forallAppend[T](l: List[T], elem: T, p: T => Boolean): Unit = {
        require(l.forall(p) && p(elem))
    }.ensuring{_ => (l :+ elem).forall(p)}

    def staysBoundedAppend[T](l: List[T], elem: T, f: T => BigInt): Unit = {
        require(l.forall(e => 0 <= f(e) && f(e) < l.size))
    }.ensuring(_ => l.forall(e => 0 <= f(e) && f(e) < (l :+ elem).size))

    def weakenForAll[T](l: List[T], p: T => Boolean, q: T => Boolean): Unit = {
        require(l.forall(e => p(e) && q(e)))
    }.ensuring(_ => l.forall(p))
}
