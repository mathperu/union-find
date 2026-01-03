import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
import stainless.annotation._
import stainless.collection.Cons

object OurListSpecs {
    def appendedElementIsAtIndexOldSize[T](l: List[T], elem: T): Unit = {
        decreases(l)
        l match {
            case Nil() => 
            case Cons(h, t) => appendedElementIsAtIndexOldSize(t, elem)
        }
    }.ensuring{_ => (l :+ elem)(l.size) == elem}

    def forallAppend[T](l: List[T], elem: T, p: T => Boolean): Unit = {
        require(l.forall(p) && p(elem))
        decreases(l)
        (l :+ elem, l) match {
            case (Nil(), _) => ()
            case (Cons(h, Nil()), Nil()) => 
                assert(h == elem)
                assert(p(elem))
            case (Cons(h1, t1), Cons(h2, t2)) => 
                assert(h1 == h2)
                assert(p(h1))
                assert(p(h2))
                forallAppend(t2, elem, p)
        }
    }.ensuring{_ => (l :+ elem).forall(p)}

    def appendPreservesIndices[T](l: List[T], n: T, i: BigInt): Unit = {
        require(0 <= i && i < l.size)
        decreases(l)
        (l :+ n, l) match {
            case (Nil(), _) => ()
            case (Cons(h1, Nil()), Nil()) => 
                assert(h1 == n)
                assert(i < 0)
            case (Cons(h1, t1), Cons(h2, t2)) => 
                assert(h1 == h2)
                if (i == 0) then ()
                else appendPreservesIndices(t2, n, i-1)
        }
    }.ensuring{_ => (l :+ n)(i) == l(i)}

    def weakenForAll[T](l: List[T], p: T => Boolean, q: T => Boolean): Unit = {
        require(l.forall(e => p(e) && q(e)))
    }.ensuring(_ => l.forall(p))

    /* def predOnSameLists[T](l1: List[T], l2: List[T], m1: List[T], m2: List[T], p: (T, List[T]) => Boolean): Unit = {
        require(l1 == l2 && m1 == m2 && forallRec(l1, p(_, m1)))
        (l1, l2) match {
            case (Nil(), Nil()) => ()
            case (Cons(h1, t1), Cons(h2, t2)) => 
                assert(h1 == h2)
                assert(m1 == m2)
                assert(p(h1, m1))
                assert(p(h2, m2))
                assert(t1 == t2)
                assert(forallRec(t1, p(_, m1)))
                predOnSameLists(t1, t2, m1, m2, p)
        }
    }.ensuring(_ => forallRec(l2, p(_, m2))) */
}
