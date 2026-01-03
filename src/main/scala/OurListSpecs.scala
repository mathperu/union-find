import stainless.lang._
import stainless.proof._
import stainless.collection.{List, ListSpecs, Nil}
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

    def appendDoesNotChangeIndices[T](l: List[T], elem: T, i: BigInt): Boolean = {
        require(0 <= i && i < l.size)
        l(i) == (l :+ elem)(i)
    }.holds

    def test[T](l: List[T], elem: T, newE: T, f: T => BigInt): Boolean = {
        require(if 0 <= f(elem) && f(elem) < l.size then l(f(elem)) == elem else false)
        if 0 <= f(elem) && f(elem) < (l :+ newE).size then (l :+ newE)(f(elem)) == elem else false
    }.holds

    def test2[T](l: List[T], elem: T, newE: T, f: T => BigInt): Boolean = {
        require(0 <= f(elem) && f(elem) < l.size && l(f(elem)) == elem)

        if (0 <= f(elem) && f(elem) < (l :+ newE).size) {
            assert(f(elem) < l.size)
            (l :+ newE)(f(elem)) == elem
        } else false
    }.holds

    // only recursive ones are really needed in the end (I think)

    def forallRec[T](l: List[T], p: T => Boolean): Boolean = 
        decreases(l)
        l match {
            case Nil() => true
            case Cons(head, tl) => p(head) && forallRec(tl, p)
        }

    def forallAppendRec[T](l: List[T], elem: T, p: T => Boolean): Unit = {
        require(forallRec(l, p) && p(elem))
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
                forallAppendRec(t2, elem, p)
        }
    }.ensuring{_ => forallRec((l :+ elem), p)}

    def predOnSameLists[T](l1: List[T], l2: List[T], m1: List[T], m2: List[T], p: (T, List[T]) => Boolean): Unit = {
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
    }.ensuring(_ => forallRec(l2, p(_, m2)))

    /* def appendDoesNotChangeIndicesForAll(l: List[T], elem: T, f: T => BigInt): Unit = {
        require(l.forall(e => l(f(e)) == e))
    }.ensuring() */
}
