package ourlistspecs

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

    def forallUpdate[T](l: List[T], addr: BigInt, elem: T, p: T => Boolean): Unit = {
        require(0 <= addr && addr < l.size)
        require(l.forall(p) && p(elem))
        
        if addr == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => forallUpdate(t, addr - 1, elem, p)
        }
    }.ensuring(_ => (l.updated(addr, elem)).forall(p))

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

    //TODO rename with actual name of property
    def mapAppend[T, U](l: List[T], elem: T, f: T => U): Unit = {
        l match {
            case Nil() => ()
            case Cons(h, t) => mapAppend(t, elem, f)
        }
    }.ensuring(_ => l.map(f) :+ f(elem) == (l :+ elem).map(f))

    def mapUpdate[T, U](l: List[T], addr: BigInt, elem: T, f: T => U): Unit = {
        require(0 <= addr && addr < l.size)
        require(f(l(addr)) == f(elem))
        
        if addr == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => mapUpdate(t, addr - 1, elem, f)
        }
    }.ensuring(_ => l.updated(addr, elem).map(f) == l.map(f))

    def mapAtIndex[T, U](l: List[T], index: BigInt, f: T => U): Unit = {
        require(0 <= index && index < l.size)
        
        if index == 0 then ()
        else l match {
            case Nil() => ()
            case Cons(h, t) => mapAtIndex(t, index - 1, f)
        }
    }.ensuring{_ => l.map(f)(index) == f(l(index))}

    def rangeAppend(start: BigInt, until: BigInt): Unit = {
        require(start <= until)
        decreases(until - start)
        if (until == start) then ()
        else rangeAppend(start + 1, until)
    }.ensuring(_ => List.range(start, until) :+ until == List.range(start, until + 1))

    def rangeAtIndexPlusStartIsIndexPlusStart(start: BigInt, until: BigInt, index: BigInt): Unit = {
        require(start <= index + start && start + index < until)

        if (index == 0) then ()
        else rangeAtIndexPlusStartIsIndexPlusStart(start + 1, until, index - 1)
    }.ensuring(_ => List.range(start, until)(index) == start + index)

    /* def weakenForAll[T](l: List[T], p: T => Boolean, q: T => Boolean): Unit = {
        require(l.forall(e => p(e) && q(e)))
    }.ensuring(_ => l.forall(p)) */

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
