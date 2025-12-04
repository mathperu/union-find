package union_find

object UnionFindSpecs {

    def UF_properties[T](uf: UnionFind[T]): Unit = {
    }.ensuring(_ => _)

    // UF_create ?

    def make_contains[T](uf: UnionFind[T], x: T): Unit = {
    }.ensuring(_ => uf.make(x).contains(x))

    def make_creates_root[T](uf: UnionFind[T], x: T): Unit = {
    }.ensuring(_ => uf.make(x).find(x).get == x)

    def make_unchanged_if_contains[T](uf: UnionFind[T], x: T): Unit = {
        require(uf.contains(x))
    }.ensuring(_ => uf.make(x) == uf)

    def find_spec[T](uf: UnionFind[T], x: T): Unit = {
        require(uf.contains(x))
    }.ensuring(y => 
        ??? // no path compression: trivial (ok) (maybe find some other specs ?)
        // with path compression : prove its equal to no compression version 
    )

    def eq_spec[T](uf: UnionFind[T], x: T, y: T): Unit = {
        require(uf.contains(x) && uf.contains(y))
    }.ensuring(_ => uf.eq(x, y) = uf.find(x) == uf.find(y))

}