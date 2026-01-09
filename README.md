# Partial Implementation of Union Find in Stainless

Mathilde Peruzzo, Rassene M'sadaa, Julian Marmier

## Verifying the project using Stainless

```bash
stainless src/*
```

**Note**: `unionMergedTheSets` has not been fully proved and will timeout in Stainless. For a partial proof, please see branch `mergeset`.

## Using the library

### Writing code

See [the example file](examples/simple.scala) for a simple example using a disjoint set of integers. The final `union` operation corresponds to the same one was shown during our presentation:

```
      0    2                      0
     /      \    union(3, 4)     / \
    1        4   ──────────►   1    2
   /                          /      \
  3                          3        4
```

```scala
val uf = emptyUF[BigInt]()

val (uf1, _) = uf.make(0)

// needed to prove that the domain is correctly initialized
MoreListSpecs.snocNil(0)

val (uf2, _) = uf1.make(1)
val (uf3, _) = uf2.make(2)
val (uf4, _) = uf3.make(3)
val (uf5, _) = uf4.make(4)

val (ufSep1, _) = uf5.union(0, 1)
val (ufSep2, _) = ufSep1.union(1, 3)
val (ufSep3, _) = ufSep2.union(2, 4)
val (ufFinal, _) = ufSep3.union(3, 4)
```

### Running the code

Simply invoke src/\* alongside the file containing the written code, specifying `--functions` to speed up the verification process:

```bash
stainless src/* examples/simple.scala --functions=exampleUsage
```
