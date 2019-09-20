[![experimental](http://badges.github.io/stability-badges/dist/experimental.svg)](http://github.com/badges/stability-badges)
[![travis build status](https://travis-ci.org/morloc-project/morloc.svg?branch=master)](https://travis-ci.org/morloc-project/morloc)

# xi

This is an experimental type system that will be loaded into `morloc`
eventually. It is not intended to be used as a standalone program, but it does
offer a simple command line tool for parsing and typechecking programs. For
example:

```
$ xi "[1,2,3]"
([1, 2, 3] :: List Int)
```

The returned expression is the input expression with type annotations. Below is
a more complex example:

```
xi "map :: forall a b . (a -> b) -> [a] -> [b]; f :: Int -> Bool; map f [1,2,3]"
$ map :: forall a b . (a -> b) -> List a -> List b
$ f :: Int -> Bool
$ (
$   ((map :: forall a b . (a -> b) -> List a -> List b) (f :: Int -> Bool) :: List Int -> List Bool)
$   ([ 1 , 2 , 3 ] :: List Int)
$   :: List Bool
$ )
```

In the example above, notice that the `map` and `f` functions are not defined.
`Xi` makes an open-world assumption where it is sufficient that `map` and `f`
are functions that could exist. `Xi` checks whether they are used consistently.

For more information, see the [project page](https://morloc-project.github.io/xi/).
