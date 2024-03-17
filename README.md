# GeoCoq
A formalization of geometry in Coq.

This library contains a formalization of geometry using the Coq proof assistant. It contains both proofs about the foundations of geometry and high-level proofs in the same style as in high-school.

Details and installation instructions can be found [here](http://geocoq.github.io/GeoCoq/).

Bug reports are to be submitted [here](https://github.com/GeoCoq/GeoCoq/issues).

It is possible to contact the authors of the GeoCoq library using our [mailing list](https://groups.google.com/forum/?hl=fr#!forum/geocoq).

GeoCoq is available as [releases packages](https://github.com/coq/opam/tree/master/released).

## Building and installation

- To get the required dependencies, you can use [opam](https://opam.ocaml.org).

  - To pin [pin](https://opam.ocaml.org/doc/Usage.html#opam-pin) the development packages.
    - `opam pin -n .`

  - GeoCoq relies on other released packages that need to be [added](https://opam.ocaml.org/doc/Usage.html#opam-repo).
    - `opam repo add coq-released https://coq.inria.fr/opam/released`

  - The required dependencies can now be installed:
    - `opam install ./coq-geocoq-coinc.opam --deps-only` to get the _GeoCoq Coinc_ dependencies;
    - `opam install ./coq-geocoq-axioms.opam --deps-only` to get the _GeoCoq Axioms_ dependencies;
    - `opam install ./coq-geocoq-elements.opam --deps-only` to get the _GeoCoq Elements_ dependencies;
    - `opam install ./coq-geocoq-main.opam --deps-only` to get the _GeoCoq Main_ dependencies;
    - `opam install ./coq-geocoq-algebraic.opam --deps-only` to get the _GeoCoq Algebraic_ dependencies;
    - `opam install ./coq-geocoq.opam --deps-only` to get the _GeoCoq_ dependencies.

- The general Makefile is in the top directory.
  - `make` : compilation of the Coq scripts (after using `./configure.sh`).

- You may also rely on `dune` to install just one part. Run:
  - `dune build coq-geocoq-coinc.install` to build only the _GeoCoq Coinc_ part (and its dependencies);
  - `dune build coq-geocoq-axioms.install` to build only the _GeoCoq Axioms_ part (and its dependencies);
  - `dune build coq-geocoq-elements.install` to build only the _GeoCoq Elements_ part (and its dependencies);
  - `dune build coq-geocoq-main.install` to build only the _GeoCoq Main_ part (and its dependencies);
  - `dune build coq-geocoq-algebraic.install` to build only the _GeoCoq Algebraic_ part (and its dependencies);
  - `dune build coq-geocoq.install` to build only the _GeoCoq_ part (and its dependencies).
