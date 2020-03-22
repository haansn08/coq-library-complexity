# Towards a Formal Proof of the Cook-Levin Theorem 

This contains Lennard Gäher's Bachelor's thesis at the [Programming Systems Lab](https://www.ps.uni-saarland.de/) of [Saarland University](https://www.uni-saarland.de/). 

Homepage of this project: https://www.ps.uni-saarland.de/~gaeher/bachelor.php

CoqDoc: https://uds-psl.github.io/ba-gaeher/website/toc.html

The project is based on the [library of undecidable problems](https://github.com/uds-psl/coq-library-undecidability). 
The main new files contributed as part of the thesis are: 

```
L/Complexity/PolyBounds.v
L/Complexity/Tactics.v
L/Complexity/MorePrelim.v
L/Complexity/FlatFinTypes.v

L/Complexity/Problems/UGraph.v
L/Complexity/Problems/FlatUGraph.v
L/Complexity/Problems/Clique.v
L/Complexity/Problems/FlatClique.v
L/Complexity/Problems/SharedSAT.v
L/Complexity/Problems/FSAT.v
L/Complexity/Problems/SAT.v
L/Complexity/Problems/kSAT.v
L/Complexity/Reductions/kSAT_to_Clique.v
L/Complexity/Reductions/kSAT_to_FlatClique.v
L/Complexity/Reductions/kSAT_to_SAT.v

L/Complexity/Problems/Cook/PR.v
L/Complexity/Problems/Cook/GenNP.v
L/Complexity/Problems/Cook/TPR.v
L/Complexity/Problems/Cook/FlatPR.v
L/Complexity/Problems/Cook/FlatTPR.v
L/Complexity/Problems/Cook/BinaryPR.v

L/Complexity/Reductions/Cook/PTPR_Preludes.v
L/Complexity/Reductions/Cook/SingleTMGenNP_to_TPR.v
L/Complexity/Reductions/Cook/TM_single.v
L/Complexity/Reductions/Cook/TPR_to_PR.v
L/Complexity/Reductions/Cook/FlatTPR_to_FlatPR.v
L/Complexity/Reductions/Cook/PR_homomorphisms.v
L/Complexity/Reductions/Cook/FlatPR_to_BinaryPR.v
L/Complexity/Reductions/Cook/TMGenNP_fixed_singleTapeTM_to_FlatFunSingleTMGenNP.v
L/Complexity/Reductions/Cook/FlatSingleTMGenNP_to_FlatTPR.v
L/Complexity/Reductions/FSAT_to_SAT.v
L/Complexity/Reductions/Cook/BinaryPR_to_FSAT.v
L/Complexity/Reductions/Cook/PR_to_BinaryPR.v
L/Complexity/Reductions/Cook/UniformHomomorphisms.v
```

## How to build

### Required packages

You need `Coq 8.8.1` or `8.8.2` built on OCAML `> 4.02.3` and the [Equations](https://mattam82.github.io/Coq-Equations/) package for Coq. If you're using opam 2 you can use the following commands to install the dependencies on a new switch:

```
opam switch create coq-library-undecidability 4.07.1+flambda
eval $(opam env)
opam install . --deps-only
```

### Build external libraries

The Undecidability libraries depends on several external libraries. Initialise and build them once as follows:

``` sh
git submodule init
git submodule update
make deps
```

### Building the undecidability library

- `make all` builds the library
- `make html` generates clickable coqdoc `.html` in the `website` subdirectory
- `make clean` removes all build files in `theories` and `.html` files in the `website` directory
- `make realclean` also removes all build files in the `external` directory. You have to run `make deps` again after this.

Use `make all -j[num #cores * 2]` to speed up compilation if you have enough RAM. For compilation with 8 threads or more, about 8-10GB RAM are needed. Minimum RAM needed is ~5GB.
This should take about 1-2 hours, depending on the speed of your system.

## Thesis
The source code of the thesis is located in `tex/thesis`. Build it with `make`. 
A PDF can be downloaded [here](https://www.ps.uni-saarland.de/~gaeher/files/thesis.pdf). 

## Acknowledgements

## License

The Coq files listed above are Copyright 2019-2020 Lennard Gäher. 
They are licensed under TODO.
TODO: work out compatibility of CeCILL of undec library with MIT license

The files in tex/ are Copyright 2019-2020 Lennard Gäher. The files in tex/thesis are based on [Yannick Forster's](https://www.ps.uni-saarland.de/~forster/) [thesis template](https://github.com/yforster/thesis-template). 



### Contributors of the underlying undecidability library 

- Yannick Forster
- Edith Heiter
- Dominik Kirst 
- Fabian Kunze
- Dominique Larchey-Wendling
- Gert Smolka
- Maximilian Wuttke

