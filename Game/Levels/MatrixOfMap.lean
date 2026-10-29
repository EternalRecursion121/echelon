import Game.Levels.MatrixOfMap.L14_RankCompLeft

World "MatrixOfMap"
Title "Matrix of a Map"

Introduction "
Hefferon Three.III. A linear map is determined by what it does to a basis, and the images of
the basis vectors, written in coordinates, are the columns of a matrix. In this world you
compute such matrices, and prove that composing maps corresponds to multiplying matrices.

The point of $\\mathrm{Rep}_{B,D}(h)$ is Hefferon's Theorem Three.III.1.9: multiplying it by
the coordinates of $\\vec v$ gives the coordinates of $h(\\vec v)$,
$$\\mathrm{Rep}_{B,D}(h)\\cdot\\mathrm{Rep}_B(\\vec v) = \\mathrm{Rep}_D(h(\\vec v)).$$
So once bases are chosen, every linear map *is* multiplication by a matrix.
"
