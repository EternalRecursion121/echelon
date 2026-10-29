import Game.Levels.MatrixOfMap.L14_RankCompLeft

World "MatrixOfMap"
Title "Matrix of a Map"

Introduction "
Hefferon Three.III. A linear map is determined by what it does to a basis, and the images of
the basis vectors, written in coordinates, are the columns of a matrix. In this world you
compute such matrices (levels 1–6), prove that composing maps corresponds to multiplying
matrices (levels 7–9), see that every map of $\\mathbb R^n$ is a matrix (levels 10–11), and
finish with the rank of a product: it can drop, and is at most the rank of either factor
(levels 12–14).

The point of $\\mathrm{Rep}_{B,D}(h)$ is Hefferon's Theorem Three.III.1.9: multiplying it by
the coordinates of $\\vec v$ gives the coordinates of $h(\\vec v)$,
$$\\mathrm{Rep}_{B,D}(h)\\cdot\\mathrm{Rep}_B(\\vec v) = \\mathrm{Rep}_D(h(\\vec v)).$$
So once bases are chosen, every linear map *is* multiplication by a matrix.
"
