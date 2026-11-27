# Simultaneous square rank of a binary pencil

Take the real binary quadratics Q = x² − y² and R = 2xy. Their pencil has symmetric matrices with rows (a,b) and (b,−a). Its determinant is −a²−b². The coefficient matrices are independent, and every nonzero pencil element has rank two.

Suppose two squares of linear forms suffice. Their span contains the two-dimensional reader plane and hence equals it. A nonzero square gives a rank-one matrix in this plane, which the determinant calculation excludes. The source proves the lower bound directly by evaluating both outputs at (1,0), (0,1) and (1,1). The output mixing matrix must be invertible. Taking traces then forces both squared input forms to vanish. Zero or one square can be padded to two with zero coefficients. The three squares x², y², (x+y)² attain the minimum. Two unrestricted products suffice, and a single scalar producer with constant linear readouts cannot yield two independent outputs.

### Synthesis for every real plane of binary quadratics

Identify a square with its coefficients (u²,uv,v²), where the middle coordinate of a form is half its mixed coefficient. Compute a normal (A,B,C) to the reader plane by ordinary elimination. The allowable projective square directions satisfy A u² + B u v + C v² = 0. If B²−4AC is positive there are two distinct real projective roots. Their Veronese images are independent and span the plane. The minimum is two. At zero discriminant there is only one direction. At negative discriminant there are none. In either case the minimum is three, since the full three-dimensional space has the square basis given above. A projective root can lie at infinity when A or C vanishes. This classification uses exact real arithmetic and an unrestricted coefficient field for the reader weights.

For example, span{x²,y²} is a secant, span{x²,xy} is tangent, and the displayed pencil has no real square direction. The discriminant classification is a written proof. The specific pencil, its dimension, rank, two-square obstruction and explicit identities are formalized in `BinaryPencil.lean`. Complex coefficients, arbitrary bilinear gates and limiting decompositions have different feasible sets. For simultaneous decomposition in wider settings see [Carlini, simultaneous sums of powers](https://arxiv.org/abs/math/0202050) if consulting the literature; the plane argument above is elementary and self-contained.

Run `lake build` and `bash scripts/audit.sh`.
