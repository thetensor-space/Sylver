/* 
    Copyright 2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;

/* 
  Kantor's Lemma as described in Brooksbank, Wilson, "The module isomorphism 
  problem reconsidered," 2015. Given isomorphic field extensions E and F of a 
  common field k, return one-way isomorphisms: from E to F and F to E.
*/
__Get_Field_Iso := function(E, F)
  f := DefiningPolynomial(E);
  R := PolynomialRing(F);
  factors := Factorization(R!f);
  assert exists(p){g[1] : g in factors | Degree(g[1]) eq 1};
  p := LeadingCoefficient(p)^-1 * p;
  phi := hom< E -> F | R.1-p >;
  g := DefiningPolynomial(F);
  R := PolynomialRing(E);
  factors := Factorization(R!g);
  i := 1;
  repeat 
    q := LeadingCoefficient(factors[i][1])^-1 * factors[i][1];
    phi_inv := hom< F -> E | R.1-q >;
    i +:= 1;
  until (E.1 @ phi) @ phi_inv eq E.1 and (F.1 @ phi_inv) @ phi eq F.1;
  return phi, phi_inv;
end function;


// Given a matrix Z, constructs a sequence of subspaces that are Z-invariant. 
__Get_Indecomp_Submods := function(Z)
  K := BaseRing(Z);
  d := Nrows(Z);
  e := Degree(MinimalPolynomial(Z));
  V := VectorSpace(K, d);

  Spin := function(S, M)
    return Append(S, S[#S] * M);
  end function;

  Inds := [PowerRSpace(K, d, e)| ];
  triv := sub< V | >;
  while &+(Inds cat [triv]) ne V do
    Q, pi := V/ &+(Inds cat [triv]);
    S := [Q.1 @@ pi];
    while #S lt e do
      S := Spin(S, Z);
    end while;
    Append(~Inds, VectorSpaceWithBasis(S));
  end while;

  return Inds;
end function;


// Given a sequence of submodules of U, return an isomorphism from U to V
__Vector_Space_Iso := function(I)
  K := BaseRing(I[1]);
  d1 := Degree(I[1]);
  d2 := Dimension(I[1]);
  e := #I;
  E := GF(#K^d2);
  U := VectorSpace(K, d1);
  V := VectorSpace(E, e);

  // We construct the basic functions between the vector spaces
  M := Matrix(&cat[Basis(S) : S in I]);
  U_to_V := function(x)
    u := Eltseq(x * M^-1);
    return V![E!(u[(i-1)*d2+1..i*d2]) : i in [1..e]];
  end function;
  V_to_U := function(y)
    v := Eltseq(y);
    u := &cat[Eltseq(z) : z in v];
    return (U!u) * M;
  end function;

  // Construct isomorphism from U to V
  phi := map< U -> V | x :-> U_to_V(x), y :-> V_to_U(y) >;
  
  // Some checks
  assert (U!0) @ phi eq V!0;
  assert forall{b : b in Basis(U) | (b @ phi) @@ phi eq b};
  assert forall{b : b in Basis(V) | (b @@ phi) @ phi eq b};

  return phi;
end function;


/* 
  Input: a tensor and a generator for the centroid's residue field. 
  Output: a tensor and a homotopism from the given tensor to the returned tensor

  Since the centroid of t is a commutative local ring, we construct a tensor s 
  over the residue field of the centroid. To get representations correct, we do 
  this over Magma's standard GF(q), where q is the order of the residue field. 
*/
__Write_over_centroid := function(t, X) 
  v := Valence(t);
  F := BaseRing(t);
  C := Centroid(t); // already computed and saved

  // We write t over a standard copy.
  K := ext< F | MinimalPolynomial(X) >; 
  E := GF(#K);
  phi, phi_inv := __Get_Field_Iso(K, E);
  coeffs := Eltseq(E.1 @ phi_inv);
  Z := &+[coeffs[i]*X^(i-1) : i in [1..#coeffs]];
  assert Dimension(C) eq Dimension(sub< Generic(C) | Z>);
  assert MinimalPolynomial(Z) eq DefiningPolynomial(E);

  // Break apart the blocks of Z. 
  projs := [*Induce(C, a) : a in [v-1..0 by -1]*];
  blocks := [*Z @ pi : pi in projs*];

  // Construct the indecomposable submodules for each block. 
  Subs := [*__Get_Indecomp_Submods(B) : B in blocks*];

  // Get the isomorphisms from original vector spaces to new vector spaces.
  Isos := [*__Vector_Space_Iso(I) : I in Subs*];

  // Build an anti-cohomotopism to construct our new tensor
  Fused := RepeatPartition(TensorCategory(t));
  Antichmtp := TensorCategory([-1 : i in [1..v-1]] cat [1], Fused);
  Isos_achmtp := Isos;
  for i in [1..v-1] do
    Isos_achmtp[i] := Isos[i]^-1;
  end for;
  H_achmtp := Homotopism(Isos_achmtp, Antichmtp);

  // Put it all together
  s := t @ H_achmtp;
  H := Homotopism(t, s, Isos, HomotopismCategory(v) : Check := __SANITY_CHECK);
  return s, H;
end function;



// =============================================================================
//                                  Intrinsics
// =============================================================================

intrinsic TensorOverCentroid( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the fully nondegenerate indecomposbale tensor over a field isomorphic 
to the residue field of the centroid of t.}
  require IsFinite(BaseRing(t)) : "Base ring of tensor must be finite.";
  C := Centroid(t);
  J, S := WedderburnDecomposition(C);

  // In case already over its residue field, do nothing.
  if Dimension(S) eq 1 then
    K := BaseRing(t);
    dims := [Dimension(X) : X in Frame(t)];
    return t, Homotopism(t, t, [*IdentityMatrix(K, d) : d in dims*], 
        HomotopismCategory(Valence(t)));
  end if;

  // Run a few checks to make sure we can handle the data.
  require IsCommutative(S) : "Tensor is not fully nondegenerate.";
  cyclic_check, X := IsCyclic(S);
  require cyclic_check : "Centroid must be a commutative local ring.";
  require IsIrreducible(MinimalPolynomial(X)) : 
      "Tensor must be indecomposable.";
  
  // Now we write t over S.
  s, H := __Write_over_centroid(t, X);

  return s, H;
end intrinsic;
