/* 
    Copyright 2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/* 
  Kantor's Lemma as described in Brooksbank, Wilson, "The module isomorphism 
  problem reconsidered," 2015. Given isomorphic field extensions E and F of a 
  common field k, return one-way isomorphisms: from E to F and F to E.
*/
__Get_Field_Iso := function(E, F)
  f := DefiningPolynomial(E);
  R := PolynomialRing(F);
  factors := Factorization(R!f);
  assert exists(p){ g[1] : g in factors | Degree(g[1]) eq 1 };
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

/* 
  Input: a tensor and a generator for the centroid's residue field. 
  Output: a tensor and a homotopism from the given tensor to the returned tensor

  Since the centroid of t is a commutative local ring, we construct a tensor s 
  over the residue field of the centroid. To get representations correct, we do 
  this over Magma's standard GF(q), where q is the order of the residue field. 
*/
__Write_over_centroid := function(t, X) 
  v := Valence(t);
  C := Centroid(t); // already computed, therefore stored

  // We write t over a standard copy.
  K := ext< BaseRing(X) | MinimalPolynomial(X) >; 
  E := GF(#K);
  phi, phi_inv := __Get_Field_Iso(K, E);
  coeffs := Eltseq(E.1 @ phi_inv);
  Z := &+[coeffs[i]*X^(i-1) : i in [1..#coeffs]];
  assert Dimension(C) eq Dimension(sub< Generic(C) | Z>);
  assert MinimalPolynomial(Z) eq DefiningPolynomial(E);


  projs := [*Induce(C, a) : a in [v-1..0 by -1]*];

end function;


// =============================================================================
//                                  Intrinsics
// =============================================================================

intrinsic WriteTensorOverCentroid( t::TenSpcElt ) -> TenSpcElt, Homotopism
{Returns the fully nondegenerate indecomposbale tensor over a field isomorphic 
to the residue field of the centroid of t.}
  require IsFinite(BaseRing(t)) : "Base ring of tensor must be finite.";
  C := Centroid(t);
  J, S := WedderburnDecomposition(C);

  // In case already over its residue field, do nothing.
  if Dimension(S) eq 1 then
    dims := [Dimension(X) : X in Frame(t)];
    return t, Homotopism(t, t, [*IdentityMatrix(K, d) : d in dims*], 
        HomotopismCategory(Valence(t)));
  end if;

  // Run a few checks to make sure we can handle the data.
  require IsCommutative(S) : "Tensor is not fully nondegenerate.";
  cyclic_check, X := IsCyclic(S);
  require cyclic_check : "Centroid must be a commutative local ring.";
  require IsIrreducible(MinimalPolynomial(X)) : "Tensor must be indecomposable."
  
  // Now we write t over S.
  s, H := __Write_over_centroid(t, X);

  return s, H;
end intrinsic;