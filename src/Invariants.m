/* 
    Copyright 2016--2019 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
  This file contains invariants for tensors. They come in two flavors: linear
  algebra and polynomial-based invariants. Most of the invariants have been 
  optimized for bimaps (3-tensors).
*/


import "Util.m" : __GetForms, __GetSlice;
import "GlobalVars.m" : __SANITY_CHECK;

// A function to remove superfluous blocks for fused coordinates. 
/*
  Given a basis as a tuple of blocks, partition as a set of subsets of {0..v}, 
  and coords as a sequence aligned with basis.
*/
__ReduceByFuse := function(basis, partition, coords)
  K := BaseRing(basis[1][1]);
  toFuse := [S meet Set(coords) : S in partition | #(S meet Set(coords)) gt 1];
  newBasis := [[*x : x in b*] : b in basis];
  newCoords := {s : s in S meet Set(coords), S in partition | #S eq 1};

  for S in toFuse do
    T := S diff {Max(S)};
    Include(~newCoords, Max(S));
    for t in T do
      i := Index(coords, t);
      for j in [1..#newBasis] do
        newBasis[j][i] := IdentityMatrix(K, 0);
      end for;
    end for;
  end for;

  return [<x : x in b> : b in newBasis], newCoords;
end function;


/*
  Given: K (Fld), dims ([RngIntElt]), repeats ({SetEnum}), A ({RngIntElt}).
  Returns: A matrix with I and -I strategically placed so that the corresponding
    linear system will equate the operators supported on repeats, relative to A.

    This matrix should be vertically joined to ensure that coordinates that are
  fused are equal. 
*/  
__FusionBlock := function(K, dims, repeats, A)
  // Setup.
  v := #dims;
  S := &+[dims[v-a]^2 : a in A];
  R := {X meet A : X in repeats | #(X meet A) gt 1};
  n := &+([(#r-1)*dims[v - Minimum(r)]^2 : r in R] cat [0]);
  
  M := ZeroMatrix(K, n, S);
  // If no repeats relative to A, we are done. 
  // Returns a (0 x S)-matrix to prevent issues with VerticalJoin.
  if n eq 0 then return M; end if;
  
  // Run through the repeats.
  row := 1;
  for r in R do
    // We fix a for this particular r, and compare everything to this.
    a := Minimum(r);
    B := r diff {a};
    if a ne 0 then
      I := IdentityMatrix(K, dims[v-a]^2);
    else
      temp := Matrix(Integers(), dims[v], dims[v], [1..dims[v]^2]);
      temp := Eltseq(Transpose(temp));
      I := PermutationMatrix(K, temp);
    end if;
    rcol := S - &+[dims[v-a+i]^2 : i in [0..a] | a-i in A] + 1;
    // Run though the set r - a.
    while #B gt 0 do
      b := Minimum(B);
      B diff:= {b};
      lcol := S - &+[dims[v-b+i]^2 : i in [0..b] | b-i in A] + 1;

      // Place the blocks.      
      InsertBlock(~M, IdentityMatrix(K, dims[v-a]^2), row, lcol);
      InsertBlock(~M, -I, row, rcol);

      row +:= dims[v-a]^2;
    end while;
  end for;

  return M;
end function;

/* 
  Given: t (TenSpcElt), A ({RngIntElt} a subset of [vav])
  Return: [Tup] (Tup are contained in Prod_a End(U_a))

  These are the operators that satisfy 
      \bigcap_{b \in A - \{a\}} (x_a - x_b).

  + Note that if |A| = 2, then this is actually a nucleus computation. 

  + We leave it to the function calling this to organize and find appropriate 
    representations.

  Complexity: If D is the product of dimensions in dims, and S is the sum of 
    squares of the dimensions supported by A, then this algorithm constructs a 
    basis for the kernel of a K-matrix with (|A|-1)*D rows and S columns.
*/
__A_Centroid_mat := function(seq, dims, A : repeats := {})
  // Initial setup.
  a := Minimum(A);
  B := A diff {a};
  d := &*(dims);
  K := Parent(seq[1]);
  v := #dims;
  d_a := dims[v-a];
  M := ZeroMatrix(K, #B*d, &+[dims[v-x]^2 : x in A]);
  I := IdentityMatrix(K, d_a);
  r_anchor := Ncols(M) - d_a^2 + 1;
  
  vprintf TensorSpace, 1 : "Constructing a %o by %o matrix over %o.\n", 
    Ncols(M), Nrows(M), K;
  
  // Construct the appropriate matrix. 
  // We place the a block on the right-most side of M.
  row := 1;
  col := 1;
  while #B gt 0 do
    b := Maximum(B);
    B := B diff {b};
    d_b := dims[v-b];

    Mats := __GetForms(seq, dims, b, a : op := true);
    LeftBlocks := [Matrix(K, [Eltseq(Mats[k][i]) : k in [1..#Mats]]) : 
      i in [1..d_a]];
    Mats := [Transpose(X) : X in Mats];
    RightBlock := -Matrix(K, &cat[[Eltseq(Mats[k][j]) : k in [1..#Mats]] : 
      j in [1..d_b]]);
    delete Mats;

    // Building the matrix strip for the equation x_a = x_b.
    // The blocks corresponding to the x_a part.
    InsertBlock(~M, KroneckerProduct(I, RightBlock), row, r_anchor);
    delete RightBlock;

    // The blocks corresponding to the x_b part. 
    for i in [1..#LeftBlocks] do
      InsertBlock(~M, KroneckerProduct(IdentityMatrix(K, d_b), LeftBlocks[i]), 
        row, col);
      row +:= d_b*Nrows(LeftBlocks[i]);
    end for;
    delete LeftBlocks;
    
    col +:= d_b^2;
  end while;

  // Check repeats.
  if #repeats ne 0 then
    vprint TensorSpace, 1 : "Adding in possible fusion data.";
    R := __FusionBlock(K, dims, repeats, A);
    M := VerticalJoin(R, M);
  end if;

  return M;
end function;

__A_Centroid := function(seq, dims, A : repeats := {})
  // Initial setup.
  a := Minimum(A);
  B := A diff {a};
  d := &*(dims);
  K := Parent(seq[1]);
  v := #dims;
  d_a := dims[v-a];
  M := ZeroMatrix(K, #B*d, &+[dims[v-x]^2 : x in A]);
  I := IdentityMatrix(K, d_a);
  r_anchor := Ncols(M) - d_a^2 + 1;
  
  vprintf TensorSpace, 1 : "Constructing a %o by %o matrix over %o.\n", 
    Ncols(M), Nrows(M), K;
  
  // Construct the appropriate matrix. 
  // We place the a block on the right-most side of M.
  row := 1;
  col := 1;
  while #B gt 0 do
    b := Maximum(B);
    B := B diff {b};
    d_b := dims[v-b];

    Mats := __GetForms(seq, dims, b, a : op := true);
    LeftBlocks := [Matrix(K, [Eltseq(Mats[k][i]) : k in [1..#Mats]]) : 
      i in [1..d_a]];
    Mats := [Transpose(X) : X in Mats];
    RightBlock := -Matrix(K, &cat[[Eltseq(Mats[k][j]) : k in [1..#Mats]] : 
      j in [1..d_b]]);
    delete Mats;

    // Building the matrix strip for the equation x_a = x_b.
    // The blocks corresponding to the x_a part.
    InsertBlock(~M, KroneckerProduct(I, RightBlock), row, r_anchor);
    delete RightBlock;

    // The blocks corresponding to the x_b part. 
    for i in [1..#LeftBlocks] do
      InsertBlock(~M, KroneckerProduct(IdentityMatrix(K, d_b), LeftBlocks[i]), 
        row, col);
      row +:= d_b*Nrows(LeftBlocks[i]);
    end for;
    delete LeftBlocks;
    
    col +:= d_b^2;
  end while;

  // Check repeats.
  if #repeats ne 0 then
    vprint TensorSpace, 1 : "Adding in possible fusion data.";
    R := __FusionBlock(K, dims, repeats, A);
    M := VerticalJoin(R, M);
  end if;

  // Solve the linear equations.
  vprintf TensorSpace, 1 : "Computing the nullspace of a %o by %o matrix.\n", Ncols(M),
    Nrows(M);
  N := NullspaceOfTranspose(M);
  delete M;

  // Interpret the nullspace as matrices.
  basis := [];
  for b in Basis(N) do
    T := <>;
    vec := Eltseq(b);
    for a in Reverse(Sort([a : a in A])) do
      MA := MatrixAlgebra(K, dims[v-a]);
      Append(~T, MA!vec[1..dims[v-a]^2]);
      vec := vec[dims[v-a]^2+1..#vec];
    end for;
    Append(~basis, T);
  end for;

  // We want to return everything to End(U_i) (in particular, no op).
  // If 0 is in A, then we need to transpose the matrices.
  if 0 in A then
    for i in [1..#basis] do
      basis[i][#basis[i]] := Transpose(basis[i][#basis[i]]);
    end for;
  end if;

  return basis;
end function;

/*
  This is essentially Transpose(Foliation(t, a)), but it splits up the matrix 
  into k equal pieces.
*/
__Coordinate_Spread := function(seq, dims, a, k)
  v := #dims;
  d_a := dims[v-a];
  dims_a := dims;
  dims_a[v-a] := 1;
  CP := CartesianProduct(< [1..d] : d in dims_a >);
  rows := [];
  for c in CP do
    grid := [{x} : x in c];
    grid[v-a] := {1..d_a};
    Append(~rows, __GetSlice(seq, dims, grid));
  end for;
  d := &*(dims_a) div k;
  if a eq 0 then 
    ep := -1; 
  else 
    ep := 1;
  end if;
  Mats := [ep*Matrix(rows[(i-1)*d+1..i*d]) : i in [1..k]];
  return Mats;
end function;


/* 
  Given: seq : [FldElt], dims : [RngIntElt], A : {RngIntElt}, 
      repeats : {SetEnum}, k : RngIntElt.
  Return: [Tup].

  If B is a k-subset of A, 
      p_B(X) = \sum_{a \in A} x_a)            if 0 not in B,
      p_B(X) = \sum_{a \in A-0} x_a - x_0)    if 0 in B.
  These operators satisfy the ideal 
      (p_B(X) : B subset A, |B| = k).

  + We leave it to the function calling this to organize and find appropriate 
    representations.

  Complexity: If D is the product of dimensions in dims, and S is the sum of 
    squares of the dimensions supported by A, then this algorithm constructs a 
    basis for the kernel of a K-matrix with (#A choose k)*D rows and S columns.
*/

__A_Derivations := function(seq, dims, A, repeats, k)
  // Initial setup.
  d := &*(dims);
  K := Parent(seq[1]);
  v := #dims;
  s := &+[dims[v-x]^2 : x in A];
  k_Subs := Subsets(A, k);
  M := ZeroMatrix(K, #k_Subs*d, s);

  // Start the bad boy up.
  vprintf TensorSpace, 1 : "Construting a %o by %o matrix over %o.\n", Ncols(M), 
    Nrows(M), K;

  // Construct the appropriate matrix.
  // We work from right to left.
  row := 1;
  for B in k_Subs do
    col := s+1;
    depth := d;
    A_comp := {0..v-1} diff A;
    
    // Run through all a in A and only do things if a in B.
    for a in Sort([x : x in A]) do
      d_a := dims[v-a];
      col -:= d_a^2;
      C := {c : c in A_comp | c lt a};
      A_comp diff:= C;
      depth div:= d_a * &*([dims[v-c] : c in C] cat [1]);
      B_row := row;

      if a in B then
        // A chopped up foliation.
        Mats := __Coordinate_Spread(seq, dims, a, depth);

        // Add the matrices to our big matrix.
        I := IdentityMatrix(K, d_a);
        r := d_a * Nrows(Mats[1]);
        for X in Mats do
          InsertBlock(~M, KroneckerProduct(I, X), B_row, col);
          B_row +:= r;
        end for;
      end if;

    end for;

    // Move down a stripe.
    row +:= d;

  end for;

  // Get the repeats block.
  vprint TensorSpace, 1 : "Adding in possible fusion data.";
  M := VerticalJoin(__FusionBlock(K, dims, repeats, A), M);
  
  // Solve the linear system.
  vprintf TensorSpace, 1 : "Computing the nullspace of a %o by %o matrix.\n", 
    Ncols(M), Nrows(M);
  N := NullspaceOfTranspose(M);
  B := Basis(N);
  if #B eq 0 then
    B := [N!0];
  end if;

  // Interpret the nullspace as matrices
  basis := [];
  for b in B do
    T := <>;
    vec := Eltseq(b);
    for a in Reverse(Sort([a : a in A])) do
      MA := MatrixAlgebra(K, dims[v-a]);
      Append(~T, MA!vec[1..dims[v-a]^2]);
      vec := vec[dims[v-a]^2+1..#vec];
    end for;
    Append(~basis, T);
  end for;

  // We want to return everything to End(U_i) (in particular, no op).
  // If 0 is in A, then we need to transpose the matrices.
  if 0 in A then
    for i in [1..#basis] do
      basis[i][#basis[i]] := Transpose(basis[i][#basis[i]]);
    end for;
  end if;

  return basis;
end function;


// A function to reduce the number of generators of a group or algebra.
__GetSmallerRandomGenerators := function( X ) 
  if not IsFinite(BaseRing(X)) then
    return X;
  end if;
  gens := Generators(X);
  if #gens le 3 then
    return X;
  end if;
  small := {};
  repeat
    Include(~small,Random(X));
    S := sub< X | small>;
  until Dimension(X) eq Dimension(S);
  return S;
end function;

// Given a tensor t, a set of coords A, a boolean F, a function ALG, a seq of 
// tuples B, and a string obj return algebra derived from the tensor. 
__MakeAlgebra := function(t, A, F, ALG, B);
  coords := Reverse(Sort([a : a in A]));

  // if we should reduce by fuse, do it.
  if F then
    B, A_rep := __ReduceByFuse(B, t`Cat`Repeats, coords);
  else
    A_rep := A;

    // if this is a nuke, then transpose might be required.
    if (#A eq 2) and (0 notin A) then
      for i in [1..#B] do
        B[i][2] := Transpose(B[i][2]);
      end for;
    end if;

  end if;

  // put it all together and leave a trail of breadcrumbs. 
  basis := [DiagonalJoin(T) : T in B];
  MA := ALG(BaseRing(t), Nrows(basis[1]));
  Operators := sub< MA | basis >;
  Operators := __GetSmallerRandomGenerators(Operators);
  DerivedFrom(~Operators, t, A, A_rep : Fused := F);

  return Operators, B;
end function;

// Given a tensor t, a set of coords A, a boolean F, a seq of 
// tuples B, and a string obj return space approximiating 
// the algebra derived from the tensor. 
__ApproximateAlgebra := function(t, A, F, B);
  coords := Reverse(Sort([a : a in A]));

  // if we should reduce by fuse, do it.
  if F then
    B, A_rep := __ReduceByFuse(B, t`Cat`Repeats, coords);
  else
    A_rep := A;

    // if this is a nuke, then transpose might be required.
    if (#A eq 2) and (0 notin A) then
      for i in [1..#B] do
        B[i][2] := Transpose(B[i][2]);
      end for;
    end if;

  end if;

  // put it all together and leave a trail of breadcrumbs. 
  basis := [DiagonalJoin(T) : T in B];
  MA := KMatrixSpace(BaseRing(t), Nrows(basis[1]), Nrows(basis[1]));
  Operators := sub< MA | basis >;
  //Operators := __GetSmallerRandomGenerators(Operators);
  //DerivedFrom(~Operators, t, A, A_rep : Fused := F);

  return Operators, B;
end function;

/* 
  A function called multiple times in the sanity check.
  Given an algebra Z, and a set B, verify the correct polynomial.
*/
__BSanity := function(Z, B : nuke := false)
  // Initial setup.
  t := Z`DerivedFrom`Tensor;
  v := Valence(t);
  CP := CartesianProduct(<Basis(X) : X in Domain(t)>);

  MultByMat := function(x, M, a)
    y := x;
    y[Valence(t) - a] := y[Valence(t) - a]*Matrix(M);
    return y;
  end function;

  if #B eq 2 then
    // In this case we need to verify x_a - x_b. 
    // If 0 in B, then no need to transpose. Otherwise, we need to transpose.
    a := Maximum(B);
    b := Minimum(B);
    if 0 in B then
      return forall{z : z in Generators(Z) | forall{x : x in CP | 
        MultByMat(x, z @ Induce(Z, a), a) @ t eq (x @ t)*(z @ Induce(Z, 0))
        }};
    else
      if nuke then
        MyTr := func< x | Transpose(x) >;
      else
        MyTr := func< x | x >;
      end if;
      return forall{z : z in Generators(Z) | forall{x : x in CP | 
        MultByMat(x, z @ Induce(Z, a), a) @ t eq 
        MultByMat(x, MyTr(Matrix(z @ Induce(Z, b))), b) @ t
        }};
    end if;
  else
    // In this case, we need to verify the derivation polynomial.
    // If 0 in B, then we need to verify Sum_{b in B - 0} x_b - x_0. Otherwise,
    // we need to verify Sum_{b in B} x_b. 
    if 0 in B then
      return forall{z : z in Generators(Z) | forall{x : x in CP | 
        &+([MultByMat(x, z @ Induce(Z, a), a) @ t : a in B diff {0}] cat 
          [Codomain(t)!0]) eq 
        (x @ t)*(z @ Induce(Z, 0))
        }};
    else
      return forall{z : z in Generators(Z) | forall{x : x in CP | 
        &+[MultByMat(x, z @ Induce(Z, a), a) @ t : a in B] eq Codomain(t)!0
        }};
    end if;
  end if;
end function;


__OperatorSanityCheck := function(Z, k : nuke := false)
  A := Z`DerivedFrom`Coords;
  return forall{B : B in Subsets(A, k) | __BSanity(Z, B : nuke := nuke)};
end function;


// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                   Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ==============================================================================
//                             Linear algebra methods
// ==============================================================================
intrinsic Centroid( t::TenSpcElt ) -> AlgMat
{Returns the centroid of the tensor t.}
  return Centroid(t, {0..Valence(t)-1});
end intrinsic;

intrinsic Centroid( t::TenSpcElt, A::{RngIntElt} ) -> AlgMat
{Returns the A-centroid of the tensor t.}
  // Check that A makes sense.
  require A subset {0..Valence(t)-1} : "Unknown tensor coordinates.";
  require #A ge 2 : "Must be at least two coordinates.";
  if t`Cat`Contra then
    require 0 notin A : "Integers must be positive for cotensors.";
  end if;
  require forall{X : X in Frame(t) | Dimension(X) gt 0} : 
      "Modules in frame must be positive dimensional.";
  
  // |A| = 2 case.
  if #A eq 2 then
    return Nucleus(t, Maximum(A), Minimum(A));
  end if;

  // Check if the centroid has been computed before.
  ind := Index(t`Derivations[1], <A, 2>);
  // If it has been, return it as an algebra. 
  if Type(t`Derivations[2][ind]) ne RngIntElt then
    C := __MakeAlgebra(t, A, true, MatrixAlgebra, t`Derivations[2][ind]);
    return C;
  end if;
   
  // Now it hasn't been computed before, and we need to compute something.
  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], A : 
    repeats := t`Cat`Repeats);

  // Construct algebra and reduce to minimal representation
  C, basis := __MakeAlgebra(t, A, true, MatrixAlgebra, basis);

  // Sanity check
  if __SANITY_CHECK then
    printf "Sanity check (Centroid)\n"; 
    assert __OperatorSanityCheck(C, 2);
  end if;

  // Checkpoint!
  t`Derivations[2][ind] := basis;
  return C;
end intrinsic;

intrinsic CentroidSVD( t::TenSpcElt, A::{RngIntElt} ) -> .
{Returns the A-centroid of a real or complex tensor t by SVD methods.}
  // Check that A makes sense.
  require Type(BaseRing(t)) eq FldRe : "Must be a real field for SVD.";
  // BUG???? should it be Valence(t) or Valence(t)-1?
  require A subset {0..Valence(t)} : "Unknown tensor coordinates.";
  require #A ge 2 : "Must be at least two coordinates.";
  if t`Cat`Contra then
    require 0 notin A : "Integers must be positive for cotensors.";
  end if;
  require forall{X : X in Frame(t) | Dimension(X) gt 0} : 
      "Modules in frame must be positive dimensional.";
  
  // // |A| = 2 case.
  // if #A eq 2 then
  //   return NucleusSVD(t, Maximum(A), Minimum(A));
  // end if;

  // // Check if the centroid has been computed before.
  // ind := Index(t`Derivations[1], <A, 2>);
  // // If it has been, return it as an algebra. 
  // if Type(t`Derivations[2][ind]) ne RngIntElt then
  //   C := __MakeAlgebra(t, A, true, MatrixAlgebra, t`Derivations[2][ind]);
  //   return C;
  // end if;
   
  // Now it hasn't been computed before, and we need to compute something.
  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  mat := __A_Centroid_mat(Eltseq(t), [Dimension(X) : X in Frame(t)], A : 
    repeats := t`Cat`Repeats);
  S, U, V := SingularValueDecomposition(Transpose(mat));
  // Detect the singular values clustered around 0.
  sings := [S[i][i] : i in [1..Minimum(Nrows(S),Ncols(S))]];
"sings:", sings;
  // Scan last to first looking at the slopes of the normalized 
  // SVD plot adjacent points.  The first inflection point (slope below -1)
  // is where we stop.
  slope := 0;
  start := #sings;
  while (start gt 1) 
    and ((sings[start] eq 0) or (sings[start-1]/sings[start] lt 5 )) do
    start := start - 1;
  end while;
  // while (start > 1) and (slope gt -1 ) do
  //   slope := (sings[start-1]-sings[start])/(#sings*sings[1]);
  //   start := start - 1;
  // end while;

  // Gather the singular vectors incident on these.
  gens := [ U[i] : i in [start..Nrows(U)]];


  // Construct algebra and reduce to minimal representation
  //C := __ApproximateAlgebra(t, A, true, gens);

  // // Sanity check
  // if __SANITY_CHECK then
  //   printf "Sanity check (Centroid)\n"; 
  //   assert __OperatorSanityCheck(C, 2);
  // end if;

  // // Checkpoint!
  // t`Derivations[2][ind] := basis;
  return gens;//C;
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt ) -> AlgMatLie
{Returns the derivation algebra of the tensor t.}
  return DerivationAlgebra(t, {0..Valence(t)-1}, Valence(t));
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt, A::{RngIntElt} ) -> AlgMatLie
{Returns the A-derivation algebra of the tensor t.}
  return DerivationAlgebra(t, A, #A);
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt, A::{RngIntElt}, k::RngIntElt ) -> 
  AlgMatLie
{Returns the (A, k)-derivation algebra of the tensor t.}
  // Make sure A makes sense.
  require A subset {0..Valence(t)-1} : "Unknown coordinates.";
  require #A gt 0 : "Set must contain at least two coordinates.";
  if t`Cat`Contra then
    require 0 notin A : "Integers must be positive for cotensors.";
  end if;
  require k ge 1 : "Integer must be at least 2.";
  require k le #A : "Integer cannot be larger than set size.";

  // Out-source the k=2 case
  if k eq 2 then
    _ := Centroid(t, A);
  end if;

  // Make sure we can obtain the structure constants. 
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  // Check if the derivations have been computed before.
  ind := Index(t`Derivations[1], <A, k>);
  fuse := (k gt 2) select true else false;
  if Type(t`Derivations[2][ind]) ne RngIntElt then
    D := __MakeAlgebra(t, A, fuse, MatrixLieAlgebra, t`Derivations[2][ind]);
    return D;
  end if; 

  // Get the derivations.
  basis := __A_Derivations(Eltseq(t), [Dimension(X) : X in Frame(t)], A,
    t`Cat`Repeats, k);

  // Construct the algebra and reduce to minimal representation.
  D, basis := __MakeAlgebra(t, A, true, MatrixLieAlgebra, basis);

  // Sanity check
  if __SANITY_CHECK then
    printf "Sanity check (DerivationAlgebra)\n";
    assert __OperatorSanityCheck(D, k);
  end if;

  // Save it
  t`Derivations[2][ind] := basis;
  return D;
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, A::{RngIntElt} ) -> AlgMat
{Returns the A-nucleus of the tensor t, for |A| = 2.}
  require #A eq 2 : "Set must contain exactly two coordinates.";
  return Nucleus(t, Maximum(A), Minimum(A));
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, a::RngIntElt, b::RngIntElt ) -> AlgMat
{Returns the ab-nucleus of the tensor t.}
  // Make sure {a,b} make sense.
  require a ne b : "Integers must be distinct.";
  v := Valence(t);
  require {a,b} subset {0..v-1} : \
    "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {a,b} : "Integers must be positive for cotensors.";
  end if;

  // Check if it has been computed before.
  ind := Index(t`Derivations[1], <{a, b}, 2>);
  if Type(t`Derivations[2][ind]) ne RngIntElt then
    Nuke := __MakeAlgebra(t, {a, b}, false, MatrixAlgebra, 
      t`Derivations[2][ind]);
    return Nuke;
  end if;

  // Make sure we can obtain the structure constants. 
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  // Construct the nucleus
  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], {a, b});

  // Construct the algebra in the correct representation
  Nuke := __MakeAlgebra(t, {a, b}, false, MatrixAlgebra, basis);

  // Sanity check
  if __SANITY_CHECK then
    printf "Sanity check (Nucleus)\n";
    assert __OperatorSanityCheck(Nuke, 2 : nuke := true);
  end if;

  // Check point!
  t`Derivations[2][ind] := basis;
  return Nuke;
end intrinsic;

intrinsic SelfAdjointAlgebra( t::TenSpcElt, a::RngIntElt, b::RngIntElt ) 
  -> ModMatFld
{Returns the vector space of ab-self-adjoint operators for the tensor t.}
  // Make sure {a,b} make sense.
  require a ne b : "Integers must be distinct.";
  v := Valence(t);
  require {a,b} subset {0..v-1} : \
    "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {a,b} : "Integers must be positive for cotensors.";
  end if;
  require Dimension(Frame(t)[v-a]) eq Dimension(Frame(t)[v-b]) : 
    "Given coordinates correspond to non-isomorphic spaces.";

  // Make sure we can obtain the structure constants. 
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  basis := __A_Centroid(Eltseq(t), [Dimension(X) : X in Frame(t)], {a, b} : 
    repeats := {{a, b}});

  // Quick fix.
  KSqMatSp := func< K, n | KMatrixSpace(K, n, n) >;
  return __MakeAlgebra(t, {a, b}, true, KSqMatSp, basis);
end intrinsic;

// ==============================================================================
//                            Special names for bimaps
// ==============================================================================
intrinsic AdjointAlgebra( t::TenSpcElt ) -> AlgMat
{Returns the adjoint *-algebra of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  if assigned t`Bimap`Adjoint then
    return t`Bimap`Adjoint;
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  S := SystemOfForms(t);
  A := AdjointAlgebra(S);
  DerivedFrom(~A, t, {2}, {2} : Fused := false);
  t`Bimap`Adjoint := A;
  return A;
end intrinsic;

intrinsic LeftNucleus( t::TenSpcElt : op := false ) -> AlgMat
{Returns the left nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  Nuke := Nucleus(t, 2, 0);
  if op then
    N := sub< Generic(Nuke) | [Transpose(X) : X in Generators(Nuke)] >;
    N`DerivedFrom := Nuke`DerivedFrom;
    return N;
  else
    return Nuke;
  end if;
end intrinsic;

intrinsic MidNucleus( t::TenSpcElt ) -> AlgMat
{Returns the mid nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  return Nucleus(t, 2, 1);
end intrinsic;

intrinsic RightNucleus( t::TenSpcElt ) -> AlgMat
{Returns the right nucleus of the 3-tensor t.}
  require t`Valence eq 3 : "Tensor must have valence 3.";
  return Nucleus(t, 1, 0);
end intrinsic;

// ==============================================================================
//                           Polynomial-based invariants
// ==============================================================================
intrinsic Discriminant( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) discriminant of the 3-tensor t.}
  require t`Valence eq 3 : "Only defined for tensors of valence 3.";
  K := BaseRing(t);
  require Type(K) ne BoolElt : "Tensor must have a base ring.";
  require Dimension(t`Domain[1]) eq Dimension(t`Domain[2]) : "Discriminant not defined for this tensor.";
  C := t`Codomain;
  n := Dimension(C);
  R := PolynomialRing(K,n);
  try
    S := SystemOfForms(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  MA := MatrixAlgebra(K,Nrows(S[1]));
  return Determinant( &+[ (MA!S[i])*R.i : i in [1..n] ] );
end intrinsic;

intrinsic Pfaffian( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) Pfaffian of the alternating 3-tensor.}
  require t`Valence eq 3 : "Only defined for tensors of valence 3.";
  require IsAlternating(t) : "Tensor must be alternating.";
  try
    disc := Discriminant(t);
  catch err
    error "Cannot compute the discriminant of the bimap."; 
  end try;
  if disc ne Parent(disc)!0 then
    factors := Factorisation(disc);
    assert forall{ f : f in factors | IsEven(f[2]) };
    return &*[ f[1]^(f[2] div 2) : f in factors ];
  end if;
  return Parent(disc)!0;
end intrinsic;
