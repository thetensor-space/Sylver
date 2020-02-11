/* 
    Copyright 2020 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
    This file contains functions we use to test the various approaches to 
    solving Sylvester equations. These are equations of the form
        XA + BY = C.
*/

// a sanity checker
intrinsic SylvesterCheck( 
    A::TenSpcElt, 
    B::TenSpcElt, 
    C::TenSpcElt, 
    X::Mtrx, 
    Y::Mtrx 
) -> BoolElt
{Decides if (X, Y) is a solution to the Sylvester equation relating the tensors 
A, B, and C.}
    c := Dimension(Codomain(C));
    A_forms := SystemOfForms(A);
    B_forms := SystemOfForms(B);
    C_forms := SystemOfForms(C);
    for k in [1..c] do
        if X*A_forms[k] + B_forms[k]*Y ne C_forms[k] then
            return false;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic SylvesterDenseSolve( A::TenSpcElt, B::TenSpcElt, C::TenSpcElt ) -> .
{Returns the tuple of matrices (X, Y) along with the vector space of solutions 
(to the homogeneous version) to the Sylvester equation: XA + BY = C.}
    K := BaseRing(C);
    require BaseRing(A) eq K : "Incompatible base fields.";
    require BaseRing(B) eq K : "Incompatible base fields.";
    a := Dimension(Domain(C)[1]);
    b := Dimension(Domain(C)[2]);
    c := Dimension(Codomain(C));
    s := Dimension(Domain(A)[1]);
    t := Dimension(Domain(B)[2]);
    require Dimension(Domain(B)[1]) eq a : "Incompatible dimensions.";
    require Dimension(Domain(A)[2]) eq b : "Incompatible dimensions.";
    require Dimension(Codomain(A)) eq c : "Incompatible dimensions.";
    require Dimension(Codomain(B)) eq c : "Incompatible dimensions.";

    /*
        Build the ingredients to get Mx = v.
        We build two "pillars" M = [P1 | P2].
    */
    // Vector
    C_blocks := AsMatrices(C, 2, 0);
    C_flats := [Eltseq(X) : X in C_blocks];
    v := Matrix(K, a*b*c, 1, &cat(C_flats));

    // Pillar #2
    B_slices := AsMatrices(B, 0, 1);
    B_block := VerticalJoin(<S : S in B_slices>);
    Pill2 := KroneckerProduct(IdentityMatrix(K, b), B_block);
    assert Nrows(Pill2) eq a*b*c;
    assert Ncols(Pill2) eq b*t;

    // Pillar #1
    A_slices := AsMatrices(A, 0, 2); 
    A_blwnup := <KroneckerProduct(IdentityMatrix(K, a), X) : X in A_slices>;
    Pill1 := VerticalJoin(A_blwnup);
    assert Nrows(Pill1) eq a*b*c;
    assert Ncols(Pill1) eq a*s;

    M := HorizontalJoin(Pill1, Pill2);

    consistent, x := IsConsistent(Transpose(M), Transpose(v));
    N := NullspaceOfTranspose(M);

    z := Eltseq(Random(N));
    X := Matrix(K, a, s, z[1..a*s]);
    Y := Transpose(Matrix(K, b, t, z[a*s + 1..#z]));
    Z := KTensorSpace(K, [a, b, c])!0;
    // Check that (X, Y) is a solution to the homogenous version.
    assert SylvesterCheck(A, B, Z, X, Y);

    if consistent then
        y := Eltseq(x);
        X := Matrix(K, a, s, y[1..a*s]);
        Y := Transpose(Matrix(K, b, t, y[a*s + 1..#y]));
        // Check that (X, Y) is a solution.
        assert SylvesterCheck(A, B, C, X, Y);
        return true, <X, Y>, N, <Transpose(M), Transpose(v)>;
    else
        return false, _, N, <Transpose(M), Transpose(v)>;
    end if;
end intrinsic;

__build_vectors := function(K, a, b, sparse)
    if sparse then
        e_nonzeros := Random([1..Minimum(3, a)]);
        f_nonzeros := Random([1..Minimum(3, b)]);
    else
        e_nonzeros := Random([a div 2..3*a div 4]);
        f_nonzeros := Random([b div 2..3*b div 4]);
    end if;
    e_terms := {Random([1..a]) : i in [1..e_nonzeros]};
    f_terms := {Random([1..b]) : i in [1..f_nonzeros]};
    get_elt := func< K | IsFinite(K) select Random(K) else 1 >;
    e := [0 : i in [1..a]];
    f := [0 : i in [1..b]];
    for i in e_terms do
        e[i] := get_elt(K);
    end for;
    for i in f_terms do
        f[i] := get_elt(K);
    end for;
    return e, f;
end function;

intrinsic SylvesterFastExistenceCheck(
    A::TenSpcElt,
    B::TenSpcElt,
    C::TenSpcElt 
) -> BoolElt
{Quickly decides if the Sylvester equation might not have a solution. A false 
means that no solution exists, and nothing can be concluded from a true.}
    // First check the data
    K := BaseRing(C);
    require BaseRing(A) eq K : "Incompatible base fields.";
    require BaseRing(B) eq K : "Incompatible base fields.";
    a := Dimension(Domain(C)[1]);
    b := Dimension(Domain(C)[2]);
    c := Dimension(Codomain(C));
    s := Dimension(Domain(A)[1]);
    t := Dimension(Domain(B)[2]);
    require Dimension(Domain(B)[1]) eq a : "Incompatible dimensions.";
    require Dimension(Domain(A)[2]) eq b : "Incompatible dimensions.";
    require Dimension(Codomain(A)) eq c : "Incompatible dimensions.";
    require Dimension(Codomain(B)) eq c : "Incompatible dimensions.";

    // Slice and initialize the data.
    e, f := __build_vectors(K, a, b);
    A_slices := AsMatrices(A, 2, 0);
    B_slices := AsMatrices(B, 1, 0);
    C_slices := AsMatrices(C, 1, 0); 
    M_A := Parent(A_slices[1])!0; 
    M_B := Parent(B_slices[1])!0; 
    M_C := Parent(C_slices[1])!0; 
    v_C := Parent(M_C[1])!0; 

    // No reason to waste time multiplying 0*M
    i := 1;
    while i lt a do
        if e[i] ne 0 then
            M_B +:= e[i]*B_slices[i];
            M_C +:= e[i]*C_slices[i];
        end if;
        i +:= 1;
    end while;
    i := 1;
    while i lt b do
        if f[i] ne 0 then
            M_A +:= f[i]*A_slices[i];
            v_C +:= f[i]*M_C[i];
        end if;
        i +:= 1;
    end while;

    // The check
    check := IsConsistent(VerticalJoin(M_A, M_B), v_C);
    return check;
end intrinsic;

// Given two tensors A, B, construct random invertible matrices and mix the 
// terms of A and B accordingly. We return the mixed tensors A, B together with 
// the random matrices P, Q.
__precondition := function(A, B)
    // Assume A and B have the roles:
    //      XA + BY = C.
    K := BaseRing(A);
    A_slices := AsMatrices(A, 2, 1);
    B_slices := AsMatrices(B, 2, 1);
    s := Nrows(A_slices[1]);
    t := Ncols(B_slices[1]);
    P := Random(GL(s, K));
    Q := Random(GL(t, K));
    A_mixed := [P*X : X in A_slices];
    B_mixed := [X*Q : X in B_slices];
    return Tensor(A_mixed, 2, 1), Tensor(B_mixed, 2, 1), P, Q;
end function;

// Given a sequence of matrices S, determine its slice rank.
__get_slice_rank := function(S)
    // Terminates the recursion.
    if #S eq 0 then
        return 0;
    elif Parent(S[1])!0 eq S[1] then
        if exists(k){k : k in [2..#S] | Parent(S[1])!0 ne S[k]} then
            return k - 1 + $$(S[k..#S]);
        else
            return 0;
        end if;
    elif #S eq 1 then // S ne 0 here
        return 1;
    end if;

    // Echelonize the first matrix, and extract the top right block.
    E, T := EchelonForm(S[1]);
    r := Rank(E);
    // If full rank, we are done.
    if Ncols(E) eq r then
        return 1;
    end if;
    // Otherwise, we recurse.
    M := ExtractBlock(E, 1, r + 1, r, Ncols(E) - r);
    Extract := function(A)
        // A = [X Y] |-> Y - XM
        X := ExtractBlock(A, 1, 1, Nrows(A), r);
        Y := ExtractBlock(A, 1, r + 1, Nrows(A), Ncols(A) - r);
        return Y - X*M;
    end function;
    return 1 + $$([Extract(A) : A in S[2..#S]]);
end function;

/*
    Given a matrix U and A, determine a matrix V such that V*U + A = 0. The 
    assumption is that the matrix 
        [ U ]
        [ A ]
    has a RREF equal to 
        [ U ]
        [ 0 ].
    In particular, U is already in RREF. 
*/
__get_clearing_matrix := function(U, A)
    K := BaseRing(A);
    V := InsertBlock(ZeroMatrix(K, Nrows(A), Nrows(U)), -A, 1, 1);
    assert V*U + A eq Parent(A)!0;
    return V;
end function;


intrinsic SylvesterQuickSolve(
    A::TenSpcElt,
    B::TenSpcElt,
    C::TenSpcElt : 
    verbose_print := true
) -> BoolElt, .
{Decides if there exists a solution to the corresponding Sylvester equation. If so, returns a solution (X, Y).}
    K := BaseRing(C);
    require BaseRing(A) eq K : "Incompatible base fields.";
    require BaseRing(B) eq K : "Incompatible base fields.";
    a := Dimension(Domain(C)[1]);
    b := Dimension(Domain(C)[2]);
    c := Dimension(Codomain(C));
    s := Dimension(Domain(A)[1]);
    t := Dimension(Domain(B)[2]);
    require Dimension(Domain(B)[1]) eq a : "Incompatible dimensions.";
    require Dimension(Domain(A)[2]) eq b : "Incompatible dimensions.";
    require Dimension(Codomain(A)) eq c : "Incompatible dimensions.";
    require Dimension(Codomain(B)) eq c : "Incompatible dimensions.";

    // Pre-condition. We now solve:
    //      X(PA) + (BQ)Y = C.
    if IsFinite(K) then
        A, B, P, Q := __precondition(A, B);
    else
        P := IdentityMatrix(K, s);
        Q := IdentityMatrix(K, t);
    end if;

    // Determine slice ranks.
    A_slices := AsMatrices(A, 0, 2); 
    B_slices := AsMatrices(B, 0, 1);
    r_A := __get_slice_rank(A_slices);
    r_B := __get_slice_rank(B_slices);

    // Worry about fringe case later.
    if r_A eq 0 or r_B eq 0 or r_A eq b or r_B eq a then
        print "Not implemented yet.";
        return false;
    end if;

    // Get matrix L_A which satisfies 
    //      L_A * A_cal = U_A, 
    // where U_A is upper triangular.
    A_cal := VerticalJoin(A_slices[1..r_A]);
    U_A, L_A := EchelonForm(A_cal);

    // Get the clearing matrices.
    V_mats := [__get_clearing_matrix(U_A, X) : X in A_slices[r_A + 1..b]];

    // Build the M and N matrices.
    I_r_A := IdentityMatrix(K, r_A);
    M_mats := [VerticalJoin(
        [V*L_A*KroneckerProduct(I_r_A, B) : B in B_slices[1..r_B]]
        ) : V in V_mats];
    N_mats := [VerticalJoin(
        [V*L_A*KroneckerProduct(I_r_A, B) : B in B_slices[r_B + 1..a]]
    ) : V in V_mats];

    // Get matrix L_B which satisfies 
    //      L_B * B_cal = U_B, 
    // where U_B is upper triangular.
    B_cal := VerticalJoin(B_slices[1..r_B]);
    U_B, L_B := EchelonForm(B_cal);

    // Get the clearing matrix W.
    W := __get_clearing_matrix(U_B, VerticalJoin(B_slices[r_B + 1..a]));

    // Construct the dense matrix.
    D := VerticalJoin([W*L_B*M : M in M_mats]) + VerticalJoin(N_mats);
    // We don't need the full D usually, but this is just a check.

    // Build the C-vector.
    // We keep them as matrices for now.
    C_blocks := AsMatrices(C, 1, 0);
    top_third := [ExtractBlock(X, 1, 1, r_A, Ncols(X)) : X in C_blocks];
    C_blocks := AsMatrices(C, 2, 0);
    mid_third := [ExtractBlock(X, 1, 1, r_B, Ncols(X)) : 
        X in C_blocks[r_A + 1..b]];
    bot_third := [ExtractBlock(X, r_B + 1, 1, Nrows(X) - r_B, Ncols(X)) : 
        X in C_blocks[r_A + 1..b]];
    // Sanity check
    c_vec := <X : X in top_third> cat <X : X in mid_third> 
        cat <X : X in bot_third>;
    assert #Eltseq(VerticalJoin(c_vec)) eq  a*b*c;

    // Build the F vectors.
    F_vecs := [Matrix(K, 1, c*r_A, Eltseq(X))*Transpose(L_A) : 
        X in top_third];

    // Build the G vectors.
    pre_G_vec := function(X, j)
        v := [Matrix(X[i]) + F_vecs[i]*Transpose(V_mats[j]) : 
            i in [1..Nrows(X)]];
        return Matrix(K, 1, c*r_B, &cat[Eltseq(u) : u in v]);
    end function;
    G_vecs := [pre_G_vec(mid_third[j], j)*Transpose(L_B) : j in [1..b - r_A]];

    // Build the H vectors.
    pre_H_vec := function(X, k)
        v := [Matrix(X[i]) + F_vecs[r_B + i]*Transpose(V_mats[k]) : 
            i in [1..Nrows(X)]];
        return Matrix(K, 1, c*(a - r_B), &cat[Eltseq(u) : u in v]);
    end function;
    H_vecs := [pre_H_vec(bot_third[k], k) + Matrix(G_vecs[k]*Transpose(W)): 
        k in [1..b - r_A]];
    // Flatten out H_vecs completely.
    v_H := Matrix(K, 1, c*(a - r_B)*(b - r_A), 
        &cat([Eltseq(h) : h in H_vecs]));

    // Now we push all zero rows to the bottom. 
    rho_A := Rank(U_A);
    rho_B := Rank(U_B);
    z_A := Nrows(U_A) - rho_A;
    z_B := Nrows(U_B) - rho_B;

    // Create the first matrix and C-vector from the U_A's.
    Z1 := [ExtractBlock(L_A*KroneckerProduct(I_r_A, B), c*r_A - z_A + 1, 1, 
        z_A, t*r_A) : B in B_slices];
    v_z1 := &cat[Eltseq(v)[c*r_A - z_A + 1..c*r_A] : v in F_vecs];

    // Create the second matrix from the U_B's.
    Z2 := [ExtractBlock(L_B*M, c*r_B - z_B + 1, 1, z_B, t*r_A) : M in M_mats];
    v_z2 := &cat[Eltseq(v)[c*r_B - z_B + 1..c*r_B] : v in G_vecs];

    if verbose_print then 
        print U_A, U_B;
        print Z1, v_z1;
        print Z2, v_z2;
    end if;

    // Put everything together. 
    D_z := VerticalJoin(D, VerticalJoin(VerticalJoin(Z1), VerticalJoin(Z2)));
    v_z := HorizontalJoin(v_H, Matrix(K, 1, #v_z1 + #v_z2, v_z1 cat v_z2));

    sol, x := IsConsistent(Transpose(D_z), v_z);

    return sol, Transpose(D_z), v_z;
end intrinsic;