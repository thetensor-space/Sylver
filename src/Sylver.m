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
        return true, <X, Y>, N, <M, v>;
    else
        return false, _, N, <M, v>;
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
    C::TenSpcElt :
    sparse := true
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
    require Type(sparse) eq BoolElt : "Parameter 'sparse' must be boolean.";

    // Slice and initialize the data.
    e, f := __build_vectors(K, a, b, sparse);
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