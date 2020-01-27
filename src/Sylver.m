/* 
    Copyright 2020 Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


/*
    This file contains functions we use to test the various approaches to solving Sylvester equations. 
*/

intrinsic SylvesterDenseSolve( A::TenSpcElt, B::TenSpcElt, C::TenSpcElt ) -> .
{Returns the tuple of matrices (X, Y) along with the vector space of solutions (to the homogeneous version) to the Sylvester equation: XA + BY = C.}
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

    // a sanity checker
    _check := function(X, Y : homogeneous := false)
        A_forms := SystemOfForms(A);
        B_forms := SystemOfForms(B);
        if homogeneous then 
            C_forms := [ZeroMatrix(K, a, b) : i in [1..c]];
        else
            C_forms := SystemOfForms(C);
        end if;
        for k in [1..c] do
            if X*A_forms[k] + B_forms[k]*Y ne C_forms[k] then
                return false;
            end if;
        end for;
        return true;
    end function;

    z := Eltseq(Random(N));
    X := Matrix(K, a, s, z[1..a*s]);
    Y := Transpose(Matrix(K, b, t, z[a*s + 1..#z]));
    assert _check(X, Y : homogeneous := true);

    if consistent then
        y := Eltseq(x);
        X := Matrix(K, a, s, y[1..a*s]);
        Y := Transpose(Matrix(K, b, t, y[a*s + 1..#y]));
        assert _check(X, Y);
        return x, N, <M, v>;
    else
        return false, N, <M, v>;
    end if;
end intrinsic;