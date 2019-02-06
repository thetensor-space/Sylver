
__vector_to_matrix := function(x,a,b)
	X := Matrix(BaseRing(x), a,a, Eltseq(x)[1..(a^2)]);
	Y := Matrix(BaseRing(x), b,b, Eltseq(x)[(a^2+1)..(a^2+b^2)]);
	return X,Y;
end function;

/*
	XA - BY = C

	A is s x b x c, 
	B is a x t x c
	C is a x b x c

 */
Adj2 := function( formsA, formsB, formsC )
	c := #formsC;	
assert ( c eq #formsB ) and (c eq #formsA);

	a := Nrows(formsC[1]);
assert (a eq Nrows(formsB[1]));
	b := Ncols(formsC[1]);
assert (b eq Ncols(formsA[1]));
	K := BaseRing(formsC[1]);

	s := Nrows(formsA[1]);
	t := Ncols(formsB[1]);

	A := formsA[1];
	for i in [2..c] do
		A := HorizontalJoin(A, formsA[i]);
	end for;


	
	mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	for j in [1..a] do
		InsertBlock(~mat, A, s*(j-1)+1, b*c*(j-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in formsB ];
	for i in [1..a] do
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~mat, slicedforms[j][i], t*(k-1)+a*s+1, c*b*(i-1)+b*(j-1)+k );
			end for;
		end for;
	end for;
	delete slicedforms;

	
	return Nullspace(mat);
end function;


/*
	XA - BY = 0

	A is s x b x c, 
	B is a x t x c

 */
Adj3 := function( formsA, formsB )
	c := #formsA;	
assert ( c eq #formsB );

	a := Nrows(formsB[1]);
	b := Ncols(formsA[1]);
	K := BaseRing(formsA[1]);

	s := Nrows(formsA[1]);
	t := Ncols(formsB[1]);

	A := formsA[1];
	for i in [2..c] do
		A := HorizontalJoin(A, formsA[i]);
	end for;

	// echelonize the columns of A, storing the transform.
	// magma only does row-echelon (even though it only does right nullspace) grumble.
	temp := Transpose(A);
	temp, T := EchelonForm(temp);
	r := Rank(temp);
	// copy the content left over
	temp := ExtractBlock( temp, 1,1, r, Ncols(temp) );
	A := Transpose(temp);
	T := Transpose(T);
	delete temp;
		
	//mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	// PENDING: it makes no sense to make this matrix, should just
	// store A and back solve iteratively.
	m1 := ZeroMatrix(K, s*a, r*a );
	for i in [1..a] do
		InsertBlock(~m1, A, s*(i-1)+1, r*(i-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in formsB ];
	m2 := ZeroMatrix(K, t*b, r*a);
	m3 := ZeroMatrix(K, t*b, a*b*c-r*a);
	for i in [1..a] do
		// Build the block blow the A's but hit it with the echelon transform.
		Z := ZeroMatrix(K, t*b, b*c);
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~Z, slicedforms[j][i], t*(k-1)+1, b*(j-1)+k );
			end for;
		end for;
		Z := Z*T;
		// Partition along pivot lines and shuffle into echelon form.
		Z0 := ExtractBlock( Z, 1, 1, t*b, r );
		InsertBlock(~m2, Z0, 1, r*(i-1)+1 );

		Z1 := ExtractBlock( Z, 1, r+1, t*b, b*c-r);
		InsertBlock(~m3, Z1, 1, (c*b-r)*(i-1)+1 );
	end for;
	delete slicedforms;
	
	// Now solve.
	Y := NullspaceMatrix(m3);
	rep, U := Solution( m1, -Y*m2);
	XMats := [ Matrix(K,a,s, rep+x ) : x in Basis(U) ];
	YMats := [ Matrix(K,t,b, Eltseq(Y[i]) ) : i in [1..Nrows(Y)]];
	
	Bas := [ DiagonalJoin(XMats[i],YMats[i]) : i in [1..#XMats]];
	return sub<MatrixAlgebra(K,a^2+b^2) | Bas >;

//	return X, Y;
end function;

/*
	XA - BY = 0

	A is s x b x c, 
	B is a x t x c

 */
Adj5 := function( forms )
	c := #forms;	

	a := Nrows(forms[1]);
	b := Ncols(forms[1]);
	K := BaseRing(forms[1]);

	s := Nrows(forms[1]);
	t := Ncols(forms[1]);

	A := forms[1];
	for i in [2..c] do
		A := HorizontalJoin(A, forms[i]);
	end for;

	// echelonize the columns of A, storing the transform.
	// magma only does row-echelon (even though it only does right nullspace) grumble.
	temp := Transpose(A);
	temp, T := EchelonForm(temp);
	r := Rank(temp);
	// copy the content left over
	temp := ExtractBlock( temp, 1,1, r, Ncols(temp) );
	A := Transpose(temp);
	T := Transpose(T);
	delete temp;
		
	//mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	// PENDING: it makes no sense to make this matrix, should just
	// store A and back solve iteratively.
	m1 := ZeroMatrix(K, s*a, r*a );
	for i in [1..a] do
		InsertBlock(~m1, A, s*(i-1)+1, r*(i-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in forms ];
	m2 := ZeroMatrix(K, t*b, r*a);
	m3 := ZeroMatrix(K, t*b, a*b*c-r*a);
	for i in [1..a] do
		// Build the block blow the A's but hit it with the echelon transform.
		Z := ZeroMatrix(K, t*b, b*c);
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~Z, slicedforms[j][i], t*(k-1)+1, b*(j-1)+k );
			end for;
		end for;
		Z := Z*T;
		// Partition along pivot lines and shuffle into echelon form.
		Z0 := ExtractBlock( Z, 1, 1, t*b, r );
		InsertBlock(~m2, Z0, 1, r*(i-1)+1 );

		Z1 := ExtractBlock( Z, 1, r+1, t*b, b*c-r);
		InsertBlock(~m3, Z1, 1, (c*b-r)*(i-1)+1 );
	end for;
	delete slicedforms;
	
	// Now solve.
	Sym := Nullspace(HorizontalJoin(m1+m2,m3));
	Alt := Nullspace(HorizontalJoin(m1-m2,m3));
//	Sym := Nullspace(m1+m2);
//	Alt := Nullspace(m1-m2);
	
//	Sym := Y meet Sym;
//	Alt := Y meet Alt;
	return [Matrix(K,a,s,Eltseq(x)) : x in Basis(Sym)], [Matrix(K,t,b,Eltseq(x)) : x in Basis(Alt)];
//	Sym := sub< Generic(Y) |
//	rep, U := Solution( m1, -Y*m2);
//	XMats := [ Matrix(K,a,s, rep+x ) : x in Basis(U) ];
//	YMats := [ Matrix(K,t,b, Eltseq(Y[i]) ) : i in [1..Nrows(Y)]];
	
//	Bas := [ DiagonalJoin(XMats[i],YMats[i]) : i in [1..#XMats]];
//	return sub<MatrixAlgebra(K,a^2+b^2) | Bas >;

//	return X, Y;
end function;
/*
	XA - AY = 0

	A nondegenerate
 */
Adj4 := function( forms )
	c := #forms;	

	a := Nrows(forms[1]);
	b := Ncols(forms[1]);
	K := BaseRing(forms[1]);

	s := Nrows(forms[1]);
	t := Ncols(forms[1]);

	A := forms[1];
	for i in [2..c] do
		A := HorizontalJoin(A, forms[i]);
	end for;

	// echelonize the columns of A, storing the transform.
	// magma only does row-echelon (even though it only does right nullspace) grumble.
	temp := Transpose(A);
	temp, T := EchelonForm(temp);
	r := Rank(temp);
	// copy the content left over
//	temp := ExtractBlock( temp, 1,1, r, Ncols(temp) );
//	A := Transpose(temp);
	T := Transpose(T);
	delete temp;
		
	//mat := ZeroMatrix( K, a*s+t*b, a*b*c );
	// PENDING: it makes no sense to make this matrix, should just
	// store A and back solve iteratively.
	m1 := ZeroMatrix(K, s*a, r*a );
	for i in [1..a] do
		InsertBlock(~m1, A, s*(i-1)+1, r*(i-1)+1 );
	end for;

	delete A;

	slicedforms := [ [ ExtractBlock(-Transpose(B), 1, i, t, 1) : i in [1..a]] : B in forms ];
	m2 := ZeroMatrix(K, t*b, r*a);
	m3 := ZeroMatrix(K, t*b, a*b*c-r*a);
	for i in [1..a] do
		// Build the block blow the A's but hit it with the echelon transform.
		Z := ZeroMatrix(K, t*b, b*c);
		for j in [1..c] do
			for k in [1..b] do
				InsertBlock(~Z, slicedforms[j][i], t*(k-1)+1, b*(j-1)+k );
			end for;
		end for;
		Z := Z*T;
		// Partition along pivot lines and shuffle into echelon form.
//		Z0 := ExtractBlock( Z, 1, 1, t*b, r );
//		InsertBlock(~m2, Z0, 1, r*(i-1)+1 );

		Z1 := ExtractBlock( Z, 1, r+1, t*b, b*c-r);
		InsertBlock(~m3, Z1, 1, (c*b-r)*(i-1)+1 );
	end for;
	delete slicedforms;
	
	// Now solve.
	Y := NullspaceMatrix(m3);
	X := Solution( m1, -Y*m2);
	XMats := [ Matrix(K,a,s, x ) : x in Basis(X) ];
	YMats := [ Matrix(K,t,b, Y[i] ) : i in [1..Nrows(Y)]];
	
	Bas := [ DiagonalJoin(XMats[i],YMats[i]) : i in [1..#XMats]];
	return Bas;//sub<MatrixAlgebra(K,a^2+b^2) | Bas >;
end function;

test := function(K, a,b,c,s,t)
	MA := KMatrixSpace(K, s,b);
	formsA := [Random(MA) : i in [1..c]];
	MB := KMatrixSpace(K, a,t);
	formsB := [Random(MB) : i in [1..c]];
	MC := KMatrixSpace(K, a,b);
	formsC := [Random(MC) : i in [1..c]];
	return formsA, formsB, formsC;
end function;

test2 := function(K, d, e )
	MA := MatrixAlgebra(K, d);
	return [ Random( MA) : i in [1..e]];
end function;

test_sym := function(K, d, e )
	MA := MatrixAlgebra(K, d);
	forms := [ Random( MA) : i in [1..e]];
	return [ X+Transpose(X) : X in forms ];
end function;

test_alt := function(K, d, e )
	MA := MatrixAlgebra(K, d);
	forms := [ Random( MA) : i in [1..e]];
	return [ X-Transpose(X) : X in forms ];
end function;

big_test := function(K, trials : dmax := 50 )
	new0 := 0.0;
	new1 := 0.0;
	new2 := 0.0;
	new3 := 0.0;
	dave := 0;
	eave := 0;
	for i in [1..trials] do
		d := Random([4..dmax]);
		e := Random([3..Minimum({10,2*d})]);
		if Random(1) eq 0 then
			forms := test_sym(K, d, e );
		else 
			forms := test_alt(K, d, e );
		end if;
		if #forms eq 0 then continue; end if;
		dave +:= d;
		eave +:= e;
		t := Cputime();
		XY := AdjointAlgebra(forms);
		new0 +:= Cputime(t);

		t := Cputime();
		XY := Adj2(forms,forms,forms);
		new1 +:= Cputime(t);

		t := Cputime();
		X, Y := Adj3(forms,forms);
		new2 +:= Cputime(t);

		t := Cputime();
		Y := Adj4(forms);
		new3 +:= Cputime(t);
		
		if i mod 10 eq 0 then
			print new0, new1, new2, new3;
			print "average dim ", 1.0*dave/i, " e ave: ", 1.0*eave/i;
		end if;
	end for;
	return new0, new1, new2, new3, 1.0*dave/trials, 1.0*eave/trials;
end function;

star := function( x )
	d := Nrows(x) div 2;
	F := ExtractBlock(x,1,1,d,d);
	G := ExtractBlock(x,d+1,d+1,d,d);
	return DiagonalJoin(G,F);
end function;

split := function( A )
//t := Cputime();
//	B := Basis(A);
//a := Cputime(t);
//t := Cputime();
	symB := [ 1/2*(x+star(x)) : x in A ];
//b := Cputime(t);
//t := Cputime();
	altB := [ 1/2*(x-star(x)) : x in A ];
//c := Cputime(t);
//print a,b,c;
	return symB cat altB;
end function;

flat_g2_test := function(K, drange )
	new0 := 0.0;
	new1 := 0.0;
	new2 := 0.0;
	new3 := 0.0;
	for d in drange do
		forms := test_alt(K, 2*d+1, 2 );
		if #forms eq 0 then continue; end if;
		t := Cputime();
		try 
			XY := AdjointAlgebra(forms);
		catch e
			print "degenerate skip";
		end try;
		new0 := Cputime(t);

//		t := Cputime();
//		XY := Adj2(forms,forms,forms);
//		new1 +:= Cputime(t);

//		t := Cputime();
//		A := Adj3(forms,forms);
//		new2 +:= Cputime(t);
	
//		t := Cputime();
//		Asplit := split(A);
//		new1 +:= Cputime(t);
		
//		t := Cputime();
//		Y := Adj4(forms);
//		Ys := split(Y);
//		new3 +:= Cputime(t);

		t := Cputime();
		Sym, Alt  := Adj5(forms);
		new4 := Cputime(t);		
//		if d mod 4 eq 0 then
			//print new0, new1, new2, new3;
			print (2*d+1), ":", new0, new4, (new0 / new4);
//		end if;
	end for;
	return new0, new4;
end function;

