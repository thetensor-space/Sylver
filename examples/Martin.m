// no Lagrangian in Magma, apparently
__laplacian := function (f)
  r := Rank (Parent (f));
return &+ [ Derivative (Derivative (f, i), i) : i in [1..r] ];
end function;

Laplacian := function (f, p)
     g := f;
     for i in [1..p] do
          g := __laplacian (g);
     end for;
return g;
end function;

//K := Rationals ();
K := RealField (10);
R<x,y,z> := PolynomialRing (K,3);

// Martin's kernel basis
B0 := [ R!1 ];  

B1 := [ x , 
        y , 
        z ];   

B2 := [ 2*z^2-x^2-y^2 , 
        z*x , 
        z*y , 
        x^2 - y^2 , 
        x*y ];

B3 := [ 2*z^3-3*z*x^2-3*z*y^2 , 
        (4*z^2-x^2-y^2)*x , 
        (4*z^2-x^2-y^2)*y , 
        z*(x^2-y^2) , 
        z*x*y , 
        x^3 - 3*x*y^2 , 
        3*x^2*y - y^3 ];
    
B4 := [ 8*z^4-24*z^2*(x^2+y^2) + 3*(x^2+y^2)^2 , 
        (4*z^3-3*z*x^2-3*z*y^2)*x , 
        (4*z^3-3*z*x^2-3*z*y^2)*y , 
        (6*z^2-y^2-x^2)*(x^2-y^2) , 
        (6*z^2-y^2-x^2)*x*y , 
        z*(x^3-3*x*y^2) , 
        z*(3*x^2*y-y^3) , 
        x^4-6*x^2*y^2+y^4 , 
        x*y*(x^2-y^2) ];
        
// test
/*
isit := true;
for i in [1..1000] do
  f := Random (B1) * Random (B2) * Random (B3) * Random (B4);
  isit and:= (Integers ()!(Laplacian (f, 5)) mod (32*Factorial (6)) eq 0);
end for;
isit;
*/

__entry := function (a, b, c, d)
return Laplacian (a * b * c * d, 5) / (32 * Factorial (6));
end function;

// build the tensor
mt := Tensor ([3,5,7,9] , [ K!0 : s in [1..3*5*7*9] ]);
mt := Tensor ([3,5,7,9] , [ K!0 : s in [1..3*5*7*9] ]);
for i in [1..3] do
  for j in [1..5] do 
    for k in [1..7] do
      for l in [1..9] do
        Assign (~mt, [i,j,k,l], K!(__entry (B1[i] , B2[j] , B3[k] , B4[l])));
      end for;
    end for;
  end for;
end for;

