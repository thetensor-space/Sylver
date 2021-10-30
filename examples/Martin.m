          /*---- Martin's first construction ----*/
          
/*

// no Laplacian in Magma, apparently
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

*/

        /*---- Martin's second construction ----*/

// x function for the surface
__xscale := function (i)
  return (30+i)^2;
end function;

// y function for the surface
__yscale := function (i)
  return (40+i)^2;
end function;

// z function for the surface
__zscale := function (i)
  return (50+i)^2;
end function;

  // computes the equation of the surface
__surface_eq := function(x,y,z, i,j,k)
 return x[1]*(__xscale(i) - x[2])/x[3] + y[1]*(__yscale(j) - y[2])/y[3] + z[1]*(__zscale(k) - z[2])/z[3];  
end function;

// generate entries which are random numbers with norm ~ exp( - C (surface_eq)^2)
__entry := function(x,y,z, width,i,j,k)
	s := 2* __surface_eq(x,y,z, i,j,k)/width;
	r := 0;
	// no need to randomly generate tiny numbers
	if Abs(s) gt 5 then
		r:= __add_noise(0, Exp( -s*s ) );
	end if;
	return r;
end function;

MartiniT := function(xsize, ysize, zsize, width)      
  K := RealField (10);

  // normalize the x, y, z functions 
  xnorm := Abs(__xscale(xsize) - __xscale(1));
  xavg := (__xscale(xsize) + __xscale(1)) /2 ;
  x := <xsize,xavg,xnorm>;

  ynorm := Abs(__yscale(ysize) - __yscale(1));
  yavg := (__yscale(ysize) + __yscale(1)) /2 ;
  y := <ysize,yavg,ynorm>;

  znorm := Abs(__zscale(zsize) - __zscale(1));
  zavg := (__zscale(zsize) + __zscale(1)) /2 ;
  z := <zsize,zavg,znorm>;
  // builds the tensor
  t := Tensor ([xsize,ysize,zsize] , [ K!0 : s in [1..xsize*ysize*zsize] ]);
  for i in [1..xsize] do
    for j in [1..ysize] do 
      for k in [1..zsize] do
        Assign (~t, [i,j,k], __entry (x,y,z,width,i,j,k));
      end for;
    end for;
  end for;
  return t;
end function;
