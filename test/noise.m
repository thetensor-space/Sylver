__add_noise := function (a, epsilon)
return a + epsilon * Random ([-1000..1000]) / 1000;
end function;

AddNoise := function (t, epsilon) 
  l := Eltseq (t);
return Parent (t)![ __add_noise (l[i] , epsilon) : i in [1..#l] ];
end function;

