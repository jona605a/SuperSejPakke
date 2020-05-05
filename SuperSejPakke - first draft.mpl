
SuperSejPakke := module()
option package;
export Jacobi, gradient, div, rot, evectors, prik, len, vop, integrer, flux, tangielt, stokes, flowkurve, flowkurveSolve, tay, hesse;

Jacobi := proc(r::{procedure})
   local kryds, i, var;
   var := [op(1,eval(r))]:
   kryds:=(x,y)->convert(VectorCalculus[CrossProduct](x,y),Vector):
   if (numelems(var) = 1) then # Kurve jacobi
   simplify(LinearAlgebra[Norm](diff(r(var[1]),var[1]),2)) assuming var[1]::real

   elif (numelems(var) = 2 and numelems(r(vop(var))) = 2) then # Plan jacobi
   simplify(abs((VectorCalculus[Jacobian](r(vop(var)),var,determinant)[2]))) assuming var[1]::real, var[2]::real

   elif (numelems(var) = 2) then # Flade jacobi
   simplify(LinearAlgebra[Norm](kryds(diff(r(vop(var)),var[1]),diff(r(vop(var)),var[2])),2)) assuming var[1]::real, var[2]::real

   elif (numelems(var) = 3)  then # Rum jacobi
   simplify(abs((VectorCalculus[Jacobian](r(vop(var)),var,determinant)[2]))) assuming var[1]::real, var[2]::real, var[3]::real
   else 0 # Overvej om vi vil have en fejlbesked
end if: end proc:

gradient := proc(f::{procedure,algebraic},opss::list:=[x,y,z])
local i, ops;
if (type(f,procedure)) then ops := op(1,eval(f)): <seq(diff(f(ops),ops[i]),i=1..nops([ops]))>;
else <seq(diff(f,opss[i]),i=1..nops(opss))>
end if: end proc:

rot:=proc(V::{procedure, Vector}) uses VectorCalculus;BasisFormat(false); local v,var;
if (type(V,procedure)) then v := V(op(1,eval(V))); var := [op(1,eval(V))]: 
unapply(Curl(Student[VectorCalculus][VectorField](v)),[vop(var)]);
else v := V; 
Curl(Student[VectorCalculus][VectorField](v));
end if: 
end proc:

div:= proc(V::{procedure, Vector}); local v;
if (type(V,procedure)) then v := V(op(1,eval(V))); else v := V; end if: 
unapply(VectorCalculus[Divergence](Student[VectorCalculus][VectorField](v)),[x,y,z])
end proc:

evectors:= proc(A::{Matrix});
sort(LinearAlgebra[Eigenvectors](A,output = list));
end proc:

prik:= proc(a::{Vector},b::{Vector})
LinearAlgebra[Transpose](a).b;
end proc:

len:= proc(a::{Vector})
sqrt(prik(a,a));
end proc:

vop:=proc(X) 
op(convert(X,list)) 
end proc:

integrer:= proc(r::{procedure},integrateRange::{list},f::{procedure}:=1);
local var, i;
var := [op(1,eval(r))]:
int(f(vop(r(vop(var))))*Jacobi(r),seq(var[i]=integrateRange[i],i=1..numelems(integrateRange)));
end proc:

flux:= proc(r::{procedure},integrateRange::{list},V::{procedure});
local var,i;
var := [op(1,eval(r))]:
int(prik(V(vop(r(vop(var)))),LinearAlgebra[CrossProduct](diff(r(vop(var)),var[1]),diff(r(vop(var)),var[2]))),seq(var[i]=integrateRange[i],i=1..numelems(integrateRange)));
end proc:

tangielt:= proc(r::{procedure},integrateRange::{range},V::{procedure})
local var,i;
var := [op(1,eval(r))]:
int(prik(V(vop(r(var[1]))),diff(r(var[1]),var[1])),var[1]=integrateRange);
end proc:

stokes:= proc(r::{procedure},integrateRange::{list},V::{procedure});
local var,i; var := [op(1,eval(V))]:
flux(r,integrateRange,unapply(rot(V(vop(var))),var));
end proc:

flowkurve:= proc(V::{procedure},starttid::{numeric}:=0,punkt::{list} := [1]);
local i, var, funk, løs;
var := [op(1,eval(V))]:
funk := [seq(var[i](t),i=1..3)]:
løs := dsolve([seq(diff(funk[i],t)=V(vop(funk))[i],i=1..3), if numelems(punkt) > 1 then seq(var[i](starttid)=punkt[i],i=1..3) else end if]):
unapply(subs(løs,<seq(var[i](t),i=1..3)>),[t]);
end proc:

flowkurveSolve := proc(flow::{procedure},punkt::{list});
local var, i; var := [op(1,eval(flow))]:
unapply(subs(solve([seq(flow(punkt[1])[i]=punkt[i+1],i=1..3)]),flow(var[1])),var[1]);
end proc:

tay := proc(f::{procedure},punkt::{list,integer},grad::{integer})
local var,i; var := [op(1,eval(f))]:
unapply(mtaylor(f(vop(var)),if numelems(var) = 1 then var[1] = punkt else [seq(var[i]=punkt[i],i=1..numelems(var))] end if, grad+1),var);
end proc:

hesse:= proc(f::{procedure})
local var; var := [op(1,eval(f))]:
unapply(VectorCalculus[Hessian](f(vop(var)),[vop(var)]),[vop(var)]);
end proc:


end module;
with(SuperSejPakke)
;
# !!!TIL BRUG AF PAKKE!!!
# Eksporter dette dokument som .mpl fil i den mappe, du gerne vil opbevare den i.
# 
# Lav derefter din path i maple til den mappe på samme på måde som gjort herunder. (Kør kommandoen for i et andet worksheet for at forstå, hvad den gør)

# 
# - mylibdir := cat(kernelopts(homedir),kernelopts(dirsep),"Desktop",kernelopts(dirsep),"Uniarbejde",kernelopts(dirsep),"Matematik 1",kernelopts(dirsep),"SuperSejPakke",kernelopts(dirsep),"Navn du eksporterede filen som");

# kør derefter kommandoen 
# 
# - read(mylibdir)

# efterfulgt af
# 
# with(Dit valgte pakkenavn)
# 
# Og pakken kan nu anvendes.
# Hvis du gerne vil kunne åbne den hver gang du lave et worksheet dokument med alle kommandoerne og via Tools-menuen i maple's top bar
# sætte det som dit standard dokument, du åbner.
# 
# 
# 
# 

# !!!FORKLARING AF HVER KOMMANDO!!!
# Kommer senere...
# 
# Hej Hans. Tænker vi bare laver hjælpekommandoer i hver funktion?
# 
# 

# Her er funktionerne brugt lidt

r:=(u,v,w)-> <u,v*(5-u^2),w>
;
Jacobi(r)
;
evectors(<4,1;3,2>)
;

V:=(x,y,z)-> <x+4*y,z+x,-7*x>
;
stokes(r,[0..4,0..1,0..2*Pi],V)
;
eval(r)
;
h:=(x,y)-> x^3-sin(y)
;
tay(h,[-1,2],2)
;

