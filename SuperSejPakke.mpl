
SuperSejPakke := module()
option package;
export jacobi, gradient, div, rot, evectors, prik, kryds, normal, len, vop, integrer, flux, tangielt, stokes, flowkurve, flowkurvesolve, tay, hesse, stamfelt, funkana, paraplot,massemidte;

jacobi := proc(r::{procedure})
local i, var;
var := [op(1,eval(r))]:
if (numelems(var) = 1) then # Kurve jacobi
   simplify(LinearAlgebra[Norm](diff(r(var[1]),var[1]),2)) assuming var[1]::real
elif (numelems(var) = 2 and numelems(r(vop(var))) = 2) then # Plan jacobi
   simplify(abs((VectorCalculus[Jacobian](r(vop(var)),var,determinant)[2]))) assuming var[1]::real, var[2]::real
elif (numelems(var) = 2) then # Flade jacobi
   simplify(LinearAlgebra[Norm](kryds(diff(r(vop(var)),var[1]),diff(r(vop(var)),var[2])),2)) assuming var[1]::real, var[2]::real
elif (numelems(var) = 3)  then # Rum jacobi
   simplify(abs((VectorCalculus[Jacobian](r(vop(var)),var,determinant)[2]))) assuming var[1]::real, var[2]::real, var[3]::real
else Xi # Overvej om vi vil have en fejlbesked
end if: end proc:

gradient := proc(f::{procedure,algebraic},opss::list:=[x,y,z])
local i, ops;
if (type(f,procedure)) then ops := op(1,eval(f)): unapply(<seq(diff(f(ops),ops[i]),i=1..nops([ops]))>,[ops]);
else <seq(diff(f,opss[i]),i=1..nops(opss))>
end if: end proc:

rot:=proc(V::{procedure, Vector}) uses VectorCalculus;BasisFormat(false); local v, var;
if (type(V,procedure)) then v := V(op(1,eval(V))); var:=[op(1,eval(V))]:
unapply(Curl(Student[VectorCalculus][VectorField](v)),var);
else v := V; 
Curl(Student[VectorCalculus][VectorField](v));
end if: 
end proc:

div:= proc(V::{procedure, Vector}); local v;
if (type(V,procedure)) then v := V(op(1,eval(V))); else v := V; end if: 
if (numelems(v)=2) then unapply(VectorCalculus[Divergence](Student[VectorCalculus][VectorField](v)),[x,y]);
else unapply(VectorCalculus[Divergence](Student[VectorCalculus][VectorField](v)),[x,y,z]);
end if; end proc:

evectors:= proc(A::{Matrix});
sort(LinearAlgebra[Eigenvectors](A,output = list));
end proc:

prik:=proc(x::Vector,y::Vector);VectorCalculus[DotProduct](x,y); end proc:

normal:=proc(r::{procedure})
local var; var:=op(1,eval(r)):
if (numelems([var])=2) then kryds(diff(r(var),var[1]),diff(r(var),var[2]));
else print("Dont dead open inside");
end if;
end proc:

kryds:=proc(x::Vector,y::Vector);
convert(VectorCalculus[CrossProduct](x,y),Vector);
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
int(f(vop(r(vop(var))))*jacobi(r),seq(var[i]=integrateRange[i],i=1..numelems(integrateRange)));
end proc:

flux:= proc(r::{procedure},integrateRange::{list},V::{procedure});
local var,i;
var := [op(1,eval(r))]:
int(prik(V(vop(r(vop(var)))),LinearAlgebra[CrossProduct](diff(r(vop(var)),var[1]),diff(r(vop(var)),var[2]))),seq(var[i]=integrateRange[i],i=1..numelems(integrateRange)));
end proc:

tangielt:= proc(r::{procedure},integrateRange::{list},V::{procedure})
local var,i;
var := [op(1,eval(r))]:
int(prik(V(vop(r(var[1]))),diff(r(var[1]),var[1])),var[1]=integrateRange[1]);
end proc:

stokes:= proc(r::{procedure},integrateRange::{list},V::{procedure});
flux(r,integrateRange,rot(V));
end proc:

flowkurve:= proc(V::{procedure},starttid::{numeric}:=0,punkt::{list} := [1],evaluate:=false);
local i, var, funk, løs;
var := [op(1,eval(V))]:
funk := [seq(var[i](t),i=1..numelems(var))]:
løs := dsolve([seq(diff(funk[i],t)=V(vop(funk))[i],i=1..numelems(var)), if numelems(punkt) > 1 then seq(var[i](starttid)=punkt[i],i=1..numelems(var)) else end if]):
if (evaluate) then unapply(evalf(subs(løs,<seq(var[i](t),i=1..numelems(var))>)),[t]);
else unapply(subs(løs,<seq(var[i](t),i=1..numelems(var))>),[t]);
end if: end proc:

flowkurvesolve := proc(flow::{procedure},punkt::{list});
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

stamfelt:= proc(V::{procedure})
local var,i,j,u; var:=op(1,eval(V)):
kryds(<-x,-y,-z>,<seq(int(u*V(seq(var[j]*u,j=1..3))[i],u=0..1),i=1..3)>);
end proc:

funkana := proc(f::{procedure},r::{procedure}:=1)
local var,nabla,H,i,sol; var:=op(1,eval(f)):
if (r=1) then
   nabla := gradient(f):
   sol := [solve([seq(nabla(var)[i]=0,i=1..numelems([var]))])]:
   if (numelems(sol)>0) then
      H := hesse(f):
      sol, seq(LinearAlgebra[Eigenvalues](subs(sol[i],H(var))),i=1..numelems(sol));
   else
      "No solutions for stationary points";
   end if:
else
   local var2, sol2, afledt; var2 := op(1,eval(r)):
   afledt := diff(f(vop(r(var2))),var2):
   sol2 := [solve(afledt=0,var2)]:
   sol2, seq(subs(var2=sol2[i],r(var2)),i=1..numelems(sol2));
end if;
end proc;

paraplot := proc(r::{procedure},range::{list})
local var,i; var:=op(1,eval(r)):
if (numelems(range)=1) then
   if (numelems(r(var))=2) then
      plot([vop(r(var)),var=range[1]]); # Kurve i 2D
   else
      plot3d(r(var),var=range[1],orientation=[-55,75,0]) # Kurve i 3D
   end if:
elif (numelems(range)=2) then
   if (numelems(r(var))=2) then
      plot3d(<r(var),0>,var[1]=range[1],var[2]=range[2],orientation=[-90,0],lightmodel=none); # Plan i 2D
   else
      plot3d(r(var),var[1]=range[1],var[2]=range[2],orientation=[-55,75,0]); # Flade i 3D
   end if:
elif (numelems([var])=3) then 
   Integrator8[sideFlader](r,[seq(vop(convert(range[i],list)),i=1..3)],[8,8,8]); 
end if;
end proc;

massemidte := proc(r::procedure, range::list, f::procedure:=1)
local M, i, var,fweight; var:=op(1,eval(f)):
M := integrer(r,range,f):
if (numelems([var])>1) then 
   fweight:=unapply(f(var)*var[i],[var]); 
else 
   fweight:=unapply([x,y,z][i],[x,y,z])
end if;
<seq(integrer(r,range,fweight),i=1..3)> * 1/M;
end proc:

end module:
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

# !!!FORKLARING AF HVER KOMMANDO!!!
# Kommer senere...
# 
# Hej Hans. Tænker vi bare laver hjælpekommandoer i hver funktion?
# 
# 


# Brug af paraplot
#r1:=(u) -> <sin(u),u^2>,[0..6]:
#r2:=(u) -> <sin(u),sqrt(u),u>,[0..6]:
#r3:=(u,v) -> <u,exp(-u/3)*sin(u)*v>,[0..2*Pi,0..1]:
#r4:=(u,v) -> <u,exp(-u/3)*sin(u)*v,-cos(v)>,[0..4,0..1]:
#r5:=(u,v,w) -> <u*v*cos(w),u*v*sin(w),u^2*v>,[0..2,0..1,0..3/2*Pi]:
#paraplot(r1);paraplot(r2);paraplot(r3);paraplot(r4);paraplot(r5);


# Brug af massemidte
#r5:=(u,v,w) -> <u*v*cos(w),u*v*sin(w),u^2*v>,[0..2,0..1,0..3/2*Pi];
#f:=(x,y,z)-> x^2+y^2+z^2;
#massemidte(r5);
#with(plots):display(paraplot(r5),pointplot3d(massemidte(r5),symbol=solidsphere,symbolsize=20,color=green))










