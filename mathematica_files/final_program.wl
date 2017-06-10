(* ::Package:: *)

variables = Sort[Flatten[Table[{Subscript[\[Alpha], i,j], Subscript[\[Beta], i,j], Subscript[\[Gamma], i,j], Subscript[\[Sigma], i,j]}, {i, 1, 3}, {j, 1, 2}]]];
transformSubstitutions=Flatten[{Table[{Subscript[A, i] -> Subscript[a, i,1] + I * Subscript[a, i,2], Subscript[B, i] -> Subscript[b, i,1] + I * Subscript[b, i,2], Subscript[C, i] -> Subscript[c, i,1] + I * Subscript[c, i,2]}, {i,1,3}], Subscript[z, 1]->Subscript[x, 1]+I*Subscript[y, 1], Subscript[z, 2]->Subscript[x, 2]+I*Subscript[y, 2], w->u+I*v, Subscript[P, 1]->Subscript[p, 1,1]+I*Subscript[p, 1,2], Subscript[P, 2]->Subscript[p, 2,1]+I*Subscript[p, 2,2], q->Subscript[q, 1]+I*Subscript[q, 2]}];
parameterSubstitutions=Flatten[{Table[{Subscript[a, i,j] -> Subscript[a, i,j][t], Subscript[b, i,j] -> Subscript[b, i,j][t], Subscript[c, i,j] -> Subscript[c, i,j][t]}, {i, 1, 3}, {j, 1, 2}],Table[Subscript[p, i,j ]-> Subscript[p, i,j][t], {i, 1, 2}, {j, 1, 2}], Subscript[q, 1] -> Subscript[q, 1][t], Subscript[q, 2] -> Subscript[q, 2][t]}]; 
diffSubstitution=Flatten[{Table[{Subscript[a, i,j]'[0] -> Subscript[\[Alpha], i,j], Subscript[b, i,j]'[0] -> Subscript[\[Beta], i,j], Subscript[c, i,j]'[0] -> Subscript[\[Gamma], i,j]}, {i, 1, 3}, {j, 1, 2}], Table[Subscript[p, i,j]'[0] -> Subscript[\[Sigma], i,j], {i, 1, 2}, {j, 1, 2}], {Subscript[q, 1]'[0] -> Subscript[\[Sigma], 3,1], Subscript[q, 2]'[0] -> Subscript[\[Sigma], 3,2]}}];
Subscript[Z, 1][AT_]:=First@AT[[1]]
Subscript[Z, 2][AT_]:=First@AT[[2]]
W[AT_]:=First@AT[[3]]
CreateTransform[]:=
Module[{at},
at = ({{Subscript[A, 1],Subscript[A, 2],Subscript[A, 3]},{Subscript[B, 1],Subscript[B, 2],Subscript[B, 3]},{Subscript[C, 1],Subscript[C, 2],Subscript[C, 3]}}).
({{Subscript[z, 1]},{Subscript[z, 2]},{w}})+({{Subscript[P, 1]},{Subscript[P, 2]},{q}});
at = at/.transformSubstitutions;
Expand@at
]
(* \:041f\:0440\:0438\:043c\:0435\:043d\:044f\:0435\:0442 \:0430\:0444\:0444\:0438\:043d\:043d\:043e\:0435 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:0435 \:043a \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 *)
TransformSurface[surface_, transform_]:=
Module[{s = surface, st,tr = transform},
st = s /.{Subscript[x, 1]->ComplexExpand@Re@Subscript[Z, 1]@tr, Subscript[y, 1]->ComplexExpand@Im@Subscript[Z, 1]@tr,
	Subscript[x, 2]-> ComplexExpand@Re@Subscript[Z, 2]@tr, Subscript[y, 2]->ComplexExpand@Im@Subscript[Z, 2]@tr,
u->ComplexExpand@Re@W@tr,v->ComplexExpand@Im@W@tr};
st
]
GetSystem[surface_]:=
Module[{s=surface,system = {}, \[CapitalPhi]=Subtract@@surface,ts,vars={}},
vars ={Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v};
ts = TransformSurface[\[CapitalPhi], CreateTransform[]]/.parameterSubstitutions;
ts = D[ts, t]/.t->0/.diffSubstitution;
ts=Expand[(ts/.Solve[s,v][[1]])];
ts *= Denominator@Simplify@ts;
ts=Simplify@ts;
system= Times @@ (vars^#[[1]])->#[[2]]&/@CoefficientRules[ts, vars];
system =DeleteCases[system[[All, 2]],0];
system
];
(* \:041f\:0440\:0438\:0432\:043e\:0434\:0438\:0442 \:043c\:0430\:0442\:0440\:0438\:0446\:0443 \:043a \:0441\:0442\:0443\:043f\:0435\:043d\:0447\:0430\:0442\:043e\:043c\:0443 \:0432\:0438\:0434\:0443 \:0441 \:0443\:0447\:0435\:0442\:043e\:043c \:043f\:0440\:0435\:0434\:043f\:043e\:043b\:043e\:0436\:0435\:043d\:0438\:0439 *)
AdaptiveElmination[matrix_, variables_]:=
Module[{m=matrix,perms = {}, dim = Dimensions@matrix,
h = Dimensions@matrix[[1]], w = Dimensions@matrix[[2]],pos,i,
vars = Flatten@{variables},pattern},
pattern = Except[0,
_Integer|_?(Variables@# === vars&)];
For[i = 1,i < Min[w, h],i++,
pos=Flatten@Position[m[[i;;, i;;]], pattern, 2, 1];
If[pos === {}, Break[],pos +={i-1, i-1}];
m[[{i, pos[[1]]}]]=m[[{pos[[1]], i}]];
m[[All,{i, pos[[2]]}]]=m[[All, {pos[[2]],i}]];
m[[i+1;;]]=Factor@MatrixReduceRow[m, i];
];
m
];
(*  *)
GetInfinitesimalTransforms[system_]:=
Module[{s = system, ta={},vars = {}, basis = {}, sol, itm = {},subs = {}},
vars =Sort@Flatten@Table[{Subscript[\[Alpha], i,j], Subscript[\[Beta], i,j], Subscript[\[Gamma], i,j], Subscript[\[Sigma], i,j]}, {i, 1, 3}, {j, 1, 2}];
itm = {Append[Table[Subscript[\[Alpha], i,1]+I*Subscript[\[Alpha], i,2],{i,1,3}],Subscript[\[Sigma], 1,1]+I*Subscript[\[Sigma], 1,2]],Append[Table[Subscript[\[Beta], i,1]+I*Subscript[\[Beta], i,2],{i,1,3}],Subscript[\[Sigma], 2,1]+I*Subscript[\[Sigma], 2,2]],Append[Table[Subscript[\[Gamma], i,1]+I*Subscript[\[Gamma], i,2],{i,1,3}],Subscript[\[Sigma], 3,1]+I*Subscript[\[Sigma], 3,2]],
{0,0,0,0}};
sol = Solve[#1==0&/@s,vars];
ta=itm/.sol[[1]];
vars = Intersection[Variables@ta,vars];
subs=Sort@Flatten[{vars[[#]]->1,Function[e,e->0]/@Complement[vars,{vars[[#]]}]}]&/@(Range@@Dimensions@vars);
ta= ta/.#&/@subs;
ta
];
(* \:041f\:0435\:0447\:0430\:0442\:0430\:0435\:0442 \:043c\:0430\:0442\:0440\:0438\:0446\:0443 \:0441 \:043d\:0443\:043c\:0435\:0440\:0430\:0446\:0438\:0435\:0439 \:0441\:0442\:0440\:043e\:043a \:0438 \:0441\:0442\:043e\:043b\:0431\:0446\:043e\:0432 *)
PrintMatrix[matrix_] :=
Module[{m = matrix, dim=Dimensions@matrix},
MatrixForm[m, TableHeadings->{Range@dim[[1]], Range@dim[[2]]}]
]
(* \:041c\:0435\:043d\:044f\:0435\:0442 \:043c\:0435\:0441\:0442\:0430\:043c\:0438 \:0441\:0442\:043e\:043b\:0431\:0446\:044b \:0432 \:043c\:0430\:0442\:0440\:0438\:0446\:0435 *)
SwapRows[matrix_,from_List, to_List] := 
Module[{m = matrix, f = from, t=to},
m[[Flatten@{f,t}]] = m[[Flatten@{t,f}]];
m
];
(* \:041c\:0435\:043d\:044f\:0435\:0442 \:043c\:0435\:0441\:0442\:0430\:043c\:0438 \:0441\:0442\:043e\:043b\:0431\:0446\:044b \:0432 \:043c\:0430\:0442\:0440\:0438\:0446\:0435 *)
SwapColumns[matrix_,from_List, to_List] := 
Module[{m = matrix, f = from, t=to},
m[[All,Flatten@{f,t}]] = m[[All,Flatten@{t,f}]];
m
];
(* \:041f\:0440\:0438\:0432\:043e\:0434\:0438\:0442 \:0443\:043a\:0430\:0437\:0430\:043d\:043d\:044b\:0439 \:0441\:0442\:043e\:043b\:0431\:0435\:0446 \:043c\:0430\:0442\:0440\:0438\:0446\:044b \:043a \:043d\:0443\:043b\:0435\:0432\:043e\:0443 \:0432\:0438\:0434\:0443, \:043d\:0430\:0447\:0438\:043d\:0430\:044f \:0441\:043e \:0441\:0442\:0440\:043e\:043a\:0438 \:0441 \:043d\:043e\:043c\:0435\:0440\:043e\:043c row *)
MatrixReduceRow[matrix_, row_]:=
Module[{m =matrix, r = row},
m = # - #[[row]]*matrix[[row]]/matrix[[row,row]]&/@matrix[[row+1;;]];
m
]
IntegrateTransforms[transforms_List]:=
Module[{tr=transforms,affine={}},
affine=MatrixExp[t*#]&/@tr;
affine
];
CheckPreservation[surface_, transform_]:=
Module[{s = surface, t,ts},
t=transform.{{Subscript[x, 1]+I*Subscript[y, 1]},{Subscript[x, 2]+I*Subscript[y, 2]},{u+I*v},{1}};
ts=Subtract@@(FullSimplify@TransformSurface[s, t]);
NumberQ[FullSimplify[(Subtract@@s)/ts]]
];


S =v*(1+Subscript[x, 2]) ==Subscript[x, 1]^2+ (1+Subscript[x, 2])*(\[Mu]*Subscript[x, 2]^2+\[Lambda]*Subscript[x, 2]*Subscript[y, 2]+\[Nu]*Subscript[y, 2]^2);
system=GetSystem[S];
matrix =Normal@CoefficientArrays[system,variables][[2]];
Print["\:041a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:043e \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0439 \:0432 \:0441\:0438\:0441\:0442\:0435\:043c\:0435: ", Length@system];
Print["\:041c\:0430\:043a\:0441\:0438\:043c\:0430\:043b\:044c\:043d\:044b\:0439 \:0440\:0430\:043d\:0433 \:043c\:0430\:0442\:0440\:0438\:0446\:044b: ",MatrixRank@matrix];
ITs = GetInfinitesimalTransforms[system];
Print["\:0420\:0430\:0437\:043c\:0435\:0440\:043d\:043e\:0441\:0442\:044c \:0433\:0440\:0443\:043f\:043f\:044b: ", Length@ITs];
Print@"\:0418\:043d\:0444\:0438\:043d\:0438\:0442\:0435\:0437\:0438\:043c\:0430\:043b\:044c\:043d\:044b\:0435 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044f:";
PrintMatrix/@ITs
groups=IntegrateTransforms@ITs;
Print@"\:041e\:0434\:043d\:043e\:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0438\:0447\:0435\:0441\:043a\:0438\:0435 \:0433\:0440\:0443\:043f\:043f\:044b:"
PrintMatrix/@FullSimplify@groups
CheckPreservation[S,#]&/@groups



