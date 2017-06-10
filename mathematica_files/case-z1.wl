(* ::Package:: *)

(* \:041e\:0447\:0438\:0441\:0442\:0438\:0442\:044c \:0432\:0441\:0435 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0435 *)
Unprotect["`*"]; 
ClearAll["`*"];
(* \:041d\:0430\:043a\:043b\:0430\:0434\:044b\:0432\:0430\:0435\:043c \:043f\:0440\:0435\:0434\:043f\:043e\:043b\:043e\:0436\:0435\:043d\:0438\:044f, \:0447\:0442\:043e \:0438\:0441\:043f\:043e\:043b\:044c\:0437\:0443\:0435\:043c\:044b\:0435 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0435 -- \:0434\:0435\:0439\:0441\:0442\:0432\:0438\:0442\:0435\:043b\:044c\:043d\:044b\:0435 *)
$Assumptions=Flatten[Join[{\[Epsilon]\[Element]Reals,Subscript[x, 1]\[Element]Reals, Subscript[x, 2]\[Element]Reals, Subscript[y, 1]\[Element]Reals, Subscript[y, 2]\[Element]Reals, u\[Element]Reals, v\[Element]Reals, Subscript[p, 1,1][t]\[Element]Reals,Subscript[p, 1,2][t]\[Element]Reals, Subscript[p, 2,1][t]\[Element]Reals, Subscript[p, 2,2][t]\[Element]Reals, Subscript[q, 1][t]\[Element]Reals, Subscript[q, 2][t]\[Element]Reals, Subscript[p, 1,1]\[Element]Reals, Subscript[p, 1,2]\[Element]Reals, Subscript[p, 2,1]\[Element]Reals, Subscript[p, 2,2]\[Element]Reals, Subscript[q, 1]\[Element]Reals, Subscript[q, 2]\[Element]Reals, t\[Element]Reals},Table[{Subscript[a, i,j][t]\[Element]Reals, Subscript[b, i,j][t]\[Element]Reals,Subscript[c, i,j][t]\[Element]Reals,Subscript[a, i,j]\[Element]Reals, Subscript[b, i,j]\[Element]Reals,Subscript[c, i,j]\[Element]Reals},{i,1,3},{j,1,2}],Table[{Subscript[k, i]\[Element]Reals},{i,1,10}]]];
Subscript[a, 1,1][0]=Subscript[b, 2,1][0]=Subscript[c, 3,1][0]=1;
Subscript[a, 1,2][0]=Subscript[a, 2,1][0]=Subscript[a, 2,2][0]=Subscript[a, 3,1][0]=Subscript[a, 3,2][0]=Subscript[b, 1,1][0]=Subscript[b, 1,2][0]=Subscript[b, 2,2][0]=Subscript[b, 3,1][0]=Subscript[b, 3,2][0]=Subscript[c, 1,1][0]=Subscript[c, 1,2][0]=Subscript[c, 2,1][0]=Subscript[c, 2,2][0]=Subscript[c, 3,2][0]=Subscript[p, 1,1][0]=Subscript[p, 1,2][0]=Subscript[p, 2,1][0]=Subscript[p, 2,2][0]=Subscript[q, 1][0]=Subscript[q, 2][0]=0;
(* \:0417\:0430\:043c\:0435\:043d\:044b \:0432 \:0438\:0441\:0445\:043e\:0434\:043d\:043e\:043c \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:0438 *)
Subscript[Z, 1][AT_]:=First@AT[[1]]
Subscript[Z, 2][AT_]:=First@AT[[2]]
W[AT_]:=First@AT[[3]]
transformSubstitutions=Flatten[{Table[{Subscript[A, i] -> Subscript[a, i,1] + I * Subscript[a, i,2], Subscript[B, i] -> Subscript[b, i,1] + I * Subscript[b, i,2], Subscript[C, i] -> Subscript[c, i,1] + I * Subscript[c, i,2]}, {i,1,3}], Subscript[z, 1]->Subscript[x, 1]+I*Subscript[y, 1], Subscript[z, 2]->Subscript[x, 2]+I*Subscript[y, 2], w->u+I*v, Subscript[P, 1]->Subscript[p, 1,1]+I*Subscript[p, 1,2], Subscript[P, 2]->Subscript[p, 2,1]+I*Subscript[p, 2,2], Q->Subscript[q, 1]+I*Subscript[q, 2]}];
(* \:041f\:0435\:0440\:0435\:0445\:043e\:0434 \:043e\:0442 \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:043e\:0432 \:043a \:0444\:0443\:043d\:043a\:0446\:0438\:044f\:043c \:043e\:0442 \:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0430 t *)
parameterSubstitutions=Flatten[{Table[{Subscript[a, i,j] -> Subscript[a, i,j][t], Subscript[b, i,j] -> Subscript[b, i,j][t], Subscript[c, i,j] -> Subscript[c, i,j][t]}, {i, 1, 3}, {j, 1, 2}],Table[Subscript[p, i,j ]-> Subscript[p, i,j][t], {i, 1, 2}, {j, 1, 2}], Subscript[q, 1] -> Subscript[q, 1][t], Subscript[q, 2] -> Subscript[q, 2][t]}]; 
(* \:0417\:0430\:043c\:0435\:043d\:0430 \:043f\:0440\:043e\:0438\:0437\:0432\:043e\:0434\:043d\:044b\:0445 \:0432 \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 *)
diffSubstitution=Flatten[{Table[{Subscript[a, i,j]'[0] -> Subscript[\[Alpha], i,j], Subscript[b, i,j]'[0] -> Subscript[\[Beta], i,j], Subscript[c, i,j]'[0] -> Subscript[\[Gamma], i,j]}, {i, 1, 3}, {j, 1, 2}], Table[Subscript[p, i,j]'[0] -> Subscript[\[Sigma], i,j], {i, 1, 2}, {j, 1, 2}], {Subscript[q, 1]'[0] -> Subscript[\[Sigma], 3,1], Subscript[q, 2]'[0] -> Subscript[\[Sigma], 3,2]}}];
(* \:041e\:0442\:0441\:043e\:0440\:0442\:0438\:0440\:043e\:0432\:0430\:043d\:043d\:044b\:0439 \:0441\:043f\:0438\:0441\:043e\:043a \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0445 *)
variables = Sort[Flatten[Table[{Subscript[\[Alpha], i,j], Subscript[\[Beta], i,j], Subscript[\[Gamma], i,j], Subscript[\[Sigma], i,j]}, {i, 1, 3}, {j, 1, 2}]]];
(* \:0412\:044b\:0432\:043e\:0434\:0438\:0442 \:043c\:0430\:0442\:0440\:0438\:0446\:0443 \:0441 \:043f\:0440\:043e\:043d\:0443\:043c\:0435\:0440\:043e\:0432\:0430\:043d\:043d\:044b\:043c\:0438 \:0441\:0442\:0440\:043e\:043a\:0430\:043c\:0438 \:0438 \:0441\:0442\:043e\:043b\:0431\:0446\:0430\:043c\:0438 *)
PrintMatrix[matr_] := MatrixForm[matr, TableHeadings->{Table[i, {i, 1, Dimensions[matr][[1]]}], Table[i, {i, 1, Dimensions[matr][[2]]}]}];
(* \:0421\:0447\:0438\:0442\:0430\:0435\:0442 \:0447\:0438\:0441\:043b\:043e \:0441\:043b\:0430\:0433\:0430\:0435\:043c\:044b\:0445 *)
Nops[expr_] := If[Head[Expand@expr] === Plus, Length[Expand@expr], If[Expand@expr === 0, 0, 1]]
ColumnReduce[matrix_,col_]:=Simplify[#*matrix[[col, col]]-matrix[[col]]*#[[col]]]&/@matrix[[col+1;;]];
(* \:041a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:043e \:043c\:0438\:043d\:043e\:0440\:043e\:0432 \:0432 \:043c\:0430\:0442\:0440\:0438\:0446\:0435 *)
MinorsCount[matr_, ord_] := Binomial[Dimensions[matr][[1]], ord] * Binomial[Dimensions[matr][[2]], ord]
(* \:0423\:0440\:0430\:0432\:0435\:043d\:043d\:0435\:043d\:0438\:0435 \:043f\:043e\:0432\:0435\:0445\:043d\:043e\:0441\:0442\:0438 *)
quardaticForm= Q -> (Subscript[k, 1]*
\!\(\*SubsuperscriptBox[\(x\), \(1\), \(\(2\)\(\ \)\)]\)+ Subscript[k, 2]*Subscript[x, 1]*Subscript[x, 2] + Subscript[k, 3]*
\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\) + Subscript[k, 4]*Subscript[x, 1]*Subscript[y, 1] + Subscript[k, 5]*Subscript[x, 2]*Subscript[y, 1] + Subscript[k, 6]*
\!\(\*SubsuperscriptBox[\(y\), \(1\), \(2\)]\) + Subscript[k, 7]*Subscript[x, 1]*Subscript[y, 2] + Subscript[k, 8]*Subscript[x, 2]*Subscript[y, 2] + Subscript[k, 9]*Subscript[y, 1]*Subscript[y, 2] + Subscript[k, 10]*
\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\));
additionalSubstitutions = {Subscript[k, 1]->1,Subscript[k, 2]->0,Subscript[k, 3]->0};
S = v*(1+Subscript[x, 2]) == Subscript[k, 1]*Subscript[x, 1]^2+ Subscript[k, 2]*Subscript[x, 1]*Subscript[y, 1] + Subscript[k, 3]*Subscript[y, 1]^2+ (1+Subscript[x, 2])*(\[Mu]*Subscript[x, 2]^2+\[Lambda]*Subscript[x, 2]*Subscript[y, 2]+\[Nu]*Subscript[y, 2]^2) /. quardaticForm /. additionalSubstitutions;
\[CapitalPhi] = v*(1+Subscript[x, 2]) - Subscript[k, 1]*Subscript[x, 1]^2- Subscript[k, 2]*Subscript[x, 1]*Subscript[y, 1] - Subscript[k, 3]*Subscript[y, 1]^2- (1+Subscript[x, 2])*(\[Mu]*Subscript[x, 2]^2+\[Lambda]*Subscript[x, 2]*Subscript[y, 2]+\[Nu]*Subscript[y, 2]^2) /. quardaticForm /. additionalSubstitutions;
TraditionalForm@S
TraditionalForm@\[CapitalPhi]


(* \:0410\:0444\:0444\:0438\:043d\:043d\:043e\:0435 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:0435 *)
AT=({
 {Subscript[A, 1], Subscript[A, 2], Subscript[A, 3]},
 {Subscript[B, 1], Subscript[B, 2], Subscript[B, 3]},
 {Subscript[C, 1], Subscript[C, 2], Subscript[C, 3]}
}).({
 {Subscript[z, 1]},
 {Subscript[z, 2]},
 {w}
})+({
 {Subscript[P, 1]},
 {Subscript[P, 2]},
 {Q}
}) /.transformSubstitutions;
MatrixForm@Expand@AT
(* \:041f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:043d\:0430\:044f \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:044c *)
ST=\[CapitalPhi]/.{Subscript[x, 1]->ComplexExpand@Re@Subscript[Z, 1]@AT, Subscript[y, 1]->ComplexExpand@Im@Subscript[Z, 1]@AT, Subscript[x, 2]->ComplexExpand@Re@Subscript[Z, 2]@AT, Subscript[y, 2]->ComplexExpand@Im@Subscript[Z, 2]@AT, u->ComplexExpand@Re@W@AT, v->ComplexExpand@Im@W@AT};
(* \:041f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:044c, \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:044b \:0437\:0430\:0432\:0438\:0441\:044f\:0442 \:043e\:0442 \:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0430 t *)
STP=ST/.parameterSubstitutions;
(* \:0414\:0438\:0444\:0444\:0435\:0440\:0435\:043d\:0446\:0438\:0440\:0443\:0435\:043c \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:044c \:043f\:043e \:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0443 t \:0432 \:0442\:043e\:0447\:043a\:0435 Id, \:0447\:0442\:043e\:0431\:044b \:043f\:0435\:0440\:0435\:0439\:0442\:0438 \:043a \:0438\:043d\:0444\:0438\:043d\:0438\:0442\:0435\:0437\:0438\:043c\:0430\:043b\:044c\:043d\:043e\:043c\:0443 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044e *)
SIT=(D[STP, t]/.t->0/.diffSubstitution);
TeXForm@SIT
(* \:0422\:0435\:043f\:0435\:0440\:044c \:043f\:043e\:043b\:0443\:0447\:0435\:043d\:043d\:043e\:0435 \:0432\:0435\:043a\:0442\:043e\:0440\:043d\:043e\:0435 \:043f\:043e\:043b\:0435 \:0440\:0430\:0441\:0441\:043c\:043e\:0442\:0440\:0438\:043c \:043d\:0430 \:0438\:0441\:0445\:043e\:0434\:043d\:043e\:0439 \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 *)
VFS=Expand[FullSimplify[(SIT/.Solve[S,v][[1]])*(1+Subscript[x, 2])^2]]
(* \:041e\:0441\:043d\:043e\:0432\:043d\:043e\:0435 \:0442\:043e\:0436\:0434\:0435\:0441\:0442\:0432\:043e \:0433\:043b\:0430\:0441\:0438\:0442, \:0447\:0442\:043e \:0432\:0435\:043a\:0442\:043e\:0440\:043d\:043e\:0435 \:043f\:043e\:043b\:0435 \:043d\:0430 \:0438\:0441\:0445\:043e\:0434\:043d\:043e\:0439 \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 \:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c \:0442\:043e\:0436\:0434\:0441\:0442\:0432\:0435\:043d\:043d\:043e \:0440\:0430\:0432\:043d\:043e \:043d\:0443\:043b\:044e. \:0421\:043b\:0435\:0434\:0443\:044f \:043b\:0435\:043c\:043c\:0435 \:043e \:0435\:0434\:0438\:043d\:0441\:0442\:0432\:0435\:043d\:043d\:043e\:0441\:0442\:0438, \:0432\:0441\:0435 \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:044b \:043f\:0440\:0438 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0445 Subscript[x, 1], Subscript[x, 2], Subscript[y, 1], Subscript[y, 2], u \:0438 v \:0434\:043e\:043b\:0436\:043d\:044b \:0431\:044b\:0442\:044c \:0440\:0430\:0432\:043d\:044b \:043d\:0443\:043b\:044e. \:0421\:043e\:0441\:0442\:0430\:0432\:0438\:043c \:0441\:0438\:0441\:0442\:0435\:043c\:0443 \:043b\:0438\:043d\:0435\:0439\:043d\:044b\:0445 \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0439 \:043e\:0442\:043d\:043e\:0441\:0438\:0442\:0435\:043b\:044c\:043d\:043e "\:0433\:0440\:0435\:0447\:0435\:0441\:043a\:0438\:0445" \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:043e\:0432 -- \:044d\:043b\:0435\:043c\:0435\:043d\:0442\:043e\:0432 \:0438\:043d\:0444\:0438\:043d\:0438\:0442\:0435\:0437\:0438\:043c\:0430\:043b\:044c\:043d\:043e\:0433\:043e \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044f (\:043f\:0440\:043e\:0438\:0437\:0432\:043e\:0434\:043d\:044b\:0445 \:0432 \:0442\:043e\:0447\:043a\:0435 \:043d\:043e\:043b\:044c) *)
varsToCoeffs= Times @@ ({Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}^#[[1]])->#[[2]]&/@CoefficientRules[VFS, {Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}];
reducedSystem=DeleteCases[varsToCoeffs[[All, 2]],0];
Print["\:041a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:043e \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0439: ",Length@reducedSystem]
Column@Factor@reducedSystem
Print["\:041f\:0440\:043e\:0441\:0442\:044b\:0435 \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:044f:"];
Column@Simplify@Select[reducedSystem, Nops[#]<=2&]
(* \:041c\:0430\:0442\:0440\:0438\:0446\:0430 \:044d\:0442\:043e\:0439 \:0441\:0438\:0441\:0442\:0435\:043c\:044b *)
(*matrix = Function[first, Function[second, Coefficient[first,second]]/@ variables]/@reducedSystem;*)
matrix =Normal@CoefficientArrays[reducedSystem,variables][[2]];
Print["\:041c\:0430\:043a\:0441\:0438\:043c\:0430\:043b\:044c\:043d\:044b\:0439 \:0440\:0430\:043d\:0433 \:043c\:0430\:0442\:0440\:0438\:0446\:044b: ",MatrixRank[matrix]]
PrintMatrix@matrix


MatrixRank@matrix
simplifiedMatrix = AdaptiveElmination[matrix,{Subscript[k, 3]}];
PrintMatrix@Factor@simplifiedMatrix;
simplifiedMatrix=Select[simplifiedMatrix,#=!=Table[0,{i,1,24}]&];
PrintMatrix@simplifiedMatrix;
sm = simplifiedMatrix[[18;;,18;;]];
PrintMatrix@AdaptiveElmination[sm,{\[Lambda]}]
PrintMatrix@AdaptiveElmination[sm,{\[Mu]}]
PrintMatrix@AdaptiveElmination[sm,{\[Nu]}]
PrintMatrix@Factor@sm


newSystem=Flatten@Append[#1==0&/@reducedSystem, {\[Mu]!=-\[Nu]}];

Column@Simplify@newSystem


sol = Solve[newSystem, variables]


MM=({
 {Subscript[\[Alpha], 1,1]+I*Subscript[\[Alpha], 1,2], Subscript[\[Alpha], 2,1]+I*Subscript[\[Alpha], 2,2], Subscript[\[Alpha], 3,1]+I*Subscript[\[Alpha], 3,2], Subscript[\[Sigma], 1,1]+I*Subscript[\[Sigma], 1,2]},
 {Subscript[\[Beta], 1,1]+I*Subscript[\[Beta], 1,2], Subscript[\[Beta], 2,1]+I*Subscript[\[Beta], 2,2], Subscript[\[Beta], 3,1]+I*Subscript[\[Beta], 3,2], Subscript[\[Sigma], 2,1]+I*Subscript[\[Sigma], 2,2]},
 {Subscript[\[Gamma], 1,1]+I*Subscript[\[Gamma], 1,2], Subscript[\[Gamma], 2,1]+I*Subscript[\[Gamma], 2,2], Subscript[\[Gamma], 3,1]+I*Subscript[\[Gamma], 3,2], Subscript[\[Sigma], 3,1]+I*Subscript[\[Sigma], 3,2]},
 {0, 0, 0, 0}
})/.sol[[1]];
PrintMatrix@Simplify@MM


Subscript[IT, 1]=MM/.{Subscript[\[Beta], 2,1]->1,Subscript[\[Alpha], 2,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 2,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 2]=MM/.{Subscript[\[Beta], 2,1]->0,Subscript[\[Alpha], 2,1]->1,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 2,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 3]=MM/.{Subscript[\[Beta], 2,1]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Sigma], 1,2]->1,Subscript[\[Sigma], 2,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 4]=MM/.{Subscript[\[Beta], 2,1]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 2,2]->1,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 5]=MM/.{Subscript[\[Beta], 2,1]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 2,2]->0,Subscript[\[Sigma], 3,1]->1};
PrintMatrix/@(FullSimplify@Subscript[IT, #]&/@Range@5)
(*v Subscript[x, 2]\[LongEqual]k Subsuperscript[x, 1, 2]+k Subsuperscript[y, 1, 2]+Subscript[x, 2] (\[Mu] Subsuperscript[x, 2, 2]+\[Nu] Subsuperscript[y, 2, 2])*)


exps=FullSimplify[MatrixExp[Subscript[IT, #]*t]&/@Range@5];
PrintMatrix/@exps



