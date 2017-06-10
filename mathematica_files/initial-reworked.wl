(* ::Package:: *)

(* \:041e\:0447\:0438\:0441\:0442\:0438\:0442\:044c \:0432\:0441\:0435 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0435 *)
Unprotect["`*"]; 
ClearAll["`*"];
(* \:041d\:0430\:043a\:043b\:0430\:0434\:044b\:0432\:0430\:0435\:043c \:043f\:0440\:0435\:0434\:043f\:043e\:043b\:043e\:0436\:0435\:043d\:0438\:044f, \:0447\:0442\:043e \:0438\:0441\:043f\:043e\:043b\:044c\:0437\:0443\:0435\:043c\:044b\:0435 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0435 -- \:0434\:0435\:0439\:0441\:0442\:0432\:0438\:0442\:0435\:043b\:044c\:043d\:044b\:0435 *)
$Assumptions=Flatten[Join[{Subscript[x, 1]\[Element]Reals, Subscript[x, 2]\[Element]Reals, Subscript[y, 1]\[Element]Reals, Subscript[y, 2]\[Element]Reals, u\[Element]Reals, v\[Element]Reals, Subscript[p, 1,1][t]\[Element]Reals,Subscript[p, 1,2][t]\[Element]Reals, Subscript[p, 2,1][t]\[Element]Reals, Subscript[p, 2,2][t]\[Element]Reals, Subscript[q, 1][t]\[Element]Reals, Subscript[q, 2][t]\[Element]Reals, Subscript[p, 1,1]\[Element]Reals, Subscript[p, 1,2]\[Element]Reals, Subscript[p, 2,1]\[Element]Reals, Subscript[p, 2,2]\[Element]Reals, Subscript[q, 1]\[Element]Reals, Subscript[q, 2]\[Element]Reals, t\[Element]Reals},Table[{Subscript[a, i,j][t]\[Element]Reals, Subscript[b, i,j][t]\[Element]Reals,Subscript[c, i,j][t]\[Element]Reals,Subscript[a, i,j]\[Element]Reals, Subscript[b, i,j]\[Element]Reals,Subscript[c, i,j]\[Element]Reals},{i,1,3},{j,1,2}],Table[{Subscript[k, i]\[Element]Reals},{i,1,3}]]];
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
MatrixReduceRow[matrix_, row_]:=# - #[[row]]*matrix[[row]]/matrix[[row,row]]&/@matrix[[row+1;;]]
ColumnReduce[matrix_,col_]:=Simplify[#*matrix[[col, col]]-matrix[[col]]*#[[col]]]&/@matrix[[col+1;;]];
(* \:041a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:043e \:043c\:0438\:043d\:043e\:0440\:043e\:0432 \:0432 \:043c\:0430\:0442\:0440\:0438\:0446\:0435 *)
MinorsCount[matr_, ord_] := Binomial[Dimensions[matr][[1]], ord] * Binomial[Dimensions[matr][[2]], ord]
(* \:0423\:0440\:0430\:0432\:0435\:043d\:043d\:0435\:043d\:0438\:0435 \:043f\:043e\:0432\:0435\:0445\:043d\:043e\:0441\:0442\:0438 *)
quardaticForm= Q -> (Subscript[k, 1]*
\!\(\*SubsuperscriptBox[\(x\), \(1\), \(\(2\)\(\ \)\)]\)+ Subscript[k, 2]*Subscript[x, 1]*Subscript[x, 2] + Subscript[k, 3]*
\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\) + Subscript[k, 4]*Subscript[x, 1]*Subscript[y, 1] + Subscript[k, 5]*Subscript[x, 2]*Subscript[y, 1] + Subscript[k, 6]*
\!\(\*SubsuperscriptBox[\(y\), \(1\), \(2\)]\) + Subscript[k, 7]*Subscript[x, 1]*Subscript[y, 2] + Subscript[k, 8]*Subscript[x, 2]*Subscript[y, 2] + Subscript[k, 9]*Subscript[y, 1]*Subscript[y, 2] + Subscript[k, 10]*
\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\));
additionalSubstitutions = {};
S = v*Subscript[x, 2] + Q == Subscript[x, 2]*(\[Mu]*Subscript[x, 2]^2+\[Nu]*Subscript[y, 2]^2) /. quardaticForm /. additionalSubstitutions;
TraditionalForm@S


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
ST=S/.{Subscript[x, 1]->FullSimplify@Re@Subscript[Z, 1]@AT, Subscript[y, 1]->FullSimplify@Im@Subscript[Z, 1]@AT, Subscript[x, 2]->FullSimplify@Re@Subscript[Z, 2]@AT, Subscript[y, 2]->FullSimplify@Im@Subscript[Z, 2]@AT, u->FullSimplify@Re@W@AT, v->FullSimplify@Im@W@AT};
(* \:041f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:044c, \:0432 \:043a\:043e\:0442\:043e\:0440\:043e\:0439 \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:044b \:0437\:0430\:0432\:0438\:0441\:044f\:0442 \:043e\:0442 \:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0430 t *)
STP=ST/.parameterSubstitutions
(* \:0414\:0438\:0444\:0444\:0435\:0440\:0435\:043d\:0446\:0438\:0440\:0443\:0435\:043c \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:044c \:043f\:043e \:043f\:0430\:0440\:0430\:043c\:0435\:0442\:0440\:0443 t \:0432 \:0442\:043e\:0447\:043a\:0435 Id, \:0447\:0442\:043e\:0431\:044b \:043f\:0435\:0440\:0435\:0439\:0442\:0438 \:043a \:0438\:043d\:0444\:0438\:043d\:0438\:0442\:0435\:0437\:0438\:043c\:0430\:043b\:044c\:043d\:043e\:043c\:0443 \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044e *)
SIT=(Subtract@@D[STP, t]/.t->0/.diffSubstitution);
(* \:0422\:0435\:043f\:0435\:0440\:044c \:043f\:043e\:043b\:0443\:0447\:0435\:043d\:043d\:043e\:0435 \:0432\:0435\:043a\:0442\:043e\:0440\:043d\:043e\:0435 \:043f\:043e\:043b\:0435 \:0440\:0430\:0441\:0441\:043c\:043e\:0442\:0440\:0438\:043c \:043d\:0430 \:0438\:0441\:0445\:043e\:0434\:043d\:043e\:0439 \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 *)
VFS=Expand[(SIT/.Solve[S,v][[1]])*Subscript[x, 2]^2];
(* \:041e\:0441\:043d\:043e\:0432\:043d\:043e\:0435 \:0442\:043e\:0436\:0434\:0435\:0441\:0442\:0432\:043e \:0433\:043b\:0430\:0441\:0438\:0442, \:0447\:0442\:043e \:0432\:0435\:043a\:0442\:043e\:0440\:043d\:043e\:0435 \:043f\:043e\:043b\:0435 \:043d\:0430 \:0438\:0441\:0445\:043e\:0434\:043d\:043e\:0439 \:043f\:043e\:0432\:0435\:0440\:0445\:043d\:043e\:0441\:0442\:0438 \:0434\:043e\:043b\:0436\:043d\:043e \:0431\:044b\:0442\:044c \:0442\:043e\:0436\:0434\:0441\:0442\:0432\:0435\:043d\:043d\:043e \:0440\:0430\:0432\:043d\:043e \:043d\:0443\:043b\:044e. \:0421\:043b\:0435\:0434\:0443\:044f \:043b\:0435\:043c\:043c\:0435 \:043e \:0435\:0434\:0438\:043d\:0441\:0442\:0432\:0435\:043d\:043d\:043e\:0441\:0442\:0438, \:0432\:0441\:0435 \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:044b \:043f\:0440\:0438 \:043f\:0435\:0440\:0435\:043c\:0435\:043d\:043d\:044b\:0445 Subscript[x, 1], Subscript[x, 2], Subscript[y, 1], Subscript[y, 2], u \:0438 v \:0434\:043e\:043b\:0436\:043d\:044b \:0431\:044b\:0442\:044c \:0440\:0430\:0432\:043d\:044b \:043d\:0443\:043b\:044e. \:0421\:043e\:0441\:0442\:0430\:0432\:0438\:043c \:0441\:0438\:0441\:0442\:0435\:043c\:0443 \:043b\:0438\:043d\:0435\:0439\:043d\:044b\:0445 \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0439 \:043e\:0442\:043d\:043e\:0441\:0438\:0442\:0435\:043b\:044c\:043d\:043e "\:0433\:0440\:0435\:0447\:0435\:0441\:043a\:0438\:0445" \:043a\:043e\:044d\:0444\:0444\:0438\:0446\:0438\:0435\:043d\:0442\:043e\:0432 -- \:044d\:043b\:0435\:043c\:0435\:043d\:0442\:043e\:0432 \:0438\:043d\:0444\:0438\:043d\:0438\:0442\:0435\:0437\:0438\:043c\:0430\:043b\:044c\:043d\:043e\:0433\:043e \:043f\:0440\:0435\:043e\:0431\:0440\:0430\:0437\:043e\:0432\:0430\:043d\:0438\:044f (\:043f\:0440\:043e\:0438\:0437\:0432\:043e\:0434\:043d\:044b\:0445 \:0432 \:0442\:043e\:0447\:043a\:0435 \:043d\:043e\:043b\:044c) *)
varsToCoeffs= Times @@ ({Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}^#[[1]])->#[[2]]&/@CoefficientRules[VFS, {Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}];
Column@varsToCoeffs
reducedSystem=DeleteCases[varsToCoeffs[[All, 2]]/.{},0];
Print["\:041a\:043e\:043b\:0438\:0447\:0435\:0441\:0442\:0432\:043e \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:0439: ",Length@reducedSystem]
Column@Factor@reducedSystem
Print["\:041f\:0440\:043e\:0441\:0442\:044b\:0435 \:0443\:0440\:0430\:0432\:043d\:0435\:043d\:0438\:044f:"];
Column@Select[reducedSystem, Nops[#]==1&]
(* \:041c\:0430\:0442\:0440\:0438\:0446\:0430 \:044d\:0442\:043e\:0439 \:0441\:0438\:0441\:0442\:0435\:043c\:044b *)
matrix = Function[first, Function[second, Coefficient[first,second]]/@ variables]/@reducedSystem;
Print["\:041c\:0430\:043a\:0441\:0438\:043c\:0430\:043b\:044c\:043d\:044b\:0439 \:0440\:0430\:043d\:0433 \:043c\:0430\:0442\:0440\:0438\:0446\:044b: ",MatrixRank[matrix]]
PrintMatrix@Factor@matrix


(* ::Input:: *)
(*(* \:041a\:043e\:043f\:0438\:0440\:0443\:0435\:043c \:043c\:0430\:0442\:0440\:0438\:0446\:0443, \:0447\:0442\:043e\:0431\:044b \:0441\:043e\:0445\:0440\:0430\:043d\:0438\:0442\:044c \:0438\:0441\:0445\:043e\:0434\:043d\:0443\:044e *)*)
(*simplifiedMatrix=matrix[[1;;,1;;]]/.{};*)
(*simplifiedMatrix[[All,Flatten@{Range[7],9,13,14,15,16,18,24}]]=simplifiedMatrix[[All,Flatten@{9,13,14,15,16,18,24,Range[7]}]];*)
(*simplifiedMatrix[[Flatten@{{Range[5],7},20,19,6,21,18,23}]]=simplifiedMatrix[[Flatten@{20,19,6,21,18,23,{Range[5],7}}]];*)
(*simplifiedMatrix[[{6,22}]]=simplifiedMatrix[[{22,6}]];*)
(*simplifiedMatrix[[2;;]]=MatrixReduceRow[simplifiedMatrix, 1];*)
(*simplifiedMatrix[[All,{10,8}]]=simplifiedMatrix[[All,{8,10}]];*)
(*simplifiedMatrix[[{8,36}]]=simplifiedMatrix[[{36,8}]];*)
(*simplifiedMatrix[[9;;]]=MatrixReduceRow[simplifiedMatrix, 8];*)
(*simplifiedMatrix[[All,{22,9}]]=simplifiedMatrix[[All,{9,22}]];*)
(*simplifiedMatrix[[{9,32}]]=simplifiedMatrix[[{32,9}]];*)
(*simplifiedMatrix[[10;;]]=MatrixReduceRow[simplifiedMatrix, 9];*)
(*simplifiedMatrix[[All,{17,10}]]=simplifiedMatrix[[All,{10,17}]];*)
(*simplifiedMatrix[[{10,30}]]=simplifiedMatrix[[{30,10}]];*)
(*simplifiedMatrix[[11;;]]=MatrixReduceRow[simplifiedMatrix, 10];*)
(*PrintMatrix@Factor@simplifiedMatrix*)


(* ::Input:: *)
(*	*)


(* ::Input:: *)
(*smallMatrix=simplifiedMatrix[[9;;,9;;]];*)
(*MatrixRank@smallMatrix*)
(*verySmallMatrix = Transpose@DeleteCases[Transpose@smallMatrix, {0..},Infinity];*)
(*PrintMatrix@verySmallMatrix*)


(* ::Input:: *)
(*(*Export[FileNameJoin@{NotebookDirectory[],"minors_init_"<>ToString@#1<>".wdx"},DeleteCases[Simplify@Flatten@Minors[verySmallMatrix, #1],0]]&/@Range[1,10]*)*)


(* ::Input:: *)
(*test=Transpose@DeleteCases[Transpose@matrix, {0..},Infinity];*)
(*PrintMatrix@test*)


newSystem=Flatten@Append[#1==0&/@reducedSystem, {\[Mu]!=0,\[Nu]!=0, Subscript[k, 10]!=0}];

Column@Simplify@Drop[newSystem, {2,6}]/.Subscript[\[Beta], 2,1]->Subscript[\[Gamma], 3,1]


sol=Solve[newSystem, variables]


MM=({
 {Subscript[\[Alpha], 1,1]+I*Subscript[\[Alpha], 1,2], Subscript[\[Alpha], 2,1]+I*Subscript[\[Alpha], 2,2], Subscript[\[Alpha], 3,1]+I*Subscript[\[Alpha], 3,2], Subscript[\[Sigma], 1,1]+I*Subscript[\[Sigma], 1,2]},
 {Subscript[\[Beta], 1,1]+I*Subscript[\[Beta], 1,2], Subscript[\[Beta], 2,1]+I*Subscript[\[Beta], 2,2], Subscript[\[Beta], 3,1]+I*Subscript[\[Beta], 3,2], Subscript[\[Sigma], 2,1]+I*Subscript[\[Sigma], 2,2]},
 {Subscript[\[Gamma], 1,1]+I*Subscript[\[Gamma], 1,2], Subscript[\[Gamma], 2,1]+I*Subscript[\[Gamma], 2,2], Subscript[\[Gamma], 3,1]+I*Subscript[\[Gamma], 3,2], Subscript[\[Sigma], 3,1]+I*Subscript[\[Sigma], 3,2]},
 {0, 0, 0, 0}
})/.sol[[1]]/.{Subscript[\[Beta], 1,1]->0,Subscript[\[Beta], 1,2]->0,Subscript[\[Beta], 3,1]->0,Subscript[\[Beta], 3,2]->0,Subscript[\[Sigma], 2,1]->0, Subscript[\[Sigma], 2,2]->0,Subscript[\[Beta], 2,2]->0};
PrintMatrix@Factor@MM


Subscript[IT, 1]=MM/.{Subscript[\[Alpha], 1,1]->1,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 2]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->1,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 3]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->1,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 4]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->1,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 5]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->1,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 6]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->1,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 7]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->1,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 8]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->1,Subscript[\[Sigma], 3,1]->0};
Subscript[IT, 9]=MM/.{Subscript[\[Alpha], 1,1]->0,Subscript[\[Alpha], 1,2]->0,Subscript[\[Alpha], 2,1]->0,Subscript[\[Alpha], 2,2]->0,Subscript[\[Alpha], 3,1]->0,Subscript[\[Alpha], 3,2]->0,Subscript[\[Sigma], 1,1]->0,Subscript[\[Sigma], 1,2]->0,Subscript[\[Sigma], 3,1]->1};
PrintMatrix/@(Subscript[IT, #]&/@Range@9)


Commutator[a_, b_] := Simplify[a.b - b.a]


exps=FullSimplify@ComplexExpand@MatrixExp[Subscript[IT, #]*t]&/@Range@9;
PrintMatrix/@exps


(* ::Input:: *)
(*AT=FullSimplify[exps[[n,1;;3,1;;3]].({*)
(* {Subscript[x, 1]+I*Subscript[y, 1]},*)
(* {Subscript[x, 2]+I*Subscript[y, 2]},*)
(* {u+I*v}*)
(*})+exps[[n,1;;3,4;;4]]]/.n->9;*)
(*PrintMatrix@AT*)
(*ST=S/.{Subscript[x, 1]->FullSimplify[Re[AT[[1,1]]]], Subscript[y, 1]->FullSimplify[Im[AT[[1,1]]]], Subscript[x, 2]->FullSimplify[Re[AT[[2,1]]]], Subscript[y, 2]->FullSimplify[Im[AT[[2,1]]]], u->FullSimplify[Re[AT[[3,1]]]], v->FullSimplify[Im[AT[[3,1]]]]};*)
(*TraditionalForm@Expand@FullSimplify@ComplexExpand@ST*)


(* ::Input:: *)
(*test=(Subscript[x, 1]+I*Subscript[y, 1])*(Cos[t]+I*Sin[t])*)


(* ::Input:: *)
(*Simplify@Expand[Expand@((FullSimplify@Im[Expand@test])^2)+Expand@((FullSimplify@Re[Expand@test])^2)]*)


(* ::Input:: *)
(*simplifiedMatrix = matrix[[1;;,1;;]];*)
(*PrintMatrix@simplifiedMatrix*)


(* ::Input:: *)
(*PrintMatrix@Drop[simplifiedMatrix, {2}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Z[\[CapitalPhi]_]:=1/2 (Subscript[A, 1,1]*(Subscript[x, 1]+I*Subscript[y, 1])+Subscript[A, 1,2]*(Subscript[x, 2]+I*Subscript[y, 2])+Subscript[A, 1,3]*(u+I*v) + Subscript[B, 1])*(D[\[CapitalPhi],Subscript[x, 1]]-D[\[CapitalPhi],Subscript[y, 1]])+1/2 (Subscript[A, 2,1]*(Subscript[x, 1]+I*Subscript[y, 1])+Subscript[A, 2,2]*(Subscript[x, 2]+I*Subscript[y, 2])+Subscript[A, 2,3]*(u+I*v) + Subscript[B, 2])*(D[\[CapitalPhi],Subscript[x, 2]]-D[\[CapitalPhi],Subscript[y, 2]])+1/2 (Subscript[A, 3,1]*(Subscript[x, 1]+I*Subscript[y, 1])+Subscript[A, 3,2]*(Subscript[x, 2]+I*Subscript[y, 2])+Subscript[A, 3,3]*(u+I*v) + Subscript[B, 3])*(D[\[CapitalPhi],u]-D[\[CapitalPhi],v])*)


(* ::Input:: *)
(*Simplify@Z[\[CapitalPhi]]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*m = Factor@simplifiedMatrix[[19;;32,15;;22]];*)
(*PrintMatrix@m*)
(*minors = DeleteCases[Flatten@Factor@Minors[m, 1], 0];*)
(*eq = #==0&/@minors;*)
(*Column@eq*)
(*Reduce[Flatten@{eq, Subscript[k, 4]!=0}]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Variables[VFS]*)


(* ::Input:: *)
(*Exponent[VFS, {Subscript[x, 1],Subscript[x, 2], Subscript[y, 1],Subscript[y, 2],u, v}]*)


(* ::Input:: *)
(*Column@MonomialList[VFS, {Subscript[x, 1],Subscript[x, 2], Subscript[y, 1],Subscript[y, 2],u, v},"DegreeLexicographic"]*)


(* ::Input:: *)
(*test=Expand[Subtract@@ST];*)
(*Column@MonomialList[test, {Subscript[x, 1],Subscript[x, 2], Subscript[y, 1],Subscript[y, 2],u, v},"DegreeLexicographic"]*)


(* ::Input:: *)
(*Column@MonomialList[SIT, {Subscript[x, 1],Subscript[x, 2], Subscript[y, 1],Subscript[y, 2],u, v},"DegreeLexicographic"]*)


(* ::Input:: *)
(*Binomial[2+4 - 1, 2]*)


(* ::Input:: *)
(*Binomial[# + 6 - 1, #]&/@{3,4,5,6}*)


(* ::Input:: *)
(*Total[{56,126,252,462}]*)


(* ::Input:: *)
(*Subscript[k, 2] Subscript[\[Alpha], 1,1]+Subscript[k, 5] Subscript[\[Alpha], 1,2]+2 Subscript[k, 1] Subscript[\[Alpha], 2,1]+Subscript[k, 4] Subscript[\[Alpha], 2,2]-Subscript[k, 3] Subscript[k, 4] Subscript[\[Alpha], 3,1]-Subscript[k, 2] Subscript[k, 5] Subscript[\[Alpha], 3,1]+\!\( *)
(*\*SubsuperscriptBox[\(k\), \(2\), \(2\)]\ *)
(*\*SubscriptBox[\(\[Alpha]\), \(3, 2\)]\)+2 Subscript[k, 1] Subscript[k, 3] Subscript[\[Alpha], 3,2]+Subscript[k, 3] Subscript[\[Beta], 1,1]+Subscript[k, 8] Subscript[\[Beta], 1,2]+Subscript[k, 7] Subscript[\[Beta], 2,2]-Subscript[k, 3] Subscript[k, 7] Subscript[\[Beta], 3,1]-Subscript[k, 2] Subscript[k, 8] Subscript[\[Beta], 3,1]+Subscript[k, 2] Subscript[k, 3] Subscript[\[Beta], 3,2]+Subscript[\[Gamma], 1,2]-Subscript[k, 2] Subscript[\[Gamma], 3,1]*)


(* ::Input:: *)
(*Simplify[%178]*)


(* ::Input:: *)
(*Factor[%179]*)


(* ::Input:: *)
(*Subscript[k, 2] Subscript[\[Alpha], 1,1]+Subscript[k, 5] Subscript[\[Alpha], 1,2]+2 Subscript[k, 1] Subscript[\[Alpha], 2,1]+Subscript[k, 4] Subscript[\[Alpha], 2,2]-(Subscript[k, 3] Subscript[k, 4] -Subscript[k, 2] Subscript[k, 5] )Subscript[\[Alpha], 3,1]+(\!\( *)
(*\*SubsuperscriptBox[\(k\), \(2\), \(2\)]\  + \(2\ *)
(*\*SubscriptBox[\(k\), \(1\)]\ *)
(*\*SubscriptBox[\(k\), \(3\)]\)\)) Subscript[\[Alpha], 3,2]+Subscript[k, 3] Subscript[\[Beta], 1,1]+Subscript[k, 8] Subscript[\[Beta], 1,2]+Subscript[k, 7] Subscript[\[Beta], 2,2]-(Subscript[k, 3] Subscript[k, 7] +Subscript[k, 2] Subscript[k, 8]) Subscript[\[Beta], 3,1]+Subscript[k, 2] Subscript[k, 3] Subscript[\[Beta], 3,2]+Subscript[\[Gamma], 1,2]-Subscript[k, 2] Subscript[\[Gamma], 3,1]*)


(* ::Input:: *)
(*Subscript[k, 1]*(Re@z)^2 + Subscript[k, 2]*Re@z*Im@z + Subscript[k, 3]*(Im@z)^2*)


(* ::Input:: *)
(*ComplexExpand[Re[z]^2 Subscript[k, 1]+Im[z] Re[z] Subscript[k, 2]+Im[z]^2 Subscript[k, 3],{z},TargetFunctions->Conjugate]*)


(* ::Input:: *)
(*TraditionalForm@Expand@FullSimplify[%65]*)


(* ::Input:: *)
(*test =1/2 (Subscript[k, 1]+Subscript[k, 3])(Abs@z)^2+1/4 (Subscript[k, 1]-Subscript[k, 3])(z^2+(Conjugate@z)^2)-1/4 I*Subscript[k, 2](z^2-(Conjugate@z)^2)*)


(* ::Input:: *)
(*TraditionalForm@Expand@test*)


(* ::Input:: *)
(*(Re@z)^2-z*Re@z*)


(* ::Input:: *)
(*Expand@Flatten[({*)
(* {Subscript[x, 1], Subscript[y, 1]}*)
(*}).({*)
(* {\[Lambda], \[Beta]},*)
(* {-\[Beta], \[Lambda]}*)
(*}).({*)
(* {Subscript[x, 1]},*)
(* {Subscript[y, 1]}*)
(*})][[1]]*)


(* ::Input:: *)
(*Eigenvalues@({*)
(* {Subscript[k, 1], Subscript[k, 2]/2},*)
(* {Subscript[k, 2]/2, -Subscript[k, 1]}*)
(*})*)


(* ::Input:: *)
(*Flatten[1/4 (z+Conjugate@{*)
(* {z, -I*(z-Conjugate@z)}*)
(*}).({*)
(* {Subscript[k, 1], Subscript[k, 2]/2},*)
(* {Subscript[k, 2]/2, -Subscript[k, 1]}*)
(*}).({*)
(* {z+Conjugate@z},*)
(* {-I*(z-Conjugate@z)}*)
(*})][[1]]*)


(* ::Input:: *)
(*Simplify[1/4 (-I (z-Conjugate[z]) (-(z+I (-z+Conjugate[z])) Subscript[k, 1]+1/2 (z+Conjugate[z]) Subscript[k, 2])+(z+Conjugate[z]) ((z+Conjugate[z]) Subscript[k, 1]+1/2 (z+I (-z+Conjugate[z])) Subscript[k, 2]))]*)


(* ::Input:: *)
(*Expand[1/8 (((4+2 I) z^2-2 I z Conjugate[z]+4 Conjugate[z]^2) Subscript[k, 1]+((1-2 I) z^2+z Conjugate[z]+2 I Conjugate[z]^2) Subscript[k, 2])]*)


(* ::Input:: *)
(*TraditionalForm[%]*)


(* ::Input:: *)
(*TeXForm@quardaticForm*)


(* ::Input:: *)
(*quardaticForm*)


(* ::Input:: *)
(*TeXForm[ComplexExpand@Im@W@AT]*)


(* ::Input:: *)
(*TeXForm[v*Subscript[x, 2] + Q - Subscript[x, 2]*(\[Mu]*Subscript[x, 2]^2+\[Nu]*Subscript[y, 2]^2)/.{Subscript[x, 1]->FullSimplify@Re@Subscript[Z, 1]@AT, Subscript[y, 1]->FullSimplify@Im@Subscript[Z, 1]@AT, Subscript[x, 2]->FullSimplify@Re@Subscript[Z, 2]@AT, Subscript[y, 2]->FullSimplify@Im@Subscript[Z, 2]@AT, u->FullSimplify@Re@W@AT, v->FullSimplify@Im@W@AT}]*)


(* ::Input:: *)
(*TeXForm@Column[ M[1]= #&/@Range@3]*)


(* ::Input:: *)
(*test = v*Subscript[x, 2]/.quardaticForm/.{Subscript[x, 1]->FullSimplify@Re@Subscript[Z, 1]@AT, Subscript[y, 1]->FullSimplify@Im@Subscript[Z, 1]@AT, Subscript[x, 2]->FullSimplify@Re@Subscript[Z, 2]@AT, Subscript[y, 2]->FullSimplify@Im@Subscript[Z, 2]@AT, u->FullSimplify@Re@W@AT, v->FullSimplify@Im@W@AT}/.parameterSubstitutions*)
(*dTest =D[test, t]/.t->0/.diffSubstitution*)
(*subs=dTest/.v->(-Q[Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2]]/Subscript[x, 2] +(\[Mu]*Subscript[x, 2]^2+\[Nu]*Subscript[y, 2]^2))*)
(*FullSimplify@Collect[subs, {1/Subscript[x, 2]}]*)
(*cc=Collect[Expand[Subscript[x, 2]^2*subs],{Q[Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2]]}]*)
(*TeXForm@cc*)
(*TraditionalForm@cc*)


(* ::Input:: *)
(*TeXForm@cc*)


(* ::Input:: *)
(*mm=(\[Mu] *)
(*\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\)+\[Nu] *)
(*\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\)) (Subscript[x, 1] Subscript[\[Beta], 1,1]-Subscript[y, 1] Subscript[\[Beta], 1,2]+Subscript[x, 2] Subscript[\[Beta], 2,1]-Subscript[y, 2] Subscript[\[Beta], 2,2]+u Subscript[\[Beta], 3,1]-(-(Q[Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2]]/Subscript[x, 2])+\[Mu] *)
(*\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\)+\[Nu] *)
(*\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\)) Subscript[\[Beta], 3,2]+Subscript[\[Sigma], 2,1])+Subscript[x, 2] (2 \[Mu] Subscript[x, 2] (Subscript[x, 1] Subscript[\[Beta], 1,1]-Subscript[y, 1] Subscript[\[Beta], 1,2]+Subscript[x, 2] Subscript[\[Beta], 2,1]-Subscript[y, 2] Subscript[\[Beta], 2,2]+u Subscript[\[Beta], 3,1]-(-(Q[Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2]]/Subscript[x, 2])+\[Mu] *)
(*\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\)+\[Nu] *)
(*\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\)) Subscript[\[Beta], 3,2]+Subscript[\[Sigma], 2,1])+2 \[Nu] Subscript[y, 2] (Subscript[y, 1] Subscript[\[Beta], 1,1]+Subscript[x, 1] Subscript[\[Beta], 1,2]+Subscript[y, 2] Subscript[\[Beta], 2,1]+Subscript[x, 2] Subscript[\[Beta], 2,2]+(-(Q[Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2]]/Subscript[x, 2])+\[Mu] *)
(*\!\(\*SubsuperscriptBox[\(x\), \(2\), \(2\)]\)+\[Nu] *)
(*\!\(\*SubsuperscriptBox[\(y\), \(2\), \(2\)]\)) Subscript[\[Beta], 3,1]+u Subscript[\[Beta], 3,2]+Subscript[\[Sigma], 2,2]))*)


(* ::Input:: *)
(*Simplify[%702]*)


(* ::Input:: *)
(*CoefficientRules[Expand@(Subscript[x, 2]*mm),{Subscript[x, 1],Subscript[y, 1],Subscript[x, 2],Subscript[y, 2],u,v}] *)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*Simplify@Expand@mm*)


(* ::Input:: *)
(*TeXForm@%*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*TeXForm[Replace[matrix, Except[0|_List]->"N", 2]]*)


(* ::Input:: *)
(*PolynomialQ[0,{x,y}]*)


(* ::Input:: *)
(*MatchQ[{Subscript[k, 1] Subscript[k, 2],123,123,123},Except[0,_?(PolynomialQ[#,Flatten@{Table[Subscript[k, i],{i, 1, 10}], \[Nu],\[Mu]}]&)]]*)


(* ::Input:: *)
(*PolynomialQ[Subscript[k, 1] Subscript[k, 2],{Subscript[k, 1],Subscript[k, 2]}]*)


(* ::Input:: *)
(*Times @@ ({Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}^#[[1]])*#[[2]]&/@CoefficientRules[VFS, {Subscript[x, 1],Subscript[x, 2],Subscript[y, 1],Subscript[y, 2],u,v}];*)


(* ::Input:: *)
(*Total@%*)


(* ::Input:: *)
(*TeXForm[\!\( *)
(*\*SubsuperscriptBox[\(x\), \(2\), \(3\)]\ *)
(*\*SubscriptBox[\(\[Sigma]\), \(3, 2\)]\)]*)


(* ::Input:: *)
(**)


(* ::Input:: *)
(**)


(* ::Input:: *)
(*test=AdaptiveElmination[Select[AdaptiveElmination[matrix,{Subscript[k, 1]}],#=!=Table[0,{i,1,24}]&][[15;;,15;;]], {\[Mu]}];*)
(*PrintMatrix@test*)
(*PrintMatrix@Factor@AdaptiveElmination[test[[3;;,3;;]],{Subscript[k, 1],Subscript[k, 4]}]*)



