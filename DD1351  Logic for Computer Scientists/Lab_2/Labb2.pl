%__________________ Main code ________________%

%	Takes an input file and saves the files premisses, goal and the proof
%	In the variables Prems, Goal and prrof. These are sent to predicates that start the control
verify(InputFileName) :- see(InputFileName),
    read(Prems),read(Goal), read(Proof),
    seen,
    validate_proof(Prems, Goal, Proof).

%	In order for the proof to be true, the goal and the proof must be correct
%	Here we define VerifiedRows as an empty list, which we will fill up with controlled lines
validate_proof(Prems, Goal, Proof):-
    match_goal(Goal,Proof),
    verify_proof(Prems,Proof,[]), !.

			
%	Checks if the goal is the same as the last line in the proof. 
%	Last adds the last line in proof to a new list called LastRow.
%	Nth checks the second element in LastRow to see if its identical to the goal
%	Puts the last element in the proof in the LastRow variable
%	Extracts the second element in the list of LastRow
match_goal(Goal,Proof):-
    last(Proof,LastRow), 
    nth1(2,LastRow,Goal). 
	

%____________________Help functions _________________%

%	Puts an element in the list using appendEL :- last in line
addList(H,VerifiedRows,NewList):-
    appendEl(H,VerifiedRows,NewList).

%	Puts an element last in a list
appendEl(X,[],[X]).
appendEl(X,[H|T],[H|Y]):-
    appendEl(X,T,Y).

%__________________ Verifies the proof ______________________%
% If the proof is an empty list, base case, then it is true. I.e if we have succesfully verified all the rows the proof will be an empty list and the proof is true
% We verify_row the head (i.e the first list in the list of proof) for every rule we have
% We add the head to the VerifiedRows, which in turn both are added to NewList
% If not, we check the prems, the proof (which we divide in a head and tail, and a checked list where we store all the controlled lines)
% verify_proof is iterated, but now we control the next list (line)  in the proof, where the previous NewList becomes VerifiedRows
verify_proof(_,[],_).
verify_proof(Prems,[H|T],VerifiedRows):-
    verify_row(Prems,H,VerifiedRows),
    addList(H,VerifiedRows,NewList),
    verify_proof(Prems,T,NewList).
	
	
%_________________Predefined rules_____________________%

/* These rules are already defined
imp(p, q)
and(or(p, q), r)
imp(neg(p), cont)
and(and(and(p,q),r),s) 
cont
*/
	
%___________________________________________________________________Rules____________________________________________________________%

%_____Premise rule_____%
%	RowNumber1 and RowNumber2 represent row numbers when two lines are involved
%	Atom1 and Atom2 represent various atoms when two lines are involved
%	RowNumber represents just that when one line is involved
%	Atom represents just that when one line is involved
verify_row(Prems,[_,Rule, premise],_):-
    member(Rule,Prems).


%___________________________________ Assumptions, i,e Boxes _____________________________________________%

%If there is a list with the word assumption in it, where the tail is the rest of the box
%Then the program will iterate through the rest of the box, where the assumption will be part of the checked list
%And the new proof will be the tail, i.e the rest of the box


verify_row(Prems,[[_,_,assumption]|BoxTail],VerifiedRows):-
    verify_proof(Prems,BoxTail,[[_,_,assumption]|VerifiedRows]).


%__________________________AND rules__________________________________________________%


%____________And introduction______%
%	Premisses are ignored
%	Line numbers are ignored
%	First member checks if Atom1 on RowNumber1 exists in the verified list
%	Second member checks if Atom2 on RowNumber2 is a member of the verified list
verify_row(_,[_,and(Atom1,Atom2),andint(RowNumber1,RowNumber2)],VerifiedRows):-
    member([RowNumber1,Atom1,_],VerifiedRows), 
    member([RowNumber2,Atom2,_],VerifiedRows).


%______AND elimination 1_____%
%	If the Atom is a member of a conjuction, then andel1 is true
verify_row(_,[_,Atom,andel1(RowNumber)],VerifiedRows):-
    member( [RowNumber,and(Atom,_),_], VerifiedRows).


%______AND elimination 2_____%
%	The other part of the conjuction
verify_row(_,[_,Atom,andel2(RowNumber)],VerifiedRows):-
    member([RowNumber,and(_,Atom),_], VerifiedRows).
	
	
%_____________________________________OR rules______________________________________________%

% ___OR introduction 1______%
%	Looks if RowNumber and the Atom are in the list before being introduced
verify_row(_,[_,or(Atom,_),orint1(RowNumber)],VerifiedRows):-
    member([RowNumber,Atom,_],VerifiedRows).


%_____OR introduction 2_______%
%	The other part of the disjunction
verify_row(_,[_,or(_,Atom),orint2(RowNumber)],VerifiedRows):-
    member([RowNumber,Atom,_],VerifiedRows).


% _____ Or Elimination Rule ___%
%	If both Atom1 and Atom2 have the same conclusion, we can eliminate the OR-rule and replace it with the conclusion
%	First member Checks if there is an or(Atom1, Atom2) on RowNumber
%	Second member starts to iterate and bactrack until it has found all the necessary boxes
%	Third member checks for an assumption in the box. If the head isn't a box, it will fail the first member will backtrack
%	Fourth looks for the conclusion in the box, where the conclusion is X and ConclusionNumber1 is the row number for that conclusion
%	Fifth member checks for the second box
%	Sixth member for assumption in second box, previously it iterated through first box and backtracked to the second box
%	Seventh member looks for the same conclusion X in the second box, conc 2 is the line number
verify_row(_,[_,Conclusion,orel(RowNumber,AssumptionNumber,ConclusionNumber1,AssumptionNumber2,ConclusionNumber2)],VerifiedRows):-
    member( [RowNumber, or(EliminatedAtom1,EliminatedAtom2),_], VerifiedRows), 		
    member( BoxFinder1, VerifiedRows),										
    member([AssumptionNumber,EliminatedAtom1,assumption],BoxFinder1),		
    member([ConclusionNumber1,Conclusion,_],BoxFinder1),			
    member(BoxFinder2,VerifiedRows),										
    member([AssumptionNumber2, EliminatedAtom2, assumption],BoxFinder2),   
    member([ConclusionNumber2,Conclusion,_],BoxFinder2).				
	
	
%_____________________________Implication rules_____________________%	


%___ Implication introduction___%
%	Does an assumption exist for the implication      
%	Is there an assumption for Atom1 in the list in a box
%	Does Atom2 exist as a conclusion in the box
%	First member Iterates and backtracks through boxes
%	Second member looks for an assumption on RowNumber1
%	third member looks for a conclusion on RowNumber2
verify_row(_,[_,imp(Atom1,Atom2),impint(RowNumber1,RowNumber2)],VerifiedRows):-
    member(BoxFinder,VerifiedRows), 											
    member([RowNumber1,Atom1,assumption],BoxFinder),							
    member([RowNumber2,Atom2,_],BoxFinder).						
	
	
%___ implication elimination_______%
%	First member looks if Atom2 is among the verified rows
%	Second member looks if Atom2 implicates Atom1 is among the verified rows
verify_row(_, [_, Atom1, impel(RowNumber1, RowNumber2)], VerifiedRows) :-
            member([RowNumber1, Atom2, _], VerifiedRows), 
            member([RowNumber2, imp(Atom2,Atom1),_], VerifiedRows). 				


%__________________________________ Negation Rules________________________________________________________________%

%_______Negation introduction_____%
%	First member assigns Boxfinder to the first element in the verified list, and keeps failing and backtracking through the other member until it reaches the proper box.
%	Second member finds where in the said box the assumption is.
%	Third member box finds the contradiction in said box
verify_row(_,[_,neg(Atom),negint(RowNumber1,RowNumber2)],VerifiedRows):-
    member(BoxFinder,VerifiedRows), 
    member([RowNumber1,Atom,assumption],BoxFinder),
    member([RowNumber2,cont,_],BoxFinder).
	
	
%______Negation negation introduction___%
%	It searches if the Atom exists on a previus RowNumber in the verified list, if yes then the Atom can exist with double negations
verify_row(_,[_,neg(neg(Atom)),negnegint(RowNumber)],VerifiedRows):-
    member([RowNumber,Atom,_],VerifiedRows).


%______Negation elimination______%
%	If the atom exists on row number 1
%	But also its negation exists on row number 2, then a contradiction exists and we can negEliminate
verify_row(_,[_,cont,negel(RowNumber1,RowNumber2)],VerifiedRows) :-
	member([RowNumber1,Atom,_],VerifiedRows),
	member([RowNumber2,neg(Atom),_],VerifiedRows).
	
	
%__________Negation negation elimination
%	It searches if negnegAtom exists on a previus Row, if yes then the Atom can exist standalone 
verify_row(_,[_,Atom,negnegel(RowNumber)],VerifiedRows):-
    member([RowNumber,neg(neg(Atom)),_],VerifiedRows).


%__________________________Various other rules_________________%

%___ Copy Rule___%
%	Look for the row and see if it exists earlier.
verify_row(_,[_,Atom,copy(RowNumber)],VerifiedRows):-
    member([RowNumber,Atom,_],VerifiedRows).


%___Contradiction Elimination___%
verify_row(_,[_,_,contel(RowNumber)],VerifiedRows):-
    member([RowNumber,cont,_],VerifiedRows).


%___LEM___%
%	Always true whenever there's a lem.
%	Atom or negAtom always produces a truism
verify_row(_,[_,or(Atom,neg(Atom)),lem],_).


%___Modus Tollens______%
%	If Atom1 implies Atom2
%	And if there exists a negAtom2 on RowNumber2, then modus tollens applies and negAtom1 exists aswell
verify_row(_,[_,neg(Atom1),mt(RowNumber1,RowNumber2)],VerifiedRows):-
    member([RowNumber1,imp(Atom1,Atom2),_],VerifiedRows),
    member([RowNumber2,neg(Atom2),_],VerifiedRows).


%___ Proof by contradiction ___%
verify_row(_,[_,Atom,pbc(RowNumber1,RowNumber2)],VerifiedRows):-
    member(BoxFinder,VerifiedRows),			%BoxFinder gets assigned the first element in the verified list,fails through the member functions below and backtracks until a box is reached
    member([RowNumber1,neg(Atom),assumption],BoxFinder), 	%This finds if there is an assumption with neg(x) in that box
    member([RowNumber2,cont,_],BoxFinder).				%This member finds if there is a contradiction in that same box


















