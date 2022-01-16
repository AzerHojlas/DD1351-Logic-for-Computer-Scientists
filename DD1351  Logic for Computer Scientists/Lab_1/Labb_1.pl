

% Arg 1 - An element
% Arg 2 - An empty list
% Arg 3 - Adds it to the empty list

appendEl(X, [], [X]).

%
appendEl(X, [H|T],[H|Y]) :-
           appendEl(X, T, Y).


select(X,[X|T],T).
select(X,[Y|T],[Y|R]) :- select(X,T,R).

member(X,L) :- select(X,L,_).


/* - här är koden */

remove_duplicates(Input, Output):-
	cleaner(Input,[],Output).

% If we get an empty list then do nothing. Base case. When the list is finished the input will become an empty list, meaning that the output and accumulator will be the same list
% and we will return to the empty list base case.
cleaner([],Acc,Acc).

% If Acc has the same element in the list then jump over and take tail
cleaner([H|T], Acc, Outlist) :-
	member(H, Acc),
	cleaner(T, Acc, Outlist).

% If Acc does not have the same element in the list then add it onto list
cleaner([H|T], Acc, Outlist) :-
         \+ member(H,Acc),
	appendEl(H, Acc, List),
	cleaner(T, List, Outlist).
	
	p(a).
