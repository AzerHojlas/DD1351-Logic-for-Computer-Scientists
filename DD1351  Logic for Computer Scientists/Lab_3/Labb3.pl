%_________________________________________Given code_____________________________%
% Loads the necessary inputs from the file 
verify(Input) :-
    see(Input),
    read(T),
    read(L),
    read(S),
    read(F),
    seen,
	check(T, L, S, [], F).


% check (T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.


%________________________________Literals_________________________________%

%___________Check match_______%

%	Checks if the labeling is inside of the list
%	First member checks if the label in the current state is in the labeling list L
%	Second member checks if Formula is identical to the desired formula F

check(_,L,S,[],Formula):-
    member([S,LabelNames],L), 
    member(Formula,LabelNames). 
	
	
%_______Check NOT match_______________%

%	Checks if the label is not inside of the Label list L

check(_,L,S,[],neg(Formula)):-
    member([S,LabelNames],L),
    \+ member(Formula,LabelNames).

%__________________________________ Easy rules________________________________________%

%_________OR__________%

%	checks if F is a or statement
%	The rules below recall the literals rules

check(T,L,S,[],or(X,Y)):-
    check(T,L,S,[],X);  
    check(T,L,S,[],Y).



%______AND______%

%	checks if F is a AND statement

check(T,L,S,[],and(X,Y)):-
    check(T,L,S,[],X),
    check(T,L,S,[],Y).
	
	
%_____________________ Other Rules _____________________%

%___ AX - In all next states _________%

%	all_trans_current_state will first find the appropriate line in the transition list
%	Then all_states_iterator will iterate through all the transitions in that line to %	see if AX holds true

check(T,L,S,[],ax(Formula)):-
    all_trans_current_state(T,L,S,[],Formula).



%_________AG - Always________%

%	Base case - In case we already have checked the states.
%	If we find ourselves in this endless loop where all other states have been blocked
%	then this will hold true
%	All states will be blocked untill this becomes true, that is if it is true

check(_,_,S,U,ag(_)):-
    member(S,U).

%	First member checks if the current state is not part of our blocked list
%	If not, then it adds the current state to our blocked list
%	The second check lines looks if our Formula Formula is true  for the current state
%	all_trans_current_state iterates through the other states and adds current state to %	the blocked list
%	all_states_iterator iterates through the transitions to see if AG holds in them

check(T,L,S,U,ag(Formula)):-
    \+member(S,U), 
    check(T,L,S,[],Formula),
    all_trans_current_state(T,L,S,[S|U],ag(Formula)).



%________ AF - Eventually it will happen______%

%	First member checks if the current state is NOT a member of the blocked list
%	Second check looks if the formula matches for the current state

check(T,L,S,U,af(Formula)):-
    \+member(S,U), 
    check(T,L,S,[],Formula). 

%	If the basse case doesn't apply, then we start building the blocked list
%	First member checks that the current state is not a member of the blocked list
%	The current state is added to the blocked list and we check the other transitions 
%	for this condition

check(T,L,S,U,af(Formula)):-
    \+member(S,U),
    all_trans_current_state(T,L,S,[S|U],af(Formula)). 

%_____EFormula - there exists some next state_____%

%	exists_trans_current_state will check the formula for validity

check(T,L,S,[],ex(Formula)):-
    exists_trans_current_state(T,L,S,[],Formula). 



%_________EG - A path exists which always holds true___________%

%	if the state is a member of the blocked list, the this holds true

check(_,_,S,U,eg(_)):-
    member(S,U).

%	If the state is not part of the blocked list, which is what the member does
%	Check looks if the formula holds true for the current state
%	exists_trans_current_state adds the state to the blocked list and checks the other %transitions

check(T,L,S,U,eg(Formula)):-
    \+member(S,U),
    check(T,L,S,[],Formula), 
    exists_trans_current_state(T,L,S,[S|U],eg(Formula)).


%____EF -  A path exists which will eventually hold true____%

%	Base case, if the current state isn't a member of the blocked list then validate

check(T,L,S,U,ef(Formula)):-
    \+member(S,U),
    check(T,L,S,[],Formula).

%	If the current state is not a member of the blocked list, then check all its trans

check(T,L,S,U,ef(Formula)):-
    \+member(S,U),
    exists_trans_current_state(T,L,S,[S|U],ef(Formula)).

%_______________________________ Transitions______________________________________%

%	Finds the appropriate transition list
%	first member checks if the current state S is part of the transitions list T
%	and finds it's specific row
%	all_states_iterator checks Transitions for validity, if it holds true, then the %	rule is valid

all_trans_current_state(T,L,S,U,F):-
    member([S,Transitions],T), 
    all_states_iterator(T,L,U,F,Transitions). 

%	Once the appropriate path has been found, will iterate
%	Iterates through all the individual transitions for the current state
%	all_states_iterator checks for validity within the transitions list
%	Base case: if the list of possible transitions T or Transitions is empty then it is true, i.e they have been iterated
%	first checks if all transitions are true for the first state in the list.
%	second fact iterates/checks recursively through the rest of the states in the 
%	row until the row becomes empty and all_states_iterator becomes true 

all_states_iterator(_,_,_,_,[]).

all_states_iterator(T,L,U,F,[Head|Tail]):-
    check(T,L,Head,U,F), 
    all_states_iterator(T,L,U,F,Tail). 



%	checks if there is at least one transition
%	member checks if the current state and its variable is part of the transition list, cuts if one state is true

exists_trans_current_state(T,L,S,U,F):-
    member([S,Transitions],T), 
    exists_one_state(T,L,U,F,Transitions),!. 

%	The first check looks if the first state in the transition list is valid
%	If it is, then the rule is true, if not, then it checks the next state until true
%	The second fact iterates through the other states in the row, cuts if true

exists_one_state(T,L,U,F,[Head|Tail]):-
    check(T,L,Head,U,F); 
    exists_one_state(T,L,U,F,Tail),!.












