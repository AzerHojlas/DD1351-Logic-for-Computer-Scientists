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



/*____________________________________________________________________Rules________________________________*/

%___________Check match_______%
check(_,L,S,[],Formula):-
    member([S,LabelNames],L), 
    member(Formula,LabelNames). 
	
	
%_______Check NOT match_______________%
check(_,L,S,[],neg(Formula)):-
    member([S,LabelNames],L),
    \+ member(Formula,LabelNames).



%_________OR match__________%
check(T,L,S,[],or(X,Y)):-
    check(T,L,S,[],X);  
    check(T,L,S,[],Y).



%______AND match______%
check(T,L,S,[],and(X,Y)):-
    check(T,L,S,[],X),
    check(T,L,S,[],Y).
	
	

%___ AX - In all next states _________%
check(T,L,S,[],ax(Formula)):-
    all_trans_current_state(T,L,S,[],Formula).



%_________AG - Always________%
check(_,_,S,U,ag(_)):-
    member(S,U).

check(T,L,S,U,ag(Formula)):-
    \+member(S,U), 
    check(T,L,S,[],Formula),
    all_trans_current_state(T,L,S,[S|U],ag(Formula)).



%________ AF - Eventually it will happen______%
check(T,L,S,U,af(Formula)):-
    \+member(S,U), 
    check(T,L,S,[],Formula). 

check(T,L,S,U,af(Formula)):-
    \+member(S,U),
    all_trans_current_state(T,L,S,[S|U],af(Formula)). 

%_____EF - there exists some next state_____%

check(T,L,S,[],ex(Formula)):-
    exists_trans_current_state(T,L,S,[],Formula). 



%_________EG - A path exists which always holds true___________%
check(_,_,S,U,eg(_)):-
    member(S,U).

check(T,L,S,U,eg(Formula)):-
    \+member(S,U),
    check(T,L,S,[],Formula), 
    exists_trans_current_state(T,L,S,[S|U],eg(Formula)).


%____EF -  A path exists which will eventually hold true____%
check(T,L,S,U,ef(Formula)):-
    \+member(S,U),
    check(T,L,S,[],Formula).


check(T,L,S,U,ef(Formula)):-
    \+member(S,U),
    exists_trans_current_state(T,L,S,[S|U],ef(Formula)).

%_______________________________ Transitions______________________________________%

/*_____________________All quantifier_________________________*/
all_trans_current_state(T,L,S,U,F):-
    member([S,Transitions],T), 
    all_states_iterator(T,L,U,F,Transitions). 


all_states_iterator(_,_,_,_,[]).

all_states_iterator(T,L,U,F,[Head|Tail]):-
    check(T,L,Head,U,F), 
    all_states_iterator(T,L,U,F,Tail). 

/*_____________________Exists quantifier______________________*
exists_trans_current_state(T,L,S,U,F):-
    member([S,Transitions],T), 
    exists_one_state(T,L,U,F,Transitions),!. 

exists_one_state(T,L,U,F,[Head|Tail]):-
    check(T,L,Head,U,F); 
    exists_one_state(T,L,U,F,Tail),!.












