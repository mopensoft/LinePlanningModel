%%%%%%%%%%%%%% DESCRIPTION %%%%%%%%%%%%%%
/*
This is the basic model with extention 01 where
- NEW: train trips run in both direction from station 1 to nStations (inbound)
- OD matrix includes outbound demand
- flow need to be in both directions
- NEW: separate turnback and stabling station:
  - trains can end the trip at turn back station but have to form another trip: # of trip start = # of trip end
  - trains can terminate at stabling stations: # of trips start and trips end at the station can be different

Key assumption: 
- not limit of trains of any type in stabling location.
- number of train running inbound on a route can be different than those running outbound on that route
- only train type run one each route

Extra Constraints:
- turnback: # of train start and end at turn back location are equal number of any type. 
*/

%%%%%%%%%%%%%% PARAMETER %%%%%%%%%%%%%%%%
%include "Test01.dzn";
int: nStations; % number of station in a single line in direction order 1->10 and 10->1
set of int: STATIONS = 1..nStations;

array[int] of int: turnbackLocs; % stations that allow trains to turn back
set of int: TURNBACKS = index_set(turnbackLocs);
array[int] of int: stablingLocs; % stations that allow to terminate trains (ie. park into stabling yard)
set of int: STABLINGS = index_set(stablingLocs);
set of int: START_END_LOCS = 1..card(TURNBACKS) + card(STABLINGS);
array[START_END_LOCS] of int: start_end = stablingLocs ++ turnbackLocs; % array of station where train can start and end the trips
% Number of possible routes (origin, destination) based on turnback and stabling locations. 
% FIXME: this only work with single line with no branch, specific combination required with branched network 
set of int: ROUTES = 1..card(START_END_LOCS) * (card(START_END_LOCS) - 1); % set of routes including both direction
% array of routes in both direction
array[ROUTES, 1..2] of int: possibleRoutes = array2d(ROUTES, 1..2, 
  [
    if j mod 4 == 1 then
      start_end[i]
    elseif j mod 4 == 2 then
      start_end[j div 4 + 1]
    elseif j mod 4 == 3 then 
      start_end[j div 4 + 1]
    else 
      start_end[i]
    endif 
    | i in 1..card(START_END_LOCS)-1, j in i*4+1..card(START_END_LOCS)*4 ]);

array[STATIONS, STATIONS] of int: odmatrix; % origin - destination matrix which can be used to identify the flow
int: totalPAX = sum(odmatrix);

int: Inbound = 1;
int: Outbound = 2;
set of int: DIRECTION = Inbound..Outbound;
array[int, 1..3] of int: links; % link between 2 adjacent stations [origin, destination, distance]
set of int: LINKS = index_set_1of2(links); % set of links
array[LINKS] of int: linkCapacity; % Capacity of each link on 1 direction. Presume that capacity is the same for other direction
int: MaxLink = max(linkCapacity); % max number of service running on any link
array[LINKS] of int: linkFlow; % number of passenger travelling on each link - This can be calculated from OD matrix with predefine travelling routes

% Specify if a link is contained in a route. [r,l] = 1 means link l in part of route r and 0 otherwise
array[ROUTES, LINKS] of int: route_link = array2d(ROUTES, LINKS, 
  [ if (links[l,1] - links[l,2]) * (possibleRoutes[r,1] - possibleRoutes[r,2]) < 0 then % route and link are in different direction
      0
    else % same direction --> need to check if start and end of a link are in between start and end of the route
      if (links[l,1] - possibleRoutes[r,1]) * (links[l,1] - possibleRoutes[r,2]) <= 0 
          /\ (links[l,2] - possibleRoutes[r,1]) * (links[l,2] - possibleRoutes[r,2]) <= 0
      then 1 
      else 0 
      endif 
    endif 
  | r in ROUTES, l in LINKS]);

array[int] of int: trainCapacity; % number of passengers a train can carry. More array item if more trains are used
set of int: TRAINTYPES = index_set(trainCapacity); % set of train type can be used
array[TRAINTYPES] of int: trainCost; % cost of train running 1 meter

array[STATIONS, STATIONS] of int: odDistance = array2d(STATIONS, STATIONS, 
      [
        sum (l in LINKS) (bool2int((links[l,1] == i /\ links[l,2] == j) \/ (links[l,1] == j /\ links[l,2] == i)) * links[l,3])
        |i, j in STATIONS]); % distance between each adjacent pair of staions

%%%%%%%%%%%%% VARIABLE %%%%%%%%%%%%%%%%%%
array[ROUTES] of var 0..MaxLink: servicePlan; % number of services running on each routes on each direction. Row 1: inbound and Row 2: outbound
array[ROUTES] of var TRAINTYPES: trainPlan; % train running of each routes. Presume that each route running 1 type of train for simplicity purpose
var int: directPAX; % # of PAX can travel direct from origins to destinations
var int: trainDistance; % distance that train running according to service plan

%%%%%%%%%%%%% CONSTRAINTS %%%%%%%%%%%%%%%
% /* 
%   1. Link Capacity: The number of services running on each link is not greater than link capacity
%   2. PAX demand cover: The number of services need to cover the flow of passenger on each links
%   3. Turback: number of train of each type start and end at turnback need to be equal
%   FUTURE: sufficient number of trains available to operate service plan => identify where should they park overnight
%   FUTURE: sufficient capacity of each turnback stations to turn the train back => how many turnbacks per time period
%   FUTURE: more detailed declaration of each routes if there're branches in the network. Order of a pair of turnback stations is not enough
% */
% Constraint 1: The number of services running on each link is not greater than link capacity
constraint forall(l in LINKS) (sum(r in ROUTES) (servicePlan[r] * route_link[r,l]) <= linkCapacity[l]);
% Constraint 2: The number of services need to cover the flow of passenger on each links
constraint forall(l in LINKS) (sum(r in ROUTES) (trainCapacity[trainPlan[r]] * servicePlan[r] * route_link[r,l]) >= linkFlow[l]);
% Constraint 3: Number of train of each type start and end at turnback need to be equal
constraint forall(t in TURNBACKS) 
  ( forall(tt in TRAINTYPES)
    (
      sum(r in ROUTES where possibleRoutes[r,1] == turnbackLocs[t] /\ trainPlan[r] == tt) (servicePlan[r]) 
      == 
      sum(r in ROUTES where possibleRoutes[r,2] == turnbackLocs[t] /\ trainPlan[r] == tt) (servicePlan[r])
    )
  );

%%%%%%%%%%%%% OBJECTIVES CONSTRAINTS %%%%%%%%%%%%%%%%
int: transferWeight;
int: operationWeight;

% Calculate total number of PAX no need transfers
constraint directPAX = sum(o in 1..nStations-1, d in o+1..nStations) (odmatrix[o,d] * bool2int(DirectTravel(o,d))); 
% Calculate total running distance of services. FIXME: this should later include other operational cost ie. fuel, labour, etc.
constraint trainDistance = sum(r in ROUTES) (servicePlan[r] * trainCost[trainPlan[r]] * Distance(r)); 

%%%%%%%%%%%%% FUNCTIONS AND PREDICATE %%%%%%%%%%%
predicate DirectTravel(int: o, int: d) = 
  exists(r in ROUTES) (servicePlan[r] > 0 /\ o in possibleRoutes[r, 1].. possibleRoutes[r, 2] /\ d in possibleRoutes[r,1].. possibleRoutes[r,2]);
function int: Distance(int: route) =
  sum(s in possibleRoutes[route,1]..possibleRoutes[route,2]-1) (odDistance[s, s + 1]); % FIXME: this should be more sophiticated based on links instead of station order OR each possible routes include all the stations from start to end of the line. 

%%%%%%%%%%%%% SOLVE PROBLEM %%%%%%%%%%%%%%%%%%%%%
%solve satisfy;
solve minimize transferWeight * (totalPAX - directPAX) + operationWeight * trainDistance;

%%%%%%%%%%%%% OUTPUT %%%%%%%%%%%%%%%%%%%%%%%%%%%
output 
% Test output
%["OD Distance:\n"] ++ [show(odDistance[i,j]) ++ if j == nStations then "\n" else ", " endif | i, j in STATIONS] ++ % Show distance matrix
% ["Route-link:\n"] ++ [show(route_link[r,l]) ++ if l == card(LINKS) then "\n" else ", " endif | r in ROUTES, l in LINKS] ++ % show route-link matrix
% ["Possible Route: "] ++ ["(" ++show(possibleRoutes[r,1]) ++ "," ++ show(possibleRoutes[r,2]) ++ "), " | r in ROUTES];
%[if j mod 2 == 1 then show(turnbackLocs[i]) ++ ", " else show(turnbackLocs[j div 2]) ++ ", " endif | i in 1..card(TURNBACKS)-1, j in i*2+1..2*card(TURNBACKS)];
% Model output
["\nInput flow: "] ++ [show(linkFlow[l]) ++ ", " | l in LINKS]++
["\nLink flow : "] ++ [show((sum(r in ROUTES) (trainCapacity[trainPlan[r]] * servicePlan[r] * route_link[r,l]))) ++ ", " | l in LINKS] ++
["\nService plan: "] ++ [show(servicePlan[r]) ++ "x" ++ "(" ++show(possibleRoutes[r,1]) ++ "," ++ show(possibleRoutes[r,2]) ++ "), " | r in ROUTES] ++
["\nTrain type  : "] ++ [show(trainPlan[r]) ++ "x" ++ "(" ++show(possibleRoutes[r,1]) ++ "," ++ show(possibleRoutes[r,2]) ++ "), " | r in ROUTES] ++
["\nObjective value: "] ++ [show(transferWeight*(totalPAX - directPAX) + operationWeight*trainDistance)];