%%%%%%%%%%%%%% DESCRIPTION %%%%%%%%%%%%%%
/*
This is the basic model to test CPRCP OD matrix (currently inbound direction)
- OD from PTV patronage model
- Only stabling station provided (train can start and stop)

Key assumption: 
- not limit of trains of any type in stabling location.
- number of train running inbound on a route can be different than those running outbound on that route
- NEW: Multiple train type run one each route

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
int: nRoutes; % number of routes
set of int: ROUTES = 1..nRoutes; % set of routes including both direction
% array of routes in both direction. NOTE: this is fun with single line but should be predefined from input data in more complicated network
int: maxRouteLength;
set of int: MAXLENGTH = 1..maxRouteLength;
array[ROUTES, MAXLENGTH] of int: possibleRoutes;
array[STATIONS, STATIONS] of int: odmatrix; % origin - destination matrix which can be used to identify the flow
int: totalPAX = sum(odmatrix);

int: Inbound = 1;
int: Outbound = 2;
set of int: DIRECTION = Inbound..Outbound;
array[int, 1..3] of int: links; % link between 2 adjacent stations [origin, destination, distance]
set of int: LINKS = index_set_1of2(links); % set of links
set of int: LINKS0 = 0..card(LINKS);
array[LINKS0, 1..3] of int: links0 = array2d(LINKS0, 1..3, [ if i==0 then 0 else links[i,j] endif | i in LINKS0, j in 1..3]);

array[LINKS] of int: linkCapacity; % Capacity of each link on 1 direction. Presume that capacity is the same for other direction
int: MaxLink = max(linkCapacity); % max number of service running on any link
array[LINKS] of int: linkFlow; % number of passenger travelling on each link - This can be calculated from OD matrix with predefine travelling routes

% Specify if a link is contained in a route. [r,l] = 1 means link l in part of route r and 0 otherwise
array[ROUTES, LINKS] of bool: route_link = array2d(ROUTES, LINKS,[ exists(x in MAXLENGTH)(possibleRoutes[r,x] == l) | r in ROUTES, l in LINKS]);
array[ROUTES, 1..maxRouteLength+1] of 0..nStations: route_station_order = array2d(ROUTES, 1..maxRouteLength+1, 
  [ if l = maxRouteLength+1 then 
      if (possibleRoutes[r,l-1] != 0) then links[possibleRoutes[r,l-1],2] else 0 endif
    else 
      if possibleRoutes[r,l] != 0 then links[possibleRoutes[r,l],1]  
      else 
        if l > 1 /\ possibleRoutes[r,l-1] != 0 then links[possibleRoutes[r,l-1],2] else 0 endif
      endif
    endif
  | r in ROUTES, l in 1..maxRouteLength+1
  ]);
array[ROUTES, STATIONS] of bool: route_station = array2d(ROUTES, STATIONS, [ exists(x in 1..maxRouteLength+1) (route_station_order[r,x] == s) | r in ROUTES, s in STATIONS]);

array[int] of int: trainCapacity; % number of passengers a train can carry. More array item if more trains are used
set of int: TRAINTYPES = index_set(trainCapacity); % set of train type can be used
array[TRAINTYPES] of int: trainCost; % cost of train running 1 meter

array[STATIONS, STATIONS] of int: odDistance = array2d(STATIONS, STATIONS, 
      [
        sum (l in LINKS) (bool2int((links[l,1] == i /\ links[l,2] == j) \/ (links[l,1] == j /\ links[l,2] == i)) * links[l,3])
        |i, j in STATIONS]); % distance between each adjacent pair of staions

%%%%%%%%%%%%% VARIABLE %%%%%%%%%%%%%%%%%%
% number of services of each train type running on each routes on each direction. [t,r] is number of train type t running on route r
array[TRAINTYPES, ROUTES] of var 0..MaxLink: servicePlan;  
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
constraint forall(l in LINKS) (sum(r in ROUTES) (sum(t in TRAINTYPES) (servicePlan[t,r]) * bool2int(route_link[r,l])) <= linkCapacity[l]);
%constraint servicePlan = array2d(TRAINTYPES, ROUTES, [0,0,0,18,0,0,0,12,0,0,4,0,0,0]);
% Constraint 2: The number of services need to cover the flow of passenger on each links
constraint forall(l in LINKS) (sum(t in TRAINTYPES, r in ROUTES) (trainCapacity[t] * servicePlan[t, r] * route_link[r,l]) >= linkFlow[l]);
% % Constraint 3: Number of train of each type start and end at turnback need to be equal
% constraint forall(t in TURNBACKS) 
%   ( forall(tt in TRAINTYPES)
%     (
%       sum(r in ROUTES where possibleRoutes[r,1] == turnbackLocs[t]) (servicePlan[tt, r]) 
%       == 
%       sum(r in ROUTES where possibleRoutes[r,2] == turnbackLocs[t]) (servicePlan[tt, r])
%     )
%   );

%%%%%%%%%%%%% OBJECTIVES CONSTRAINTS %%%%%%%%%%%%%%%%
int: transferWeight;
int: operationWeight;

% Calculate total number of PAX no need transfers
constraint directPAX = sum(o in 1..nStations-1, d in o+1..nStations) (odmatrix[o,d] * bool2int(DirectTravel(o,d))); 
% Calculate total running distance of services. FIXME: this should later include other operational cost ie. fuel, labour, etc.
constraint trainDistance = sum(t in TRAINTYPES, r in ROUTES) (servicePlan[t, r] * trainCost[t] * Distance(r)); 

%%%%%%%%%%%%% FUNCTIONS AND PREDICATE %%%%%%%%%%%
predicate DirectTravel(int: o, int: d) = 
  exists(r in ROUTES) (sum(t in TRAINTYPES) (servicePlan[t, r] > 0 /\ route_station[r,o] /\ route_station[r,d]) > 0);
function int: Distance(int: route) =
  sum(s in possibleRoutes[route,1]..possibleRoutes[route,2]-1) (odDistance[s, s + 1]); % FIXME: this should be more sophiticated based on links instead of station order OR each possible routes include all the stations from start to end of the line. 

%%%%%%%%%%%%% SOLVE PROBLEM %%%%%%%%%%%%%%%%%%%%%
%solve satisfy;
%solve minimize transferWeight * (totalPAX - directPAX) + operationWeight * trainDistance;
solve minimize sum(servicePlan);

%%%%%%%%%%%%% OUTPUT %%%%%%%%%%%%%%%%%%%%%%%%%%%
output 
% -------- TEST PARAMETER ----------
%["OD Distance:\n"] ++ [show(odDistance[i,j]) ++ if j == nStations then "\n" else ", " endif | i, j in STATIONS] ++ % Show distance matrix
%["Route-link:\n"] ++ [show(bool2int(route_link[r,l])) ++ if l == card(LINKS) then "\n" else ", " endif | r in ROUTES, l in LINKS] ++ % show route-link matrix
% ["Possible Route: "] ++ ["(" ++show(possibleRoutes[r,1]) ++ "," ++ show(possibleRoutes[r,2]) ++ "), " | r in ROUTES];
%[if j mod 2 == 1 then show(turnbackLocs[i]) ++ ", " else show(turnbackLocs[j div 2]) ++ ", " endif | i in 1..card(TURNBACKS)-1, j in i*2+1..2*card(TURNBACKS)];
["Route-Station_order:\n"] ++ [show(route_station_order[r,l]) ++ if l == maxRouteLength+1 then "\n" else ", " endif | r in ROUTES, l in 1..maxRouteLength+1] ++ % show route-link matrix

% ------- MODEL OUTPUT -------------
["\nMax Link:" ++ show(MaxLink) ++" \n"] ++
["\nInput flow: \n"] ++ [show(linkFlow[l]) ++ ", " | l in LINKS]++
["\nLink flow: \n"] ++ [show((sum(t in TRAINTYPES, r in ROUTES) (trainCapacity[t] * servicePlan[t, r] * route_link[r,l]))) ++ ", " | l in LINKS] ++
["\nLink usage: \n"] ++ [show(linkCapacity[l]) ++ ", " | l in LINKS] ++
["\nLink usage: \n"] ++ [show((sum(t in TRAINTYPES, r in ROUTES) (servicePlan[t, r] * route_link[r,l]))) ++ ", " | l in LINKS] ++
["\nService plan: \n"] ++ [show(servicePlan[t,r]) ++ "x" ++ "(" ++show(possibleRoutes[r,1]) ++ "," ++ show(possibleRoutes[r,2]) ++ "), " 
  ++ if r == card(ROUTES) then "\n" else "" endif
  | t in TRAINTYPES, r in ROUTES] ++
%["\nObjective value: "] ++ [show(transferWeight*(totalPAX-directPAX) + operationWeight*trainDistance)];
["\nObjective value: "] ++ [show(sum(servicePlan))];