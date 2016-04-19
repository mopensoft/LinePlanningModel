%%%%%%%%%%%%%% DESCRIPTION %%%%%%%%%%%%%%
/*
This model schedule time for train trips based on provided service plan.
Input:
- Network: stations and links
- planned period (time)
- routes and frequencies
Output:
- Schedule individual trips
- Connect trips to identify rolling stock requirement
*/

%%%%%%%%%%%%%% PARAMETER %%%%%%%%%%%%%%%%
int: operationTime; % total number of minutes in planned time. ie. 120 = 2h
set of int: DURATION = 1..operationTime;
int: timedStation;  
int: nStations;
set of int: STATIONS = 1..nStations;
array[int, 1..3] of int: links;
set of int: LINKS = index_set_1of2(links);
set of int: LINKS0 = 0..card(LINKS);
array[LINKS] of int: linkHeadway; 

int: maxRouteLength; % max length of a route. This is used to define route path as an array
set of int: MAXLENGTH = 1..maxRouteLength;
array[int, MAXLENGTH] of LINKS0: routes; % routes[i, j] is link j of route i. If route length less than maxRouteLength, route[i,j] = 0 for all j>max
set of int: ROUTES = index_set_1of2(routes);
array[ROUTES] of int: frequencies;

int: nTrips = sum(r in ROUTES) (frequencies[r]); % total number of trips to schedule
set of int: TRIPS = 1..nTrips;
% array to identify if a link is in a trip
array[TRIPS, LINKS] of bool: tripLink = array2d(TRIPS, LINKS, [ exists(x in MAXLENGTH) (routes[r,x] == l) | r in ROUTES, t in 1..frequencies[r], l in LINKS]); 
% array to identify order of links in each trip
array[TRIPS, MAXLENGTH] of LINKS0: tripRoute = array2d(TRIPS, MAXLENGTH, [ routes[r, l] | r in ROUTES, t in 1..frequencies[r], l in MAXLENGTH]);

int: minTurnback; % minimum minutes required to turn back train

%%%%%%%%%%%%% VARIABLE %%%%%%%%%%%%%%%%%%
array[TRIPS, LINKS] of var DURATION: sched; % the start time of trip on each link
array[TRIPS, MAXLENGTH] of var 0..operationTime: tripTime; % start time of each link in a trip
array[TRIPS] of var TRIPS: nextTrip; % keep trip connection e.g. nextTrip[i] is the next trip form by trip i.

%%%%%%%%%%%%% CONSTRAINTS %%%%%%%%%%%%%%%
% input validation constraints (LATER)
% link time is in time order
constraint forall(t in TRIPS, i in 1..maxRouteLength-1 where tripRoute[t,i+1] != 0) 
              (sched[t,tripRoute[t,i+1]] == sched[t,tripRoute[t,i]] + links[tripRoute[t,i],3]);

% headway and overlap contraint on each link
constraint forall(t1, t2 in TRIPS where t1 != t2) (
  forall(l in LINKS where tripLink[t1,l] /\ tripLink[t2,l]) (abs(sched[t1,l] - sched[t2,l]) > linkHeadway[l]) 
);

% trip time
constraint forall(t in TRIPS, i in MAXLENGTH) (if tripRoute[t,i] != 0 then tripTime[t,i] = sched[t, tripRoute[t,i]] else tripTime[t,i] = 0 endif);

% connection constraint: to connect train that start and end at same station where start > end + minTurnback. Policy FIFO

%%%%%%%%%%%%% OBJECTIVES CONSTRAINTS %%%%%%%%%%%%%%%%
% count number of rolling stock required

%%%%%%%%%%%%% FUNCTIONS AND PREDICATE %%%%%%%%%%%
function string: int2time(var int: minutes) = show(minutes div 60) ++ ":" ++ show(minutes mod 60) ++ ":00";

%%%%%%%%%%%%% SOLVE PROBLEM %%%%%%%%%%%%%%%%%%%%%
solve satisfy;

%%%%%%%%%%%%% OUTPUT %%%%%%%%%%%%%%%%%%%%%%%%%%%
output
["Trip link:\n"] ++ [format(5,j) ++ "  " | j in LINKS] ++ ["\n"] 
++ [format(5, tripLink[i,j]) ++ if j == card(LINKS) then "\n" else ", " endif | i in TRIPS, j in LINKS] 
++ ["Trip path: \n"]
++ [format(4, tripRoute[t, i]) ++ if i == maxRouteLength then "\n" else "" endif | t in TRIPS, i in MAXLENGTH]
++ ["Trip time: \n"]
++ [format(4, tripTime[t, i]) ++ if i == maxRouteLength then "\n" else "" endif | t in TRIPS, i in MAXLENGTH];
% ++ % print XML output
% ["<timetable>\n"] ++
% % Print stations
% ["<stations>\n"] ++
% ["\t<station id = \"" ++ show(i) ++ "\" name = \"S" ++ show(i) ++ "\"/>\n" | i in STATIONS] ++
% ["</stations>\n"] ++
% % Print links
% ["<links>\n"] ++
% ["\t<link id=\"" ++ show(i) ++ "\" source=\"" ++ show(links[i,1]) ++ "\" target=\"" ++ show(links[i,2]) ++ "\" traveltime=\"" ++ show(links[i,3]) ++ "\" />\n" | i in LINKS] ++
% ["</links>\n"] ++
% ["<trains>\n"] ++ 
% % Print Passenger trains
% ["\t<train id=\"P1\">\n"] 
% ++ 
% [  if tripRoute[i,j] != 0 then
%      "\t\t<stop sid=\"" ++ show(links[tripRoute[i,j],1]) ++ "\""
%      ++ " arrival=\"" ++ int2time(tripTime[i,j]) ++ "\""
%      ++ " departure=\"" ++ int2time(tripTime[i,j]) ++ "\""
%      ++ " platform=\"1\"/>\n" 
%      ++ if (j == maxRouteLength) then 
%           "\t\t<stop sid=\"" ++ show(links[tripRoute[i,j],2]) ++ "\""
%            ++ " arrival=\"" ++ int2time(tripTime[i,j]) ++ "\""
%            ++ " departure=\"" ++ int2time(tripTime[i,j] + links[tripRoute[i,j],3]) ++ "\""
%            ++ " platform=\"1\"/>\n" 
%            ++ "\t</train>\n"
%            ++ if i < card(TRIPS) then
%                 "\t<train id=\"P" ++ show(i+1) ++ ">\n" 
%               else ""
%               endif
%         else 
%            "" 
%         endif 
%     else 
%       if tripRoute[i,j-1] != 0 then
%           "\t\t<stop sid=\"" ++ show(links[tripRoute[i,j],2]) ++ "\""
%            ++ " arrival=\"" ++ int2time(tripTime[i,j]) ++ "\""
%            ++ " departure=\"" ++ int2time(tripTime[i,j] + links[tripRoute[i,j],3]) ++ "\""
%            ++ " platform=\"1\"/>\n" 
%            ++ "\t</train>\n"
%            ++ if i < card(TRIPS) then
%                 "\t<train id=\"P" ++ show(i+1) ++ ">\n" 
%               else ""
%               endif
%       else ""
%       endif
%     endif
%     | i in TRIPS, j in MAXLENGTH] 
% ++
% ["</trains>\n"] ++
% ["</timetable>"];