
#GLOBAL VARIABLES FOR SEARCHER
PRINTSEARCH := true;
LOGSEARCH := false;

BestPoint := function(score_function_action, multiplication, point, perms, checked, goodstarters, entry, perfect_score)
    local 
    checkscore, new_goodstarters, n, tau, j, pi, newpoint, score, best, best_score;
    ###
    checkscore := function(pi)
        local local_score;
        if pi in checked then
            return -1;
        else
            local_score := score_function_action(pi);
            return local_score;
        fi;
    end;
    ###
    new_goodstarters := [];
    ###
    best_score := -2;
    n := Size(perms);
    tau := Random(SymmetricGroup(n));
    for j in [1..n] do
        pi := perms[j^tau];
        newpoint := multiplication(point,pi);
        score := checkscore(newpoint);
        if score > entry then
            if ForAll(goodstarters, p-> not p[1] = newpoint) then
                Add(new_goodstarters, [newpoint, score]);
            fi;
        fi;
        if score > best_score then
            best := newpoint;
            best_score := score;
        fi;
    od;
    #
    return [best, best_score, new_goodstarters];
end;

SeperatePermutations := function(perms, number_kernels)
    local number_perms, seperations, packages_of_perms;
    number_perms := Size(perms);
    seperations := List([0..number_kernels-1], i->Int(i*number_perms/(number_kernels)));
    seperations := Concatenation(seperations, [number_perms]);
    packages_of_perms := List([1..number_kernels], i-> perms{[seperations[i]+1..seperations[i+1]]});
    return packages_of_perms;
end;

#this function just reads checked and goodstarters, it does change them
CheckPointParallel := function(score_function_action, multiplication, point, perms, checked, goodstarters, entry, perfect_score, number_kernels)
    local packages_of_perms, worker, best_points, i;
    ###
    packages_of_perms := SeperatePermutations(perms, number_kernels);
    worker := function(i)
        return BestPoint(score_function_action, multiplication, point, packages_of_perms[i], checked, goodstarters, entry, perfect_score);
    end;
    best_points := ParListByFork([1..number_kernels], worker, rec( NumberJobs := number_kernels ) );
    for i in [1..number_kernels] do
        Append(goodstarters, best_points[i][3]);
    od;
    ###
    Exec("clear");
    ###
    i :=  PositionProperty(goodstarters, x-> x[1] = point);
    if not i = fail then
        Remove(goodstarters, i);
    fi;
    ###
    Add(checked, point);
    #####
    best_points := Filtered(best_points, b-> not b[1] in checked);
    ####
    i := PositionMaximum(best_points, b->b[2]);
    return best_points[i]{[1,2]};
end;

FilterGoodStarters := function(score_function_action, goodstarters, entry, levelup)
    local local_entry, local_goodstarters, counter, average;
    local_goodstarters := StructuralCopy(goodstarters);
    counter := 0;
    repeat
        average := Average(List(local_goodstarters, gs -> gs[2]));
        local_entry := Maximum(average + (counter*(2/10)), entry + 2/10);
        local_goodstarters := Filtered(local_goodstarters, gs -> score_function_action(gs[1]) > local_entry-3);
        Print("We filtered the start points, new entry: ", Float(local_entry), ". \n \n");
        counter := counter+1;
    until Size(local_goodstarters) < levelup/2;
    return [local_goodstarters, local_entry];
end;

#Remarks on the Searcher method:
#
#we need a permutation generator, that decides which permutations should be checked
#the permutation generator reads in the geometry and the current point
#if some point are protected this should be reflected in the permutation generator
#
#we need a persistence function that decides if the search schould countinue
#the persistence function reads in a score, the maximal score of the search, the entry
#
#the search returns the original geometry, a permutation and a number (return code)
#
#if the return code is 1 or 2, then the search failed, because it ran out of good starters,
#in this case the returned point is the best point, that was found within this search
#if the return code is 1, this means that search ran out of good points very quickly, i.e.
#it considered less than 2000 points
#if the return code is 2, this means that the search considered more than 2000 points
#
#if the return code is 3 or 4, this means that the search found a point with score
#greater than aim
#if the return code is 4 than the geometry obtained by acting with the point is perfect
#if the return code is 3, the the geometry obtained by acting with the point is not perfect
#
Searcher := function
    (
        geo_datum,
        action_data,
        multiplication,
        score_function,
        metric_on_points,
        perfect_score,
        aim,
        permutation_generator,
        persistence_function,
        start_entry,
        starter,
        levelup,
        limit,
        number_kernels
        #we dont need a number of protected points because this is encoded in permutation_generator
    )
    local
    n, entry, checked, goodstarters, point, score, very_best,
    very_best_score, total_counter, last_maximum_counter, failed, result_code,
    best_neighbour, perms, filter_result, distance, distance_to_best,
    score_function_action, chain;
    ###
    n := geo_datum[1];
    ###
    entry := start_entry;
    ###
    checked := [];
    goodstarters := [];
    ###
    #normal case
    if NumberArgumentsFunction(action_data) = 2 then
        score_function_action := function(point)
            local new_geo_datum, scores;
            new_geo_datum := action_data(geo_datum, point);
            return score_function(new_geo_datum);
        end;
    #if we have special score on perms, e.g. with penalty
    elif NumberArgumentsFunction(action_data) = 1 then
        score_function_action := action_data;
    fi;
    ###
    point := starter;
    score := score_function_action(point);
    distance := 0;
    distance_to_best := 0;
    ###
    very_best := point;
    very_best_score := score;
    ###
    total_counter := 0;
    last_maximum_counter := 0;
    ###
    failed := false;
    ###
    if LOGSEARCH then
        chain := [[point, 1]];
    else
        chain := false;
    fi;
    ###
    while score < aim do
        ###
        if PRINTSEARCH then
            Print("It is ", CurrentDateTimeString(), "\n");
            Print("We checked ", total_counter, " points so far.\n");
            Print("We have ", Size(checked), " blocked points.\n");
            Print("We have ", Size(goodstarters), " potential start points.\n");
            Print("The very best point had a score of ", very_best_score, ".\n");
            Print("It was found ", last_maximum_counter, " points ago.\n");
            Print("Our current point has a score of ", score, ".\n");
            Print("It is at distance ", distance, " from the start point. \n");
            Print("It is at distance ", distance_to_best, " from the best point. \n");
        fi;
        ###
        perms := permutation_generator(geo_datum, point);
        best_neighbour := CheckPointParallel
            (
                score_function_action,
                multiplication,
                point,
                perms,
                checked,
                goodstarters,
                entry,
                perfect_score,
                number_kernels
            );
        checked := SSortedList(checked);
        total_counter := total_counter + 1;
        last_maximum_counter := last_maximum_counter + 1;
        if PRINTSEARCH then
            Print("The best neighbour has a score of ", best_neighbour[2], ".\n\n");
        fi;
        #
        #choosing if next point is best neighbour ore one of the goodstarters
        #
        if persistence_function(best_neighbour[2], very_best_score, entry) then
            point := best_neighbour[1];
            score := best_neighbour[2];
            if LOGSEARCH then
                Add(chain, [point, 1]);
            fi;
            distance := metric_on_points(starter, point);
            distance_to_best := metric_on_points(very_best, point);
            if score > very_best_score then
                very_best := point;
                very_best_score := score;
                last_maximum_counter :=  0;
            fi;
        else
            if not goodstarters = [] then
                point := goodstarters[1][1];
                if LOGSEARCH then
                    Add(chain, [point, 0]);
                fi;
                score := goodstarters[1][2];
                distance := metric_on_points(starter, point);
                distance_to_best := metric_on_points(very_best, point);
            else
                #here just give up
                Print("There no are good starters left.\n");
                Print("The search failed... \n \n");
                if total_counter < 2000 then
                    result_code := 1;
                else
                    result_code := 2;
                fi;
                failed := true;
                break;
            fi;
        fi;
        #
        #sorting good starters every now and then
        #
        if Random([1..17]) mod 17 = 0 then
            SortBy(goodstarters, x->-x[2]);
        fi;
        #
        #if we have too much good starters, we filter them
        #
        if Size(goodstarters) > levelup then
            if last_maximum_counter < 4 then
                filter_result := FilterGoodStarters(score_function_action, goodstarters, entry, levelup/3);
            else
                filter_result := FilterGoodStarters(score_function_action, goodstarters, entry, levelup);
            fi;
            goodstarters := StructuralCopy(filter_result[1]);
            entry := filter_result[2];
        fi;
        #
        #if we have too much blocked points, we filter them
        #
        if Size(checked) > 10000 then
            Print("We checked 10000 points, we filter the checked points now...\n\n");
            SortBy(checked, x->-score_function_action(x));
            checked := checked{[1..1000]};
        fi;
        #
        #if there was now new maximum for some time we give up
        #
        if last_maximum_counter > limit then
            Print("We did not find a better point for a long time. We give up now...\n");
            Print("The search failed... \n \n");
            result_code := 2;
            failed := true;
            break;
        fi;
    od;
    if failed then
        return [geo_datum, very_best, result_code, chain];
    else
        if score = perfect_score then
            return [geo_datum, point, 4, chain];
        else
            return [geo_datum, point, 3, chain];
        fi;
    fi;
end;
