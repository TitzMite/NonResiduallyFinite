
#the following data and functions are to compute the normal closure of bar delta^4

wp_data := ComputeDataWordProblem(y21);
reductions := wp_data[1];
turns := wp_data[2];
alternative_turns := wp_data[3];
invo := (3,6)(5,8)(7,9)(12,14);
#these are the normal forms of bar delta^4 and its inverse
nrf := [ 1, 3, 4, 6, 1, 3, 4, 6 ];
nrf_inv := [ 3, 4, 6, 1, 3, 4, 6, 1 ];

n0 := nrf;
#n1 = n0*w1*n0*w1^-1
w1 := [2,11];
w1_inv := List(Reversed(w1), x->x^invo);
n1 := [ 1, 3, 4, 13, 4, 2, 6, 11, 3, 1, 9, 6, 11, 2 ];
n1_inv := List(Reversed(n1), x->x^invo);
#
#n2 = w2*n1*w2^-1
w2 := [ 3, 6, 12, 7, 11, 2 ];
w2_inv := List(Reversed(w2), x->x^invo);
n2 := [ 7, 10, 15, 7, 6, 13, 3, 4, 6, 11, 3, 14, 13, 2 ];
#
#n3 = w3*n1^-1*w3^-1
w3 := [ 3, 2, 6, 6, 14, 5, 12, 6, 11, 9, 3, 14, 13, 2, 11, 15, 14, 8, 13, 5, 12, 5, 14, 4, 3, 1 ];
w3_inv := List(Reversed(w3), x->x^invo);
n3 := [ 1, 4, 14, 2, 8, 8, 10, 15, 8, 7, 12, 5, 3, 15 ];
#
#n4 = n2*n3
n4 := [ 7, 6, 13, 15, 7, 13, 9, 5, 4, 15 ];
#
#n5 = w4*n4*w4^-1
w4 := [ 1, 12, 5, 15, 1, 12, 5, 12, 11, 2, 10, 7, 2, 11, 9, 14, 8, 12, 8, 9, 11, 15, 14, 4, 2, 6, 7, 1, 12, 5, 15, 11, 9 ];
w4_inv := List(Reversed(w4), x->x^invo);
n5 := [ 7, 14, 7, 6, 9, 12, 13, 5, 3, 1 ];
#
#n6 =  w5*n4*w5^-1
w5 := [ 1, 3, 5, 13, 4, 5, 11, 12, 10, 11, 2, 10, 7, 2, 11, 9, 14, 8, 12, 8, 9, 11, 15, 14, 4, 2, 6, 7, 1, 12, 5, 15, 11, 9 ];
w5_inv := List(Reversed(w5), x->x^invo);
n6 := [ 1, 11, 12, 9, 1, 10, 11, 3, 2, 4 ];
#n5*n6
short := [ 7, 4 ];

short_but_long := Concatenation(
        w4, w2, nrf, w1, nrf, w1_inv, w2_inv, w3, w1, nrf_inv, w1_inv, nrf_inv, w3_inv, w4_inv,
        w5, w2, nrf, w1, nrf, w1_inv, w2_inv, w3, w1, nrf_inv, w1_inv, nrf_inv, w3_inv, w5_inv
    );

##########

count_operations := function()
    local n0, n1, n1_inv, n2, n3, n4, n5, n6, n7,
    w1, w1_inv, w2, w2_inv, w3, w3_inv, w4, w4_inv, w5, w5_inv,
    counter, first_computation, second_computation, third_computation, fourth_computation,
    fifth_computation, sixth_computation, seventh_computation;
    counter := [0,0,0];
    n0 := nrf;
    w1 := [2,11];
    w1_inv := List(Reversed(w1), x->x^invo);
    ###
    first_computation := NormalForm_WithCounting(y21, Concatenation(n0, w1, nrf, w1_inv));
    n1 := first_computation[1];
    n1_inv := List(Reversed(n1), x->x^invo);
    counter := counter+first_computation{[2,3,4]};
    Print("n1 = ", n1, "\n");
    Print("calculations in last step: ", first_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ###
    w2 := [ 3, 6, 12, 7, 11, 2 ];
    w2_inv := List(Reversed(w2), x->x^invo);
    second_computation := NormalForm_WithCounting(y21, Concatenation(w2, n1, w2_inv));
    n2 := second_computation[1];
    counter := counter+second_computation{[2,3,4]};
    Print("n2 = ", n2, "\n");
    Print("calculations in last step: ", second_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ###
    w3 := [ 3, 2, 6, 6, 14, 5, 12, 6, 11, 9, 3, 14, 13, 2, 11, 15, 14, 8, 13, 5, 12, 5, 14, 4, 3, 1 ];
    w3_inv := List(Reversed(w3), x->x^invo);
    third_computation := NormalForm_WithCounting(y21, Concatenation(w3, n1_inv, w3_inv));
    n3 := third_computation[1];
    counter := counter+third_computation{[2,3,4]};
    Print("n3 = ", n3, "\n");
    Print("calculations  in last step: ", third_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ###
    fourth_computation := NormalForm_WithCounting(y21, Concatenation(n2, n3));
    n4 := fourth_computation[1];
    counter := counter+fourth_computation{[2,3,4]};
    Print("n4 = ", n4, "\n");
    Print("calculations  in last step: ", fourth_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ###
    w4 := [ 1, 12, 5, 15, 1, 12, 5, 12, 11, 2, 10, 7, 2, 11, 9, 14, 8, 12, 8, 9, 11, 15, 14, 4, 2, 6, 7, 1, 12, 5, 15, 11, 9 ];
    w4_inv := List(Reversed(w4), x->x^invo);
    fifth_computation := NormalForm_WithCounting(y21, Concatenation(w4, n4, w4_inv));
    n5 := fifth_computation[1];
    counter := counter+fifth_computation{[2,3,4]};
    Print("n5 = ", n5, "\n");
    Print("calculations  in last step: ", fifth_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ###
    w5 := [ 1, 3, 5, 13, 4, 5, 11, 12, 10, 11, 2, 10, 7, 2, 11, 9, 14, 8, 12, 8, 9, 11, 15, 14, 4, 2, 6, 7, 1, 12, 5, 15, 11, 9 ];
    w5_inv := List(Reversed(w5), x->x^invo);
    sixth_computation := NormalForm_WithCounting(y21, Concatenation(w5, n4, w5_inv));
    n6 := sixth_computation[1];
    counter := counter+sixth_computation{[2,3,4]};
    Print("n6 = ", n6, "\n");
    Print("calculations  in last step: ", sixth_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
    ####
    seventh_computation := NormalForm_WithCounting(y21, Concatenation(n5, n6));
    n7 := seventh_computation[1];
    counter := counter+seventh_computation{[2,3,4]};
    Print("n7 = ", n7, "\n");
    Print("calculations  in last step: ", seventh_computation{[2,3,4]}, "\n");
    Print("calculations in total: ", counter, "\n\n");
end;

#the data encodes the elements known to lie in the finite residual of the groups for q=3
nrf_q3_1 := [1, -14, 1, -12, 3, -12, 3, -1, 14, -1, 12, -3, 12, -3];
nrf_q3_2 := [3, -12, 3, -14, 1, -14, 1, -3, 12, -3, 14, -1, 14, -1];

VerifyClaims := function()
    local rws, quotient, cover_q31, cover_q32, cover_q33, cover_q34, radu_graphs, combis, norm;
    #
    Print("starting verification at ", CurrentDateTimeString(), "\n");
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (1):\n\n");
    Print("Complex Y_1^2:\n\n");
    CheckLinks(y21);
    Print("Complex Y_1^3:\n\n");
    CheckLinks(y31);
    Print("Complex Y_2^3:\n\n");
    CheckLinks(y32);
    Print("Complex Y_3^3:\n\n");
    CheckLinks(y33);
    Print("Complex Y_4^3:\n\n");
    CheckLinks(y34);
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (2):\n\n");
    Print("Presentation q=2:\n");
    CorrectPresentation(y21,bar_gamma21);
    Print("Presentation q=3, i=1:\n");
    CorrectPresentation(y31,bar_gamma31);
    Print("Presentation q=3, i=2:\n");
    CorrectPresentation(y32,bar_gamma32);
    Print("Presentation q=3, i=3:\n");
    CorrectPresentation(y33,bar_gamma33);
    Print("Presentation q=3, i=4:\n");
    CorrectPresentation(y34,bar_gamma34);
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (3):\n\n");
    count_operations();
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (4):\n\n");
    Print("Cayley balls for q=2:\n");
    DiscretenessCheckThickness3(y21);
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (5):\n\n");
    Print("Cayley balls for q=3, i=1:\n");
    DiscretenessCheckThickness4(y31);
    Print("Cayley balls for q=3, i=2:\n");
    DiscretenessCheckThickness4(y32);
    Print("Cayley balls for q=3, i=3:\n");
    DiscretenessCheckThickness4(y33);
    Print("Cayley balls for q=3, i=4:\n");
    DiscretenessCheckThickness4(y34);
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    # 
    Print("Verifying (6):\n\n");
    quotient := f40/List(Concatenation(shared_tietzes, remaining_tietzes_bar_gamma31, [nrf_q3_1, nrf_q3_2]), t->AbstractWordTietzeWord(t, GeneratorsOfGroup(f40)));
    rws := KBMAGRewritingSystem(quotient);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws);
    oprec.maxeqns := 2 ^ 22 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    KnuthBendix(rws);
    Print("The index of the finite residual in bar gamma for q=3, i=1 is: ", Size(rws) ,".\n");
    quotient := f40/List(Concatenation(shared_tietzes, remaining_tietzes_bar_gamma32, [nrf_q3_1, nrf_q3_2]), t->AbstractWordTietzeWord(t, GeneratorsOfGroup(f40)));
    rws := KBMAGRewritingSystem(quotient);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws);
    oprec.maxeqns := 2 ^ 22 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    KnuthBendix(rws);
    Print("The index of the finite residual in bar gamma for q=3, i=2 is: ", Size(rws) ,".\n");
    quotient := f40/List(Concatenation(shared_tietzes, remaining_tietzes_bar_gamma33, [nrf_q3_1, nrf_q3_2]), t->AbstractWordTietzeWord(t, GeneratorsOfGroup(f40)));
    rws := KBMAGRewritingSystem(quotient);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws);
    oprec.maxeqns := 2 ^ 22 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    KnuthBendix(rws);
    Print("The index of the finite residual in bar gamma for q=3, i=3 is: ", Size(rws) ,".\n");
    quotient := f40/List(Concatenation(shared_tietzes, remaining_tietzes_bar_gamma34, [nrf_q3_1, nrf_q3_2]), t->AbstractWordTietzeWord(t, GeneratorsOfGroup(f40)));
    rws := KBMAGRewritingSystem(quotient);
    oprec := OptionsRecordOfKBMAGRewritingSystem( rws);
    oprec.maxeqns := 2 ^ 22 - 1;
    oprec.confnum := 5000;
    oprec.tidyint := 2000;
    KnuthBendix(rws);
    Print("The index of the finite residual in bar gamma for q=3, i=4 is: ", Size(rws) ,".\n");
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    # 
    Print("Verifying (7):\n\n");
    cover_q31 := ConstructRaduGraphCover(y31, [nrf_q3_1, nrf_q3_2]);
    cover_q32 := ConstructRaduGraphCover(y32, [nrf_q3_2, nrf_q3_2]);
    cover_q33 := ConstructRaduGraphCover(y33, [nrf_q3_1, nrf_q3_2]);
    cover_q34 := ConstructRaduGraphCover(y34, [nrf_q3_1, nrf_q3_2]);
    radu_graphs := [cover_q31[1],cover_q32[1],cover_q33[1],cover_q34[1]];
    combis := Combinations([1..4],2);
    if ForAll(combis, c-> GraphIsomorphism(radu_graphs[c[1]], radu_graphs[c[2]]) = fail) then
        Print("The buildings for q=3 are pairwise not isomorphic.\n");
    else
        Print("The verification failed.\n");
    fi;
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("Verifying (8):\n\n");
    norm := compute_norm_of_error();
    Print("The norm of the error is ", norm, "\n\n");
    # 
    Print("\n\n----------------------------------------\n\n");
    # 
    Print("verification finished at ", CurrentDateTimeString(), "\n");
end;

