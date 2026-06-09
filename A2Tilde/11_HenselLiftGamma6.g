#https://math.stackexchange.com/questions/4381402/how-do-i-force-gap-give-me-a-true-random-number
Reset(GlobalMersenneTwister,CurrentDateTimeString());;

F := FreeGroup(
    "e1", "e2", "e3", "e4", "e5", "e6", "e7",
    "f1", "f2", "f3", "f4", "f5", "f6", "f7",
    "g1", "g2", "g3", "g4", "g5", "g6", "g7"
);

AssignGeneratorVariables(F);

rels := [
    #triangles
    e1*f1*g2, e1*f2*g1, e1*f3*g3, e2*f1*g1, e2*f4*g4, e2*f5*g5, e3*f1*g4,
    e3*f6*g2, e3*f7*g6, e4*f2*g6, e4*f4*g3, e4*f6*g5, e5*f2*g7, e5*f5*g4,
    e5*f7*g3, e6*f3*g5, e6*f4*g7, e6*f7*g2, e7*f3*g1, e7*f5*g6, e7*f6*g7,
    #maximal tree
    e4, g7,
    # #images under involution
    # e1 <-> g1^-1,
    # e2 <-> g2^-1,
    # e3 <-> g4^-1,
    # e5 <-> g6^-1,
    # e6 <-> g5^-1,
    # e7 <-> g3^-1,
    # f1 <-> f1^-1,
    # f2 <-> f2^-1,
    # f3 <-> f3^-1,
    # f4 <-> f6^-1,
    # f5 <-> f7^-1
    # images under C3 action
    # e1 -> e2 -> e3 -> e1
    # e4 -> e4
    # e5 -> e6 -> e7 -> e5
    # f1 -> f1
    # f2 -> f4 -> f6 -> f2
    # f3 -> f5 -> f5 -> f3
    # g1 -> g4 -> g2 -> g1
    # g3 -> g5 -> g6 -> g3
    # g7 -> g7
    ];

gamma6_all_gens := F/rels;

#e3 and g4^-1 are conjugate by the involution in the extension
gamma6 := Group(gamma6_all_gens.3, gamma6_all_gens.18^-1);

psi:= IsomorphismFpGroupByGenerators(gamma6, GeneratorsOfGroup(gamma6));

Tietzes := List(RelatorsOfFpGroup(Image(psi)), rel -> TietzeWordAbstractWord(rel, FreeGeneratorsOfFpGroup(Image(psi))));

################

#A3_mat and B3_mat are images under an epimorphism to SU(3,3)

A3_mat := 
    [
        [ Z(3), Z(3), Z(3) ], [ 0*Z(3), Z(3)^0, Z(3)^0 ], [ 0*Z(3), 0*Z(3), Z(3) ]
    ];

B3_mat :=
    [
        [ Z(3), Z(3)^0, Z(3) ], [ Z(3), 0*Z(3), 0*Z(3) ], [ Z(3)^0, Z(3)^0, 0*Z(3) ] 
    ];

phi3 := GroupHomomorphismByImages(gamma6, Group([A3_mat,B3_mat]));

################################################
################################################

polys := Concatenation(
    Cartesian([1],[-160..160]*(1/16), [-160..160]*(1/16)),
    Cartesian([0],[1],[-160..160]*(1/16)));

SplitsOverQ := function(p)
    local a, b, c, D, n, d;
    a := p[1];
    b := p[2];
    c := p[3];
    if a = 0 then
        return false;
    fi;
    D := b^2 - 4*a*c;
    n := NumeratorRat(D);
    d := DenominatorRat(D);
    return n >= 0 and IsSquareInt(n) and IsSquareInt(d);
end;

polys := Filtered(polys, p->SplitsOverQ(p) = false);

MinimalPolys := function(elm)
    local a, b, k, n,x, p, goods;
    n := Size(DefaultRing(elm));
    if n<2 then
        n := Size(DefaultField(elm));
    fi;
    goods := Filtered(polys, p->(p[1]*elm^2+p[2]*elm+p[3]) = 0*elm);
    return goods;
end;

################################################
################################################

LiftsElement := function(elm)
    local n, p, x, lifts;
    n := Size(DefaultRing(elm));
    if n<2 then
        n := Size(DefaultField(elm));
    fi;
    p := Factors(n)[1];
    if elm = 0*elm then
        x := 0;
    else
        x := Int(elm);
    fi;
    lifts := List([0..p-1], i->ZmodnZObj(x+n*i, n*p));
    return lifts;
end;

LiftMatrix := function(mat)
    local l11, l12, l13, l21, l22, l23, l31, l32, l33,
    a11, a12, a13, a21, a22, a23, a31, a32, a33,
    lifts, M;
    l11 := LiftsElement(mat[1][1]);
    l12 := LiftsElement(mat[1][2]);
    l13 := LiftsElement(mat[1][3]);
    l21 := LiftsElement(mat[2][1]);
    l22 := LiftsElement(mat[2][2]);
    l23 := LiftsElement(mat[2][3]);
    l31 := LiftsElement(mat[3][1]);
    l32 := LiftsElement(mat[3][2]);
    l33 := LiftsElement(mat[3][3]);
    lifts := [];
    for a11 in l11 do
        for a12 in l12 do
            for a13 in l13 do
                for a21 in l21 do
                    for a22 in l22 do
                        for a23 in l23 do
                            for a31 in l31 do
                                for a32 in l32 do
                                    for a33 in l33 do
                                        M := [
                                            [a11, a12, a13],
                                            [a21, a22, a23],
                                            [a31, a32, a33]
                                        ];
                                        Add(lifts, M);
                                    od;
                                od;
                            od;
                        od;
                    od;
                od;
            od;
        od;
    od;
    return SSortedList(lifts);
end;

#criteria for a lifted pair
CheckTietzeRelations := function(a, b)
    local prod, rel, admissible, x, r;
    r := DefaultRing(a[1][1]);
    if Size(r) < 2 then
        r := DefaultField(a[1][1]);
    fi;
    admissible := true;
    for rel in Tietzes do
        prod := DiagonalMat([One(r),One(r),One(r)]);
        for x in rel do
            if x = 1 then
                prod := prod * a;
            elif x = -1 then
                prod := prod * a^-1;
            elif x = 2 then
                prod := prod * b;
            elif x = -2 then
                prod := prod * b^-1;
            fi;
        od;
        admissible := DiagonalMat([One(r),One(r),One(r)]) = prod;
        if admissible = false then
            return admissible;
        fi;
    od;
    return admissible;
end;

#checked until here

###########################

GoodTrace:=function(m)
    local tr;
    tr := Trace(m);
    if tr = 0*tr then
        return false;
    else
        return tr - One(DefaultRing(tr))/2 = 0*tr;
    fi;
end;

IsGoodLift := function(x)
    return
    IsUnit(Determinant(x))
    and
    Determinant(x) = Determinant(x)^0
    and
    GoodTrace(x);
end;

InvariantMat := function(m)
    return (Trace(m)^2 - Trace(m^2))/2;
end;

#run LiftPair(A3_mat, B3_mat)

LiftPair := function(a, b)
    local liftsa, liftsb, pairs, x,y,z, pi, i, n, j, m, tau, minpols;
    Print("Lifting a pair...\n\n");
    liftsa := LiftMatrix(a);
    liftsa := Filtered(liftsa, IsGoodLift);
    Print("We have ", Size(liftsa), " potential left lifts.\n\n");
    if liftsa = [] then
        Print("checked all pairs...\n\n");
        Print("\n-----------------\n\n");
        return 0;
    else
        liftsb := LiftMatrix(b);
        liftsb := Filtered(liftsb, IsGoodLift);
        Print("We have ", Size(liftsb), " potential right lifts.\n\n");
        pairs := [];
        n := Size(liftsa);
        pi := Random(SymmetricGroup(n));
        m := Size(liftsb);
        tau := Random(SymmetricGroup(m));
        for i in [1..n] do
            x := liftsa[i^pi];
            for j in [1..m] do
                y := liftsb[j^tau];
                if CheckTietzeRelations(x,y) then
                    Print("We found an admissible pair:\n");
                    Print("\n");
                    Print("Matrix A:\n");
                    Display(x);
                    Print("\n");
                    Print("Matrix B:\n");
                    Display(y);
                    Print("\n");
                    minpols := MinimalPolys(Trace(x));
                    if Size(minpols) = 1 then
                        Print("Trace of A is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(InvariantMat(x));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("The coefficient of the linear term in the\ncharacteristic polynomial of A is probably a root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(y));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of B is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(x*y));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of AB is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(x^2*y));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of AAB is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(y^2));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of B^2 is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(x*y^2));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of AB^2 is probably root of ", minpols[1],".\n");
                    fi;
                    minpols := MinimalPolys(Trace(x^2*y^2));
                    if Size(minpols) = 1 then
                        Print("\n");
                        Print("Trace of A^2B^2 is probably root of ", minpols[1],".\n");
                    fi;
                    Print("\n");
                    z := LiftPair(x,y);
                    if z=0 then
                        break;
                    fi;
                fi;
            od;
        od;
        Print("checked all pairs...\n\n");
        Print("\n-----------------\n\n");
        return 1;
    fi;
end;