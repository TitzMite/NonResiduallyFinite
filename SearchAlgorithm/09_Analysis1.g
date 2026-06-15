
#returns Radu graph equipped with automorphism group
#that maps triangles to triangles
#this group corresponds to the automorphism group of the triangle complex
#the automorphism group encodes the action on the simplices which
#are ordered by index and label, where the labels are ordered by e<f<g
RaduGraphTriangles := function(triangles)
    local shifted_triangles, rel, aut, gamma, gens, l,m,n, coloring;
    l := Maximum(List(triangles, t->t[1]));
    m := Maximum(List(triangles, t->t[2]));
    n := Maximum(List(triangles, t->t[3]));
    shifted_triangles := List(triangles, t->[t[1],t[2]+l,t[3]+l+m]);
    Sort(shifted_triangles);
    coloring := [[1..l], [l+1..m+l], [m+l+1..l+m+n]];
    rel := function(x,y)
        return (not x=y) and ForAny(shifted_triangles, t->IsSubset(t, [x,y]));
    end;
    gamma := Graph(Group(()), [1..Last(coloring[3])], OnPoints, rel, true);
    aut := AutomorphismGroup(gamma);
    gens := Filtered(aut, a-> OnSetsSets(shifted_triangles, a) = shifted_triangles );
    aut := Group(gens);
    aut := Group(SmallGeneratingSet(aut));
    gamma := NewGroupGraph(aut, gamma);
    return [gamma, coloring, shifted_triangles];
end;

CheckLinks := function(triangles)
    local rg_coloring_cover, rg, coloring, localgeo12, localgeo23, localgeo31, i, c, cons, sub;
    rg_coloring_cover := RaduGraphTriangles(triangles);
    rg := rg_coloring_cover[1];
    coloring := rg_coloring_cover[2];
    localgeo12 := InducedSubgraph(rg, Concatenation(coloring[1], coloring[2]));
    localgeo23 := InducedSubgraph(rg, Concatenation(coloring[2], coloring[3]));
    localgeo31 := InducedSubgraph(rg, Concatenation(coloring[3], coloring[1]));
    cons := ConnectedComponents(localgeo12);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo12, c);
        Print("Link number ", i, " in the local geometry (1,2) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo23);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo23, c);
        Print("Link number ", i, " in the local geometry (2,3) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
    cons := ConnectedComponents(localgeo31);
    for i in [1..Size(cons)] do
        c := cons[i];
        sub := InducedSubgraph(localgeo31, c);
        Print("Link number ", i, " in the local geometry (3,1) has\n");
        Print("order ", OrderGraph(sub), ", girth ", Girth(sub), " and diameter ", Diameter(sub), ".\n\n");
    od;
end;

IsomorphicComplexes := function(triangles1, triangles2)
    local rg_coloring_cover1, rg_coloring_cover2, rg1, rg2, iso, aut1, isos,
    shifted_triangles1, shifted_triangles2;
    rg_coloring_cover1 := RaduGraphTriangles(triangles1);
    rg_coloring_cover2 := RaduGraphTriangles(triangles2);
    rg1 := rg_coloring_cover1[1];
    rg2 := rg_coloring_cover2[1];
    shifted_triangles1 := rg_coloring_cover1[3];
    shifted_triangles2 := rg_coloring_cover2[3];
    iso := GraphIsomorphism(rg1, rg2);
    if iso = fail then
        return false;
    else
        aut1 := AutomorphismGroup(rg1);
        isos := List(aut1, a->a*iso);
        return ForAny(isos, a-> OnSetsSets(shifted_triangles1, a) = shifted_triangles2);
    fi;
end;

