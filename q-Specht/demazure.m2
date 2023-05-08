-- In the following we try to produce a q-variant version of the Specht Polynomials.
-- First we would want to compute the demazure operators and all of their possible combinations.
-- We do this by producing a hashmap that relates permutations to their demazure.
-- Start by producing the demazure from (i,i+1) then  iterate for all permuations.

------------------------------------------------------------------------------------

--- We first create a correspondence between Permutations and Reduced words




restart
loadPackage "WeylGroups"    -- Package for computations in the WeylGroup
loadPackage "SpechtModule"  -- Package for computing young Tabeleaux Constructions
loadPackage "InvariantRing" -- Package for computations involving invariants of group actions
loadPackage "pushFWDbasis"   -- Package for computing pushforward


-- Push Forward Function to check if we indeed obtain a basis
  


-- length of reduced word of a given permutation:
cLen := (l) -> (
    len := 0;
    if #l==1 then return len;
    for i from 0 to #l-2 do (
	for j from i+1 to #l-1 do (
	    if l_i > l_j then len=len+1;
	    );
	);
    return len;
    )

-- Descent of a permutation:
descent := (l) -> (
    dec := {};
    if #l<=1 then return dec;
    for i from 0 to #l-2 do (
	if l_i > l_(i+1) then dec=append(dec,i);
	);
    return dec;
    )
        
-- Transposition (i,i+1) in Sn
s := (i,n) -> (
    perm := {};
    for j from 0 to n-1 do (
	if (j<i or j>i+1) then perm = append(perm,j);
	if j==i then perm = append(perm,j+1);
	if j==i+1 then perm = append(perm,j-1);
	);
    return perm;
    )


-- reduced word given as a list of indices of transpositions
red := (p) -> (
    N := #p;
    D := descent(p);
    reduced := {};
    while cLen(p) > 0 do (
	for i in D do (
	    if cLen(p_(s(i,N))) < cLen(p) then (
		p = p_(s(i,N));
		reduced = append(reduced,i);
		D = descent(p);
		break;
		);
	    );
	);
    return reverse reduced;
    )
    

-- divided difference operator
del := (f,i) -> (
    R := ring f;
    x := gens R;
    g := permutePolynomial(s(i,#x),f);
    return (f-g)//(x_i-x_(i+1));
    )

-- action of Ti in the polynomial ring
act := (q,f,i) -> (
    R := ring f;
    x :=gens R;
    return(del(x_i*f,i)-q*x_i*del(f,i));
    )

-- the action defined for any permutation given its reduced word T_p = T_i_1...T_i_k
Hecke := (q,f,p) -> (
    g := f;
    desc = reverse red p;
    for i in desc do (
	g = act(q,g,i);
	);
    return g;
    )


------ Some Tableaux functions

-- Conjugate of a Tableaux
conjTab := (tab) -> (
    if (#tab == 0) then (return tab);
    entrie := flatten toList apply(0..numColumns(tab)-1,i->tab_i);
    listPar := apply(0..numColumns(tab)-1, i->#tab_i);
    par := new Partition from listPar;
    tab := youngTableau(par,entrie);
    sortColumnsTableau youngTableau(par,entrie);
    return tab
    )

-- Partition from a Tableaux
parFromTab := (tab) -> (
    if (#tab == 0) then (return {});
    listPar = apply(0..numRows(tab)-1, i->#tab^i);
    return (new Partition from listPar);
    )

-- q-row stabilizer defined in dipper and james
qRowStabilizer := (q,tab) -> (
    N := size tab;
    rT = rowStabilizer(tab);
    appList = {};
    for r in rT do (
	appList = append(appList,{1,r});
	);
    return appList;
    )

-- q-column stabilizer defined in dipper and james
qColStabilizer := (q,tab) -> (
    N := size tab;
    cT := columnStabilizer(tab);
    appList := {};
    l := 0;
    mu := max apply(cT,cLen);
    mi := min apply(cT,cLen);
    for c in cT do (
	l = cLen(c);
	appList = append(appList,{(-1)^(-l)*(q)^(-l+mu-mi),c});
	);
    return appList;
    )

-- given a partition l this calculates the longest element in S_l
longestElement := (tab) -> (
    ctab := conjTab tab;
    w1 := readingWord(tab);
    w2 := readingWord(ctab);
    return (inversePermutation(w1))_w2;
    );

-- q-version of the young symmetrizer also from dipper and james
qYoungSym := (q,tab,pol) -> (
     qRT := qRowStabilizer(q,tab);
     qCT := qColStabilizer(q,tab);
     wtab := longestElement tab;
     qYS := {};
     for R in qRT do (
	 for C in qCT do (
	     qYS = append(qYS,{C_0,R_1,C_1});
	     );
	 );
     SUM := apply(qYS, E -> E_0*Hecke(q,Hecke(q,pol,E_1),E_2));
     return sum SUM;
     )
 
-- Specht Polynomials
qSpechtPolynomial := (q,tab1,tab2,rng) -> (
      mon := indexMonomial(tab2,tab1,rng);
      hsp := qYoungSym(q,tab1,mon);
      coef := apply(flatten entries (coefficients hsp)_1,i-> (map(baseRing ring i,ring i)) i);
      coefgcd := gcd apply(coef,numerator);
      coefgcdFrac := (map(baseRing rng,ring coefgcd)) coefgcd;
      return hsp*(1/coefgcdFrac);
      )
  
qSpechtFromPartition = (q,tab,rng) -> (
    par := parFromTab(tab);
    stTab := toListOfTableaux standardTableaux(par);
    return apply(stTab, i-> qSpechtPolynomial(q,i,tab,rng));
    )

qSpechtPolynomialSet = (q,rng) -> (
    n := numgens rng;
    return flatten  apply(flatten apply(partitions n, i ->  (toListOfTableaux standardTableaux i)), i -> qSpechtFromPartition(q,i,rng));
    )


-- Testing
eleSym = (var) -> (
    n := #var;
    elem := toList apply(1..n, i->(sum(apply(subsets(1..n,i), j -> (times(toSequence apply(j, k -> var_(k-1))))))));   
    return elem;
    )

Sn = (rng) -> (
    x := gens rng;
    kk := coefficientRing rng;
    n := numgens rng;
    Tgens := (eleSym(gens rng))_{0..(n-1)};
    print(apply(Tgens,ring));
    T := kk[f_1..f_n,Degrees => {1..n}];
    TtoS := map(rng,T,Tgens);
    return (T,TtoS,Tgens))

n = 4;
rng = frac(QQ[p]);
Field = QQ;
R = rng[x_1..x_n];
H = Field[x_1..x_n];
q = -1/2; 



hspSet = qSpechtPolynomialSet(q,H);
qBasis = matrix {hspSet};

HSPset = apply(toList(0..n-2), i-> apply(hspSet, f -> act(q,f,i))); 
QBasis = apply(HSPset, B -> matrix{B});


(T,TtoR,Tgens) = Sn H
phi = map(H^1,H^1,{{1}})
PushFWD(TtoR,phi,qBasis,qBasis)

tau = apply(QBasis, B-> (map(rng,T)) PushFWD(TtoR,phi,qBasis,B));




---------------------------------------------------------------------------------------

qmap = map(H,R,flatten join(entries vars H,{1})) -- set the number in brackets to the new 'q'-value
hspSetH = apply(hspSet,i-> qmap i)


qBasis = matrix {hspSetH}

(T,TtoR,Tgens) = Sn(H)
phi = map(H^1,H^1,{{-1/2}})
PushFWD(TtoR,phi,qBasis,qBasis)













