

load "roots.m";


discriminants:=function(N);
	n0:=Valuation(N,2);
	assert n0 ge 2;
	P:=PrimeDivisors(N div 2^n0);
	disc:=[2^(n0-2),2^(2*n0)] cat [2^j : j in [n0..(2*n0-2)]];
	k:=#P;
	for i in [1..k] do
		p:=P[i];
		n:=Valuation(N,p);
		disc:=&cat[ [ p^j*d : d in disc  ] : j in [n..(2*n) ]];
	end for;
	if IsSquare(N) then
		disc:=[ d : d in disc | Valuation(d,2) in [n0..(2*n0-2)] or &or[ IsOdd(Valuation(d,p)) : p in P ] ];
	end if;
	return Sort(disc);
end function;


discriminant:=function(form);
	a,b,c,r,s,t:=Explode(form);
	return 4*a*b*c+r*s*t-a*r^2-b*s^2-c*t^2;
end function;


matrix:=function(form);
	a,b,c,r,s,t:=Explode(form);
	return Matrix([[ 2*a, t, s ], [ t, 2*b, r ] , [ s, r, 2*c] ]);
end function;

level:=function(form);
	A:=matrix(form);
	assert discriminant(form) eq Determinant(A)/2;
	Ainv:=ChangeRing(A,Rationals())^(-1);
	D:=Denominator(Ainv);	
	diag:=Diagonal(D*Ainv);
	diag:=[Integers()!r : r in diag];
	if &and[IsEven(r) : r in diag] then
		return D;
	else
		return 2*D;
	end if;
end function;

isPrimitive:=function(form);
	return GCD(form) eq 1;
end function;


reciprocal:=function(form);
          a,b,c,r,s,t:=Explode(form);
d:=discriminant(form);
N:=level(form);
m:= Integers()!(4*d/N);
A11:=4*b*c -r^2;
A22:=4*a*c -s^2;
A33:=4*a*b -t^2;
A23:=s*t -2*a*r;
A32:=A23;
A13:=r*t -2*b*s;
A31:=A13;
A12:=r*s -2*c*t;
A21:=A12;
alpha:=Integers()!(A11/m);
beta:=Integers()!(A22/m);
gamma:=Integers()!(A33/m);
ro:=Integers()!(2*A23/m);
sig:=Integers()!(2*A13/m);
tau:=Integers()!(2*A12/m);
phi:=[alpha,beta,gamma,ro,sig,tau];
return phi;
end function;


isReduced:=function(form,d);
	a,b,c,r,s,t:=Explode(form);
	if a gt b or b gt c then
		return false;
	end if;
	if (&and[m gt 0 : m in [r,s,t]] or &and[m le 0 : m in [r,s,t]]) eq false then
		return false;
	end if;
	if (AbsoluteValue(t) gt a) or (AbsoluteValue(s) gt a) or (AbsoluteValue(r) gt b) then
		return false;
	end if;
	if (a+b+r+s+t) lt 0 then
		return false;
	end if;
	if a eq t and s gt 2*r then
		return false;
	end if;
	if a eq s and t gt 2*r then
		return false;
	end if;
	if b eq r and t gt 2*s then
		return false;
	end if;
	if a eq -t and s ne 0 then
		return false;
	end if;
	if a eq -s and t ne 0 then
		return false;
	end if;
	if b eq -r and t ne 0 then
		return false;
	end if;
	if (a+b+r+s+t eq 0) and (2*a+2*s+t gt 0) then
		return false;
	end if;
	if a eq b and AbsoluteValue(r) gt AbsoluteValue(s) then
		return false;
	end if;
	if b eq c and AbsoluteValue(s) gt AbsoluteValue(t) then
		return false;
	end if;
	abc:=a*b*c;
	assert (d/4 le abc) and (abc le d/2);
	return true;
end function;

reducedFormsNd:=function(N,d);
	forms:=[];
        M:=Integers()!(N/2);
        mu:=Integers()!((N^2)/d);
        min1:=Min(M,Floor((d/2)^(1/3)));
if IsOdd(mu) then
        //print "mu is odd", mu;
	for a in [1..min1] do
               if (a mod 4 eq 0) or (a mod 4 eq (-mu mod 4)) then
                   min2:=Min(M,Floor((d/(2*a))^0.5));
//P:=Integers()!Ceiling((d/(N*a)));
	       for b in [a..min2] do
                      if (b mod 4 eq 0) or (b mod 4 eq (-mu mod 4)) then
				for s in [-a..0] do
					for t in [-a..0] do
						alp:=4*a*b-t^2;
						rts:=RootsMod(a,-s*t,d+b*s^2,alp);
						rset:=[];
						for R in rts do
							if R eq 0 then
								R0:=0;
							else
								R0:=R-alp;
							end if;
							while R0 ge -b do
								Append(~rset,R0);
								R0:=R0-alp;
							end while;
						end for;	
						for r in rset do
							D:=d+a*r^2-r*s*t+b*s^2;
							assert IsDivisibleBy(D,alp);
							c:=D div alp;
							if c ge Max(b,d/(4*a*b)) and c le Min(M,Floor(d/(2*a*b))) then
                                                             if (c mod 4 eq 0) or (c mod 4 eq (-mu mod 4)) then
                                                                form:=[a,b,c,r,s,t];
								assert discriminant(form) eq d;
								if isReduced(form,d) and isPrimitive(form) then
									if level(form) eq N then
										Append(~forms,form);
									end if;
								end if;
                                                             end if;
							end if;
						end for;
					end for;
				end for;
				for s in [1..a] do
					for t in [1..a] do 
						alp:=4*a*b-t^2;
						rts:=RootsMod(a,-s*t,d+b*s^2,alp);
						rset:=[];
						for R in rts do
							if R eq 0 then
								R0:=alp;
							else
								R0:=R;
							end if;
							while R0 le b do
								Append(~rset,R0);
								R0:=R0+alp;
							end while;
						end for;	
						for r in rset do
							D:=d+a*r^2-r*s*t+b*s^2;
							assert IsDivisibleBy(D,alp);
							c:=D div alp;
							if c ge Max(b,d/(4*a*b)) and c le Min(M,Floor(d/(2*a*b))) then
                                                             if (c mod 4 eq 0) or (c mod 4 eq (-mu mod 4)) then
								form:=[a,b,c,r,s,t];
								assert discriminant(form) eq d;
								if isReduced(form,d) and isPrimitive(form) then
									if level(form) eq N then
										Append(~forms,form);
									end if;
								end if;
                                                             end if;
							end if;
						end for;
					end for;
		             end for;
                      end if;
		end for;
                end if;
	end for;
else
        //print "mu is even", mu;
	for a in [1..min1] do
               
                   min2:=Min(M,Floor((d/(2*a))^0.5));
// P:=Integers()!Ceiling((d/(N*a)));
	       for b in [a..min2] do
                     
				for s in [-a..0] do
					for t in [-a..0] do
						alp:=4*a*b-t^2;

						rts:=RootsMod(a,-s*t,d+b*s^2,alp);
						rset:=[];
						for R in rts do
							if R eq 0 then
								R0:=0;
							else
								R0:=R-alp;
							end if;
							while R0 ge -b do
								Append(~rset,R0);
								R0:=R0-alp;
							end while;
						end for;	
						for r in rset do
							D:=d+a*r^2-r*s*t+b*s^2;

							assert IsDivisibleBy(D,alp);
							c:=D div alp;
							if c ge Max(b,d/(4*a*b)) and c le Min(M,Floor(d/(2*a*b))) then
                        
								form:=[a,b,c,r,s,t];
								assert discriminant(form) eq d;
								if isReduced(form,d) and isPrimitive(form) then
									if level(form) eq N then
										Append(~forms,form);
									end if;
								end if;
							end if;
						end for;
					end for;
				end for;
				for s in [1..a] do
					for t in [1..a] do 
						alp:=4*a*b-t^2;
						rts:=RootsMod(a,-s*t,d+b*s^2,alp);
						rset:=[];
						for R in rts do
							if R eq 0 then
								R0:=alp;
							else
								R0:=R;
							end if;
							while R0 le b do
								Append(~rset,R0);
								R0:=R0+alp;
							end while;
						end for;	
						for r in rset do
							D:=d+a*r^2-r*s*t+b*s^2;
							assert IsDivisibleBy(D,alp);
							c:=D div alp;
							if c ge Max(b,d/(4*a*b)) and c le Min(M,Floor(d/(2*a*b))) then
								form:=[a,b,c,r,s,t];
								assert discriminant(form) eq d;
								if isReduced(form,d) and isPrimitive(form) then
									if level(form) eq N then
										Append(~forms,form);
									end if;
								end if;
							end if;
						end for;
					end for;
		             end for;
                      
		end for;
                
	end for;
end if;        
       
        return forms;

end function;


genus:=function(form);
	M:=matrix(form);
	L:=LatticeWithBasis(Matrix([[1,0,0],[0,1,0],[0,0,1]]),M);
	return Genus(L);
end function;


// forms is a set of ternary quadratic forms having same level and discriminant
// this partitions the set according to genus

genusParts:=function(forms);
	parts:=[ ];
	for f in forms do
		flag:=false;
		for i in [1..#parts] do
			g:=parts[i][1];
			if genus(f) eq genus(g) then
					parts[i] := parts[i] cat [f];
					flag:=true;
			end if;	
		end for;
		if flag eq false then
			parts:=parts cat [[f]];
		end if;
	end for;
	return parts;
end function;


// form is a ternary quadratic form
// gives the theta series expansion for form upto q^m

theta:=function(form,m);
	M:=matrix(form);
	L:=LatticeWithBasis(Matrix([[1,0,0],[0,1,0],[0,0,1]]),M);
	th:=ThetaSeries(L,2*m);
	P<q>:=Parent(th);
	return &+[Coefficient(th,2*i)*q^i : i in [0..m]];
end function;


// part is a genus for ternary quadratic forms
// returns Theta(f)-Theta(g) for f,g in the genus
// to precision q^m
//but it is of the form theta(f)-theta(g) for fixed g where g is the first element of the genus "part"
//This is enough when we are trying to compute the subspace of half integral weight forms coming from difference of theta series 
// as the vector space generated by Theta(f)-Theta(g) as f, g varies in "part" is same as the vector space generated by Theta(f)-Theta(part[1]) as f varies in "part"


partGen:=function(part,m);
	f:=part[1];
	th:=theta(f,m);
	P<q>:=Parent(th);
	return [ P | P!(theta(part[i],m)) - th : i in [2..#part] ];
end function;

// part is a genus for ternary quadratic forms
// returns Theta(f)-Theta(g) for f,g in the genus
// to precision q^m where both f and g are varying in the genus "part"


partGennew:=function(part,m);
	f:=part[1];
	th:=theta(f,m);
	P<q>:=Parent(th);
        //Res:=P!(theta(part[i],m) - theta(part[j],m)) : i in [1..#part] , j in [1..#part] | i lt j]
	return [ P | P!(theta(part[i],m) - theta(part[j],m)) : i in [1..#part] , j in [1..#part] | i lt j];
end function;


// N level
// d squarefree (corresponding to character \chi_d=(d/.)
// this gives generators for the subspace of S_{3/2}(N,\chi_d)
// that comes from differences of theta series of ternary quadratic forms

subspace:=function(N,d,m);
	assert d ge 1;
	assert N ge 4;
	assert IsSquarefree(d);
	assert IsDivisibleBy(N,d);
	assert IsDivisibleBy(N,4);
	discs:=discriminants(N);
	discs:=[ D : D in discs | IsDivisibleBy(D,d) and IsSquare(D div d) ];
	P<q>:=PowerSeriesRing(Integers(),m+1);
	gens:=[P | ];
	frms:=[];
	AA:=[];
	for D in discs do
	       del:= Integers()!((N^3)/(4*D));
                min:=Minimum(D,del);
                //D, min;
                if min eq D then
                     	forms:=reducedFormsNd(N,D);
		     	parts:=genusParts(forms);
        	     	for part in parts do
				if #part gt 1 then
				nn:=#part;
				mm:=#AA;
				if mm eq 0 then
					rr:=0;
				else
					rr:=#AA[1];
				end if;
				AA:=[ a cat [0 : i in [1..nn]] : a in AA];
				BB:=[ [0 : j in [1..(rr+nn)] ]  : i in [1..(nn-1)]];
				for i in [1..(nn-1)] do
					BB[i][rr+1]:=-1;
					BB[i][rr+i+1]:=1;
				end for;
				AA:=AA cat BB;
				frms:=frms cat part;
                         	gens := gens cat [P!s : s in partGen(part,m)]; //enough to use partGen instead of bigger set partGennew
				end if;
		     	end for;
                else
		  	//min; 
                    	forms:=[reciprocal(phi) : phi in reducedFormsNd(N,del)];
                     	parts:=genusParts(forms);
    	for part in parts do
				if #part gt 1 then
				nn:=#part;
				mm:=#AA;
				if mm eq 0 then
					rr:=0;
				else
					rr:=#AA[1];
				end if;
				AA:=[ a cat [0 : i in [1..nn]] : a in AA];
				BB:=[ [0 : j in [1..(rr+nn)] ]  : i in [1..(nn-1)]];
				for i in [1..(nn-1)] do
					BB[i][rr+1]:=-1;
					BB[i][rr+i+1]:=1;
				end for;
				AA:=AA cat BB;
				frms:=frms cat part;
                           	gens := gens cat [P!s : s in partGen(part,m)]; //enough to use partGen instead of bigger set partGennew
				end if;
                     	end for;
                end if;
	end for;	
	return gens,frms,AA;
end function;

//returns the lower bound for dimension and basis of cusp forms coming from theta series from ternary quadratic forms.

// make m Sturm's bound to be rigorous.
dimensionLB:=function(N,d,m);
        gens,frms,AA:=subspace(N,d,m);
        CC:=Matrix(RationalField(),AA);
        V:=VectorSpace(Rationals(),m);
	B:=[];	
	for Q in gens do
		Append(~B,V![Coefficient(Q,i) : i in [1..m]]);		
	end for;
        Mat:=Matrix(B);
	U:=sub<V | B>;
        bas:=Basis(U);
        E,Trans:=EchelonForm(Mat);
        //E;
        //Trans;
        //CC;
        DD:=Trans*CC;
        P<q>:=PowerSeriesRing(RationalField(),m+1);
        frmsbas:=[P|];
        for b in bas do
	      b1:=Eltseq(b);
              Append(~frmsbas, &+[b1[i]*q^i:i in [1..m]]);
        end for;

return DD,frms,frmsbas,Dimension(U);	
end function;

//Given suitable symmetric matrix returns a ternary quadratic form
formmat:=function(mat);
      
      assert IsSymmetric(mat);
      assert (mat[1,1] mod 2) eq 0;
      assert (mat[2,2] mod 2) eq 0;
      assert (mat[3,3] mod 2) eq 0;

      a:=IntegerRing()!(mat[1,1] div 2);
      b:=IntegerRing()!(mat[2,2] div 2);
      c:=IntegerRing()!(mat[3,3] div 2);
      t:=mat[1,2];
      s:=mat[1,3];
      r:=mat[2,3];
f:=[a,b,c,r,s,t];

return f;

end function;

//equivalence check
equiv:=function(frm1,frm2);
M1:=matrix(frm1);
M2:=matrix(frm2);
B := RMatrixSpace(IntegerRing(), 3, 3) ! [1,0,0, 0,1,0, 0,0,1];
L1:=LatticeWithBasis(B,M1);
L2:=LatticeWithBasis(B,M2);

return IsIsometric(L1,L2);

end function;

//groups the frms set as above according to disciminants                        
grpRR:=function(frms);
       discs:=discriminants(level(frms[1]));
       D:=[d : d in discs | IsSquare(d)];
       R:=[];
       for i in [1..#D] do
	     RRi:=[];
           for f in frms do
		 df:=discriminant(f);
                   if df eq D[i] then
		       Append(~RRi,f);
                   end if;
           end for;
           Append(~R,RRi);
       end for;
       return  R;
end function;


// This follows Bungert's paper and computes the representatives of M/Gl_3(Z)which is required in computing the action of Hecke operators for theta forms coming from ternary quadratic forms.
//RR is the collection of reduced forms of level and discriminant same as given form.
hecketheta:=function(form,p,frms);
     RR:=grpRR(frms);
     for i in [1..#RR] do
	     if form in Set(RR[i]) then
	         l:=i;
             end if;
     end for;
     N:=level(form);
     assert N mod p ne 0;
     Af:=matrix(form);
     A:=[];
     B:=[];
     C:=[];
     D:=[];
     
     p2:=p^2;
    for a in [1..p2] do
        for b in [1..p2] do
            for c in [1..p2] do
                if (a*b*c eq p^3) then
                   for d in [0..(a-1)] do
                       for e in [0..(a-1)] do
                           for f in [0..(b-1)] do
                               M:=Matrix(3,3,[a,d,e,0,b,f,0,0,c]);
                                   if ElementaryDivisors(M) eq [1,p,p2] then
                                       S:=Transpose(M)*Af*M;
                                         if &and[(S[i,j] mod p2) eq 0 : i,j in [1..3]] then
                                             Append(~A,M);

                                             Append(~B,S);
                                             
                                         end if;
                                   end if;
                           end for;
                       end for;
                   end for;
                end if;
            end for;
        end for;
    end for; 
//B;

   T:=0;
    
    for M in B do
	  
          a11:=IntegerRing()!(M[1,1] div p2);
          a12:=IntegerRing()!(M[1,2] div p2);
          a13:=IntegerRing()!(M[1,3] div p2);
          a21:=IntegerRing()!(M[2,1] div p2);
          a22:=IntegerRing()!(M[2,2] div p2);
          a23:=IntegerRing()!(M[2,3] div p2);
          a31:=IntegerRing()!(M[3,1] div p2);
          a32:=IntegerRing()!(M[3,2] div p2);
          a33:=IntegerRing()!(M[3,3] div p2);
          Mnew:=Matrix(3,3,[a11,a12,a13,a21,a22,a23,a31,a32,a33]);
          f:=formmat(Mnew);
          Append(~C,f );         
          thetaf:=theta(f,50);
          T:=T+thetaf;
     end for;

          for c in C do
             for r in RR[l] do
		     if equiv(c,r) then
			     // print c , r;
                        Append(~D,r);
                     end if;
             end for;
          end for;
     

return D;  //C,  T;
 
end function;


heckeSimplified:=function(qf,p,frms);
A:=hecketheta(qf,p,frms);
return [ #[g : g in A | equiv(g,f)]  : f in frms  ];
end function;

// input: one of the row of DD
// frms
// prime p
//computes Hecke action on space of cusp forms
heckeactioncusp:=function(frms,p);
             M:=[];
             n:=#frms;
             for i in [1..n] do
	           Append(~M,heckeSimplified(frms[i],p,frms));
             end for;
             Mat:=Matrix(RationalField(),n,n,M);
             return Mat;
             //Dnew:=dd*Mat;
             //return Dnew;
end function;


heckeSimplifiedLinComb:=function(li,frms,p,hecactcusp);
        
        //assert #li eq #frms;
        //M:=heckeactioncusp(frms,p);
        L:=Matrix([li]);
        a:=Eltseq(L*hecactcusp);
        return a;


        /*n:=#frms;
	a:=[0 : i in [1..n]];
	
	for j in [1..n] do
		alpha:=li[j];
		if alpha  ne 0 then
			v:=heckeSimplified(frms[j],p,frms);
			a:=[a[i]+alpha*v[i] : i in [1..n]];
		end if;
	end for;		
	return a;*/
end function;


heckeOnBasis:=function(li,frms,dim,DD,p,hecactcusp);
	W:=VectorSpaceWithBasis(Rows(DD));
	a:=heckeSimplifiedLinComb(li,frms,p,hecactcusp);
	a:=W!a;
	C:=Coordinates(W,a);
	C:=[C[i] : i in [1..dim]];
	return C;
end function;

heckeMatrix:=function(frms,dim,DD,p,hecactcusp);
	mat:=[ heckeOnBasis(Eltseq(Rows(DD)[j]) , frms, dim, DD,p,hecactcusp) : j in [1..dim]];
	return Matrix(mat);
end function;



//----------------------------------------------------------------
//three of the following functions are from eigen.m

//This function gives first prime which is coprime to a given N                
coprime := function(N);
p:=1;
while true do
	   p:=NextPrime(p);
if GCD(p,N) eq 1 then
return p;
end if;
end while;
end function;

//This function is used in the below one
eigenEmbedding:=function(lambdap,j);
K:=Parent(lambdap);
if K eq Rationals() then
return lambdap;
 else
   return RealEmbeddings(lambdap)[j];
end if;
end function;

//Returns primes for which vectors of eigenvalues of newforms of weight 2 and level dividing N/2 are pairwise distinct
//The primes remain the same in case we take newforms of weight 2,level dividing N/2 and character chi^2 where chi is quadratic character and conductor chi^2 divides the level of newforms


primeschk:=function(N);
           M:=N div 2;
           forms:=[* *];
           for d in Divisors(M) do
                NFs:=Newforms(CuspForms(d));
                for class in NFs do
			  forms:=forms cat [* class[1] *];
                end for;
           end for;
           //print forms;                                                          
           pairs:=[];
           k:=#forms;
           for i in [1..k] do
	         Ki:=Parent(Coefficient(forms[i],0));
                 di:=Degree(Ki);
                 for j in [1..di] do
                        Append(~pairs,<i,j>);
                 end for;
           end for;
           //print pairs; 
           quads:=[];
           for pair1, pair2 in pairs do
	       if (pair1[1] lt pair2[1]) or (pair1[1] eq pair2[1] and pair1[2]\
					   lt pair2[2]) then
					 Append(~quads,<pair1[1],pair1[2],pair2[1],pair2[2]>);
              end if;
           end for;
           //print(quads);                                   
           p:=2;
           prs:=[];
           while #quads ne 0 do
	        p:=NextPrime(p);
               //print p;                                                      
               if GCD(p,N) eq 1 then
                        for quad in quads do
				   i1,j1,i2,j2:=Explode(quad);
                                   lambda1:=eigenEmbedding(Coefficient(forms[i1],p),j1);
                                   lambda2:=eigenEmbedding(Coefficient(forms[i2],p),j2);

                                   if AbsoluteValue(lambda1-lambda2) gt 10^(-5) then
                                             Include(~prs,p);
                                             Exclude(~quads,quad);
                                             //print quads;
                                   end if;
                        end for;
               end if;
           end while;
           return prs;
end function;
//---------------------------------------------------------------------------




//h is the newform given of level dividing N/2
//This functions gives the half inetgral weight forms of level N weight 3/2 coming from the ternary quadratic form which are equivalent to a given new form h

eigenforms:=function(h,N,d,m)
            DD,frms,frmsbas,dim:=dimensionLB(N,d,m);
//DD;
//frms;
//frmsbas;
//dim;

            r:=#frms;
            P:= primeschk(N);
P;
            S:=[* *];
            if #P gt 0 then
                for p in P do
                    lambdap := Coefficient(h,p) ;
                    Dp:=heckeactioncusp(frms,p);
                    Mp:=heckeMatrix(frms,dim,DD,p,Dp);
                    //assert lambda in the list of eigenvalues of Mp
                    p;
                    Sp:=Eigenspace(Mp,lambdap);
                    Append(~S,Sp);
                end for;
            else
                    q:=coprime(N);
                    lambdaq := Coefficient(h,q) ;
                    Dq:=heckeactioncusp(frms,q);
                    Mq:=heckeMatrix(frms,dim,DD,q,Dq);
                    //assert lambda in the list of eigenvalues of Mq
                    q;
                    Sq:=Eigenspace(Mq,lambdaq);
                    Append(~S,Sq);
            end if;
            if #S eq 0 then
	      V:=0;
            else   
              V:= &meet [U:U in S];
            end if;
            //V;
            B:=Basis(V);
            return V, B, frms, [ &+[Eltseq(B[j])[i]*frmsbas[i] : i in [1..dim]] : j in [1..Dimension(V)]]; //frmsbas, 
end function;


//New functions
//the following function compares two modular forms for equality given their power series expansion upto q^m
compare:=function(f, g, m)
         listf:=[Coefficient(f,i): i in [0..(m-1)]];
         listg:=[Coefficient(g,i): i in [0..(m-1)]];
         if listf eq listg then 
            return true;
         else 
            return false;
         end if;
end function;


//checks if the shimura lifts are of the form theta_f-theta_g and return theta_f, theta_g
//h is the newform of integral weight, N is the level we are loking for Shimura lift, d corresponds to quadratic char, d=1, trivial char, prec1 precision for computing Shimuralift, prec2 precision for checking of lift comes from difference of theta series. 

shimtheta:=function(h,N,d,prec1,prec2)
          V,B,frms,lifts:=eigenforms(h,N,d,prec1);
          genera:=genusParts(frms);
          n:=#genera;
          m:=#lifts;
          part:=[partGennew(genera[i],prec2): i in [1..n]];
          list:=[* *];
          for i in [1..m] do //lifts
              for j in [1..n] do
                   k_j:= #genera[j];
                   for a, b in [1..k_j] do 
                       if a lt b then 
			  if (compare(lifts[i], (1/2)*(theta(genera[j][a], prec2)-theta(genera[j][b],prec2)),prec2) eq true) or (compare(lifts[i], (1/2)*(theta(genera[j][a], prec2)-theta(genera[j][b],prec2)),prec2) eq true) then 
                           Append(~list, [* i, genera[j][a], genera[j][b] *] );
			  end if;
                       end if;
		   end for;
	      end for;
           end for;
         return m, lifts, list;
end function;



//------------------------------------------------------------------------


//------------------------OLD FUNCTIONS-------------------------------------



/*
// input: one of the row of DD
// frms
// prime p
//computes Hecke action on space of cusp forms
heckeactioncusp:=function(dd,frms,p);
             M:=[];
             n:=#frms;
             for i in [1..n] do
	           Append(~M,heckeSimplified(frms[i],p,frms));
             end for;
             Mat:=Matrix(RationalField(),n,n,M);
             return Mat;
             //Dnew:=dd*Mat;
             //return Dnew;
end function;
*/

//h is the newform given of level dividing N/2
//This functions gives the half inetgral weight forms of level N weight 3/2 coming from the ternary quadratic form which are equivalent to a given new form h

eigenformsold:=function(h,N,d,m);
            DD,frms,frmsbas,dim:=dimensionLB(N,d,m);
            r:=#frms;
            P:= primeschk(N);
            S:=[* *];
            DD1:=Matrix(RationalField(),dim,r,[DD[i]:i in [1..dim]]);
            if #P gt 0 then
                for p in P do
                    lambdap := Coefficient(h,p) ;
                    Dp:=heckeactioncusp(DD,frms,p);
                    Dp1:=Matrix(RationalField(),dim,r,[Dp[i]:i in [1..dim]]);
                    Mp1:=Dp1-(lambdap)*DD1;
                    Kp1:=Kernel(Mp1);
//print p; print Kp1;
                    Append(~S,Kp1);
                end for;
	    else
	        q:=coprime(N);
                lambdaq := Coefficient(h,q) ;
                Dq:=heckeactioncusp(DD,frms,q);
                Dq1:=Matrix(RationalField(),dim,r,[Dq[i]:i in [1..dim]]);
                Mq1:=Dq1-(lambdaq)*DD1;
                Kq1:=Kernel(Mq1);
                Append(~S,Kq1);
            end if;
            if #S eq 0 then
	      K:=0;
            else   
              K:= &meet [U:U in S];
            end if;
            return K;

end function;
//-----------------------------------------------------------------------------





/* A:=[0 : i in [1..#frms]];
   for i in [1..#frms] do
	 hS:=heckeSimplified(frms[i],p,frms);
hS;
hS:=[h*dd[i] : h in hS];
hS;
A:=[A+hS[j] : j in [1..#frms]];
end for;
return A; */

/*E:=EllipticCurve([1,1]);
E;
h:=Newform(E);
Level(h);
Eg:=eigenforms(h,1984,1,1000);
Eg;*/

/*S:=Newforms(CuspForms(50,2));
S;
h:=S[1][1];
h;
E:=EllipticCurve(h);
E;
E1:=QuadraticTwist(E,-1);
E1;
h1:=Newform(E1);
h1;
Eq8000:=eigenforms(h1,8000,1,1000);
Eq8000;
*/
