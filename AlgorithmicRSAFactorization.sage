from sage.rings.polynomial.multi_polynomial_sequence import PolynomialSequence

N = input("N : ")  # Bit size of each RSA prime p, q in N = p*q
M = 8*N*N - 12*N + 4  # number of variables in the solution space
P = 0
Q = 0
while ((P<2**(N-1)) or (P>2**N)) or ((Q<2**(N-1)) or (Q>2**N)) or (P==Q):
    P = next_prime((2**(N-1))+floor((2**(N-1))*random()))
    Q = next_prime((2**(N-1))+floor((2**(N-1))*random()))

print("P      : ",P.bits())
print("Q      : ",Q.bits())

F = BooleanPolynomialRing(M,'x')
names = F.gens()

def bit_adder_carry(c_in,a,b,eqn_arr):
    s = c_in+a+b
    c_out = a*b+c_in*a+c_in*b
    return s,c_out

def mod_add_seq(add1,add2,c_in,st,en,v_ctr,eqn_arr):
    for i in range(st,en):
        s,c_in[0] = bit_adder_carry(c_in[0],add1[i],add2[i],eqn_arr)
        eqn_arr.append(names[v_ctr[0]]+s)
        add1[i] = names[v_ctr[0]]
        eqn_arr.append(names[v_ctr[0]+1]+c_in[0])
        c_in[0] = names[v_ctr[0]+1]
        v_ctr[0] += 2
    return

PQ = (P*Q).digits(base=2,padto=2*N)
print("PQ = ",PQ)
for i in range(2*N):
    if PQ[i]==0: PQ[i] = names[0]+names[0]
    else: PQ[i] = names[0]+names[0]+1
pbase = [1]+list(names[0:N-2])+[1]
qbase = [1]+list(names[N-2:2*N-4])+[1]
eqn_arr = []
v_ctr = [2*N-4]
strt = cputime()

###NOR ADD
sum_arr = pbase+N*[0]
for i in range(1,N-1):
    add_temp = i*[0]
    eqn_arr.append(qbase[i]+PQ[i]+sum_arr[i])
    add_temp.append(qbase[i])
    for j in range(N-2):
        eqn_arr.append(names[v_ctr[0]]+pbase[j+1]*qbase[i])
        add_temp.append(names[v_ctr[0]])
        v_ctr[0] += 1
    add_temp.append(qbase[i])
    add_temp += (N-i)*[0]
    eqn_arr.append(names[v_ctr[0]]+sum_arr[i]*qbase[i])
    c_in = [names[v_ctr[0]]]
    v_ctr[0] += 1
    mod_add_seq(sum_arr,add_temp,c_in,i+1,N+i,v_ctr,eqn_arr)
    sum_arr[N+i] = names[v_ctr[0]-1]#+qtemp[N+i]
qtemp = (N-1)*[0]+pbase+[0]
c_in = [0]
mod_add_seq(sum_arr,qtemp,c_in,N-1,2*N-1,v_ctr,eqn_arr)
sum_arr[2*N-1] = names[v_ctr[0]-1]#+qtemp[2*N-1]
for i in range(N): eqn_arr.append(sum_arr[N-1+i]+PQ[N-1+i])
###NOR ADD

###REV ADD
sum_arr = (N-1)*[0]+pbase+[0]
for i in range(1,N-1):
    add_temp = (N-1-i)*[0]
    add_temp.append(qbase[N-1-i])
    for j in range(N-2):
        eqn_arr.append(names[v_ctr[0]]+pbase[j+1]*qbase[N-1-i])
        add_temp.append(names[v_ctr[0]])
        v_ctr[0] += 1
    add_temp.append(qbase[N-1-i])
    add_temp += (i+1)*[0]
    sum_arr[N-1-i] = qbase[N-1-i]
    c_in = [names[0]+names[0]]
    mod_add_seq(sum_arr,add_temp,c_in,N-i,2*N,v_ctr,eqn_arr)
    eqn_arr.append(names[v_ctr[0]-1])
add_temp = pbase+N*[0]
c_in = [names[0]+names[0]]
mod_add_seq(sum_arr,add_temp,c_in,1,2*N,v_ctr,eqn_arr)
eqn_arr.append(names[v_ctr[0]-1])
for i in range(1,2*N): eqn_arr.append(sum_arr[i]+PQ[i])
###REV ADD

elapsed = cputime(strt)
print("equations generated in ",elapsed,"sec")

###REDUCTION
lin_eqn_remains = 1
EQNN = len(eqn_arr)
solutions = {}
strt = cputime()
while lin_eqn_remains==1:
    for i in range(EQNN):
        p = eqn_arr[i]
        if p.degree()==1:
            mon = p.monomials()
            if len(mon)<3:
                subs_var = mon[0]
                subs_val = p+mon[0]
                solutions[subs_var] = subs_val
                for j in range(EQNN):
                    if eqn_arr[j]!=0 : eqn_arr[j] = eqn_arr[j].subs({subs_var:subs_val})

    eqn_arr = [u+names[0]+names[0] for u in eqn_arr if u!=names[0]+names[0]]
    lin_eqn_remains = 0
    EQNN = len(eqn_arr)
    for i in range(EQNN):
        if eqn_arr[i].degree()==1:
            pt = eqn_arr[i].monomials()
            if len(pt)<3:
                lin_eqn_remains = 1
                i = EQNN

elapsed = cputime(strt)
print("conversion done in ",elapsed,"sec")
###REDUCTION

###COUNT MONOMS
strt = cputime()
monoms = []
for i in range(len(eqn_arr)):
    t = eqn_arr[i].monomials()
    for j in range(len(t)):
        if t[j] not in monoms: monoms.append(t[j])
print("equations : ",len(eqn_arr))
print("monomials : ",len(monoms))
elapsed = cputime(strt)
print("# of monoms calculated in ",elapsed,"sec")
###COUNT MONOMS

###SOLUTION
S = PolynomialSequence(arg1=F,arg2=eqn_arr)
strt = cputime()
A = S.solve(n=Infinity, algorithm='sat', eliminate_linear_variables=false);
elapsed = cputime(strt)
t = get_memory_usage()
for j in range(len(A)):
    prime_str = "P"+str(j)+"     :  [1, "
    for i in range(N-2):
        if names[i] in A[j].keys():
            prime_str += str(A[j][names[i]])+", "
        elif names[i] in solutions.keys():
            prime_str += str(solutions[names[i]])+", "
    prime_str += "1]"
    print(prime_str)
print("system solved in ",elapsed," sec")
print("memory  : ",t)
###SOLUTION

"""
of = open("ofile32.txt","w")
for i in range(len(eqn_arr)):
   of.write(str(eqn_arr[i]))
   of.write("\n")
of.close()
"""